//! **T5: the kernel's replay facts against the in-tree Rust reader** (stage 5
//! D9 phase C; design `kernel/design/stage5/stage5-D9-D10-design.md` §14.4, §6.4,
//! §7.1, §17).
//!
//! The kernel is reached through `tm_kernel_ffi::call`: a genesis request (`ckpt:
//! null`, no `reseal`) carrying the whole log from line 1, a zone table from
//! `tm/src/cli/tz_table.rs` and `want.facts`. Its `facts` are decoded into
//! [`Facts`] and compared **field by field** with the facts the Rust derives
//! through the test chokepoint `support/replay.rs` (`replay_of_text`, whose body
//! is `Ctx::replay_of`'s: the in-tree parse, then `replay(None, tz)`).
//!
//! Each phase-C step extends [`Facts`] with the fields it adds (the §14.4 table's
//! "T5 compares" column); a step is not done until this file passes for them.
//!
//! | step | fields |
//! |---|---|
//! | C1 | `cancelled`: the lines of the entries the undo mask cancels (`ViewRow::cancelled`) |
//! | C2 | `days`: every entry's wake-attributed day (`ViewRow::day`), survivors, cancelled entries and undos alike, as `(line, days since 0001-01-01)` |
//! | C3 | `block`: the block family of the machine (`start`, `pause`, `unpause`, `interrupt`, `resume`, `stop`, `done`, `extend`). Per day, `DayReplay`'s `first_start`, `starts`, `block_min`, `blocks_done`, `load_fifths`, `minutes_by_ci`, `ci_unknown`, `done`, `lost_min`, `dropped` and its `Block`/`Pause`/`Interrupt` segments; every `ItemReplay` field; the start observations of `energy`; `durations`; `interrupts`; `open_block`; `open_interrupt`; `last_effective_t` ([`Block`]) |
//! | C5 | `day`: the day header and records family (`wake`, `arrive`, `loc`, `break`, `energy`, `idle`, `routine`'s day half, `plan`, `demote`, `drop`, `close`, unknown events). Per day every remaining `DayReplay` field (`wake`, `slept_min`, `onset_min`, `arrival`, `loc`, `window`, `budget`, `loc_changes`, `leak_min`, `longest_leak`, `idle`, `breaks`, `routine_min`, `plans`, `replans_today`, `drift_min`, `last_plan_hash`); `demotions` (each with its day), `closes` (each with its day), `dropped_items`, the global `longest_leak`, `unknown`. The block family's comparison widens to every segment kind, every energy observation, and exactly the Rust's set of days ([`DayFam`]) |
//! | C6 | **the entire `Replay`**. The kernel's facts are design §8.4's view (every day's record, seam, observations, interruptions, demotions, closes and headers; every date's window; every item; the all-time counts), decoded into the families above plus `seams` (fork `DaySeam`: since-break anchor, idle marks, `last_t`), `rows` (`tm log`'s `ViewRow`s: line, tag, id, day, cancelled, display), the counts (`entry_count`, `line_count`, `days.keys().last()`) and each id's first done date and count; and then rebuilt as a `tm_core::log::Replay` ([`kernel_replay`]) compared with the fork's by its own `PartialEq` and `ported_facts()` (D14) |
//! | C7 | no new field: [`TRIPLES`] generated `(L, E, M)` triples ([`triple`]). The undone log `L ++ E ++ M ++ undosFor E` is compared in full with the fork, and so is the log without the command, `L ++ M`, with `E`'s lines left blank so every entry keeps its line. When `untouchedBy E M` holds, the two agree on every fact but the line bookkeeping (Replay.lean's `undoing_a_command_replays_the_log_without_it`); when it does not, the fork's cancellation is reproduced line by line and the two disagree |
//! | C4 | `completion`: the completion family (`done`'s `mark_done`, `routine`, `skip`, `event`): `done_items` and `last_done` (the latest by instant, the first of equal instants), `done_dates`, `instances` (the last record in file order), `LatestNamed` per `(name, id?)` from `events` (with each occurrence's line) and every `latest_named` query, `event_names`; and the replay warnings as `(line, status)`, each checked against `Replay.warnings`' text ([`Completion`]) |
//!
//! **The inputs**, every one compared in full:
//! * the seven corpus logs (`kernel/corpus/logs/*.jsonl`, the design's four, and
//!   the three plans' `.tm/log.jsonl`);
//! * the generated 1-month and 6-month logs (`support/loggen.rs`, 40 a day);
//! * [`SEQUENCES`] generated sequences mixing every arm of [`Arm`]: undos (the
//!   silent-verb undo of quirk Q6(d) among them), out-of-order wakes, retro
//!   `break`/`idle`, housekeeping closes between a command and its undo (Q6(f)),
//!   a partial `done` after `stop`, `extend`, and a `:60` stamp inside a block;
//! * §6.4's zone cases, each its own arm ([`zone_cases`]).
//!
//! **Exceptions** come only from design §17's parity list, each named where it
//! is used. At C1 and C2 there are none: §17 lists the undo mask, dangling undos,
//! the housekeeping cancellation, both first-wake rules and day attribution in
//! `cfg.tz` inside the table's span, leap seconds included, as exact by design.
//! C4 adds none to the compared inputs (§17: `last_done` by instant and instances
//! by file order are exact by design). Parity P33, a routine `done` whose `inst`
//! names a date before 0001-01-01, is not generated; it has its own named test
//! ([`t5_p33_a_done_date_before_the_origin_is_the_named_exception`]). C5 adds none
//! (§17: late-bound `slept` is exact by design). Parity P34, an `idle` gap or a
//! routine's minutes reaching before 0001-01-01, is not generated; it has its own
//! named test ([`t5_p34_a_gap_before_the_origin_is_the_named_exception`]). C6 adds none: the
//! seams, the view rows and the counts are exact (§17: observation order by source
//! line is exact by design); P33's and P34's tests carry the one date into the first
//! done date and the last day. C7 adds none: §17 lists the undo mask and the housekeeping
//! cancellation as exact by design, and the triples are generated inside the table's span.

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

#[allow(dead_code)]
#[path = "support/loggen.rs"]
mod loggen;

#[allow(dead_code)]
#[path = "support/replay.rs"]
mod replay;

#[allow(dead_code)]
#[path = "../src/cli/kernel_log.rs"]
mod kernel_log;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::{Mutex, OnceLock};

use chrono::{DateTime, Datelike, Duration, FixedOffset, NaiveDate, TimeZone, Timelike, Utc};
use chrono_tz::Tz;
use serde_json::{json, Value};
use tm_core::log::{
    fmt_timestamp, parse_instance_status, BreakRecord, CloseRecord, DayReplay, DaySeam, Demotion, DurationObs, EnergyObs, Event, IdleMark, IdleRecord,
    InstanceRecord, Interruption, ItemReplay, LeakRecord, LogEntry, LogSegment, OpenBlock, Replay, SegmentKind, StartRecord,
};
use tm_core::model::InstanceStatus;

/// How many generated sequences T5 runs (design §14.4).
const SEQUENCES: u64 = 256;

thread_local! {
    /// C4: how many `latest_named` queries [`assert_parity`] has compared on this test's thread.
    static LATEST_NAMED_QUERIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn latest_named_queries() -> usize {
    LATEST_NAMED_QUERIES.with(std::cell::Cell::get)
}

// ---------------------------------------------------------------------------
// The two readers.

/// **The facts T5 compares.** Each phase-C step adds its fields here, in the
/// kernel's decoder and in the Rust's, and nowhere else.
#[derive(Clone, Debug, PartialEq)]
struct Facts {
    /// C1: the physical lines of the cancelled entries (undone, or undos), in
    /// file order.
    cancelled: Vec<u64>,
    /// C2: every entry's day in file order, `(line, day)`, the day counted from
    /// 0001-01-01 as the kernel's `Cal.Day` is ([`day_number`]).
    days: Vec<(u64, i64)>,
    /// C3: the block family.
    block: Block,
    /// C4: the completion family and the replay warnings.
    completion: Completion,
    /// C5: the day header and records family.
    day: DayFam,
    /// C6: every day's seam (fork `DaySeam`: R1's since-break anchor, R2's idle marks, R4's `last_t`).
    seams: BTreeMap<i64, SeamRow>,
    /// C6: `tm log`'s view rows, every entry in file order (`ViewRow` and its display).
    rows: Vec<RowView>,
    /// C6: `entry_count()`, `line_count()`, and `days.keys().last()` (`status_line`'s fallback, §8.4's `lastDay`).
    counts: (u64, u64, Option<i64>),
    /// Not a replay fact: the lines each reader refused (T1's field, carried so a
    /// line one reader dropped cannot hide from the facts above).
    warnings: Vec<u64>,
}

/// A `DateTime<FixedOffset>` as the kernel writes one: seconds since
/// 0001-01-01T00:00:00Z, nanoseconds (a leap second's included), whether the
/// written offset is west of UTC, and its seconds. The offset is compared too,
/// though chrono's `PartialEq` ignores it: the kernel keeps what was written.
type Stamp = (i64, u32, bool, u32);

/// Seconds from 0001-01-01T00:00:00Z to the Unix epoch.
const EPOCH_FROM_CE: i64 = 62_135_596_800;

fn stamp_of(t: &DateTime<FixedOffset>) -> Stamp {
    let off = t.offset().local_minus_utc();
    (t.timestamp() + EPOCH_FROM_CE, t.timestamp_subsec_nanos(), off < 0, off.unsigned_abs())
}

/// C3: one day's block fields (`DayReplay`). Segments are `(start, end, kind,
/// arguments)` of every kind (C5 widens C3's three), in `DayReplay::segments`' order.
#[derive(Clone, Debug, PartialEq, Default)]
struct DayBlock {
    first_start: Option<Stamp>,
    starts: Vec<(Stamp, String, u64, Option<u64>)>,
    block_min: u64,
    blocks_done: u64,
    load_fifths: u64,
    by_ci: Vec<u64>,
    ci_unknown: BTreeMap<String, u64>,
    done: Vec<String>,
    lost_min: u64,
    dropped: Vec<String>,
    segments: Vec<(Stamp, Stamp, String, Vec<Option<String>>)>,
}

/// C3: one item's `ItemReplay`, `minutes_by_day` included.
#[derive(Clone, Debug, PartialEq, Default)]
struct ItemBlock {
    minutes: u64,
    blocks: u64,
    by_day: BTreeMap<i64, u64>,
    done_at: Vec<Stamp>,
    partial_done_at: Vec<Stamp>,
    stops: u64,
    extended_min: u64,
}

/// `EnergyObs`: `(line, t, day, pred, rep, hsw, loc, slept_min, went, id, from_start)`.
type EnergyRow = (u64, Stamp, i64, u64, u64, f64, String, Option<u64>, Option<u64>, Option<String>, bool);
/// `DurationObs`: `(line, t, day, id, ci, tags, est_min, actual_min, went, partial)`.
type DurationRow = (u64, Stamp, i64, String, u64, Vec<String>, u64, u64, Option<u64>, bool);
/// `Interruption`: `(start, end, day, id, lost_min, dropped)`.
type InterruptRow = (Option<Stamp>, Option<Stamp>, i64, Option<String>, u64, Vec<String>);
/// `OpenBlock`: `(id, started, worked_min, since, paused)`.
type OpenBlockRow = (String, Stamp, u64, Option<Stamp>, bool);

/// **C3: the block family.** `days` holds every day the reader created (C5: the
/// kernel creates every day the fork does, so the two sets are compared exactly).
/// `energy` is every observation, a start's and (C5) an `energy` event's.
#[derive(Clone, Debug, PartialEq, Default)]
struct Block {
    days: BTreeMap<i64, DayBlock>,
    items: BTreeMap<String, ItemBlock>,
    energy: Vec<EnergyRow>,
    durations: Vec<DurationRow>,
    interrupts: Vec<InterruptRow>,
    open_block: Option<OpenBlockRow>,
    open_interrupt: Option<InterruptRow>,
    last_effective: Option<Stamp>,
}

/// C6: a day's seam, `(since_break, idle marks as (kind, stamp, actual_min), last_t)`.
type SeamRow = (Option<Stamp>, Vec<(String, Stamp, Option<u64>)>, Option<Stamp>);
/// C6: a view row, `(line, tag, id, day, cancelled, display)`.
type RowView = (u64, String, Option<String>, i64, bool, String);

/// C4: an instance record, `(stamp, status, status as logged, actual_min)`.
type InstanceRow = (Stamp, String, String, Option<u64>);
/// C4: one `(name, id?)` key's `LatestNamed`, `(latest line, latest stamp, dated
/// line, dated stamp)`.
type NamedRow = (u64, Stamp, u64, Stamp);

/// **C4: the completion family.**
#[derive(Clone, Debug, PartialEq, Default)]
struct Completion {
    /// `last_done`; its keys are `done_items` (checked on the Rust side).
    last_done: BTreeMap<String, Stamp>,
    /// `done_dates`, days counted from 0001-01-01.
    done_dates: BTreeMap<String, BTreeSet<i64>>,
    /// `instances`, keyed `(item, inst)`.
    instances: BTreeMap<(String, String), InstanceRow>,
    /// `LatestNamed` per `(name, id?)`.
    named: BTreeMap<(String, Option<String>), NamedRow>,
    /// The replay warnings, `(line, status as logged)`, in file order.
    warnings: Vec<(u64, String)>,
    /// C6: per id with a done date, `(done_date_first, done_date_count)` (R3's narrowing; §8.4's A).
    done_first: BTreeMap<String, (Option<i64>, u64)>,
}

fn status_name(s: InstanceStatus) -> &'static str {
    match s {
        InstanceStatus::Pending => "pending",
        InstanceStatus::Done => "done",
        InstanceStatus::Missed => "missed",
        InstanceStatus::Expired => "expired",
        InstanceStatus::Skipped => "skipped",
    }
}


/// The instant order of two stamps (chrono's: the offset is not compared).
fn instant_of(s: &Stamp) -> (i64, u32) {
    (s.0, s.1)
}

/// The Rust's completion family, from the in-tree `Replay`. The named records
/// and the warnings need each occurrence's line, which the fork's lists do not
/// carry: they are walked beside the surviving rows of their kind, in file order,
/// and checked against them.
fn rust_completion(r: &Replay, tz: Tz) -> Completion {
    let done_items: BTreeSet<String> = r.last_done.keys().cloned().collect();
    assert_eq!(done_items, r.done_items, "the fork's done_items are its last_done keys");
    let mut out = Completion {
        last_done: r.last_done.iter().map(|(k, t)| (k.clone(), stamp_of(t))).collect(),
        done_dates: r.done_dates.iter().map(|(k, ds)| (k.clone(), ds.iter().map(|d| day_number(*d)).collect())).collect(),
        done_first: r.done_dates.keys().map(|id| (id.clone(), (r.done_date_first(id).map(day_number), r.done_date_count(id) as u64))).collect(),
        instances: r
            .instances
            .iter()
            .flat_map(|(item, m)| {
                m.iter().map(move |(inst, rec)| {
                    (
                        (item.clone(), inst.clone()),
                        (stamp_of(&rec.t), status_name(rec.status).to_string(), rec.raw_status.clone(), rec.actual_min.map(u64::from)),
                    )
                })
            })
            .collect(),
        ..Completion::default()
    };
    let survivors: Vec<_> = r.view().iter().filter(|row| !row.cancelled).collect();
    // The replay warnings: one a surviving routine with a status the fork does not read.
    for row in &survivors {
        if let Event::Routine { status, .. } = &row.entry.ev {
            if parse_instance_status(status).is_none() {
                out.warnings.push((row.line, status.clone()));
            }
        }
    }
    let texts: Vec<String> = out
        .warnings
        .iter()
        .map(|(line, raw)| {
            let row = survivors.iter().find(|row| row.line == *line).expect("the warned row");
            format!("{}: unknown routine status {raw:?}", fmt_timestamp(&row.entry.t))
        })
        .collect();
    assert_eq!(texts, r.warnings, "Replay.warnings is one message a surviving unknown status, in file order");
    // `events[name]` in file order, beside the surviving `event` rows of that name.
    for (name, occ) in &r.events {
        let rows: Vec<_> = survivors.iter().filter(|row| matches!(&row.entry.ev, Event::Named { name: n, .. } if n == name)).collect();
        assert_eq!(rows.len(), occ.len(), "events[{name}] is its surviving rows");
        let mut keys: BTreeMap<Option<String>, NamedRow> = BTreeMap::new();
        for (row, e) in rows.iter().zip(occ) {
            let Event::Named { id: row_id, .. } = &row.entry.ev else { unreachable!("filtered to events") };
            assert_eq!((stamp_of(&row.entry.t), row_id), (stamp_of(&e.t), &e.id), "events[{name}] in file order");
            let (line, t) = (row.line, stamp_of(&e.t));
            let date = |s: &Stamp| day_number(date_in(s, tz));
            keys.entry(e.id.clone())
                .and_modify(|k| {
                    // `t >= latest` and `(date, t) >= (date, latest_dated)`: a later line wins a tie.
                    if instant_of(&t) >= instant_of(&k.1) {
                        k.0 = line;
                        k.1 = t;
                    }
                    if (date(&t), instant_of(&t)) >= (date(&k.3), instant_of(&k.3)) {
                        k.2 = line;
                        k.3 = t;
                    }
                })
                .or_insert((line, t, line, t));
        }
        for (id, k) in keys {
            out.named.insert((name.clone(), id), k);
        }
    }
    out
}

/// The local date of a stamp in `tz`.
fn date_in(s: &Stamp, tz: Tz) -> NaiveDate {
    DateTime::from_timestamp(s.0 - EPOCH_FROM_CE, s.1).expect("a stamp in range").with_timezone(&tz).date_naive()
}

/// **`Replay::latest_named(name, id, tz)` from the kernel's per-key records**: the
/// key addressed to nobody and the key addressed to `id` merged, the later line
/// winning a tie, as the fork's walk over `events[name]` does.
fn kernel_latest_named(c: &Completion, name: &str, id: &str, tz: Tz) -> Option<(Stamp, Stamp)> {
    let keys = [c.named.get(&(name.to_string(), None)), c.named.get(&(name.to_string(), Some(id.to_string())))];
    let mut best: Option<NamedRow> = None;
    for k in keys.into_iter().flatten() {
        best = Some(match best {
            None => *k,
            Some(b) => {
                let date = |s: &Stamp| day_number(date_in(s, tz));
                let latest = if (instant_of(&k.1), k.0) > (instant_of(&b.1), b.0) { (k.0, k.1) } else { (b.0, b.1) };
                let dated = if (date(&k.3), instant_of(&k.3), k.2) > (date(&b.3), instant_of(&b.3), b.2) { (k.2, k.3) } else { (b.2, b.3) };
                (latest.0, latest.1, dated.0, dated.1)
            }
        });
    }
    best.map(|b| (b.1, b.3))
}

/// A date as the kernel counts it: days since 0001-01-01 (chrono counts that
/// date as day 1 from the common era).
fn day_number(d: NaiveDate) -> i64 {
    i64::from(d.num_days_from_ce()) - 1
}

/// The wire table of `tz`, probed once per zone per test binary.
fn table(tz: Tz) -> Value {
    static TABLES: OnceLock<Mutex<HashMap<String, Value>>> = OnceLock::new();
    let tables = TABLES.get_or_init(|| Mutex::new(HashMap::new()));
    let mut guard = tables.lock().expect("the table cache");
    guard.entry(tz.name().to_string()).or_insert_with(|| tz_table::probe(tz).to_wire()).clone()
}

fn j_u64(v: &Value, what: &str) -> u64 {
    v.as_u64().unwrap_or_else(|| panic!("{what}: {v}"))
}
fn j_str(v: &Value, what: &str) -> String {
    v.as_str().unwrap_or_else(|| panic!("{what}: {v}")).to_string()
}
fn j_arr<'a>(v: &'a Value, what: &str) -> &'a Vec<Value> {
    v.as_array().unwrap_or_else(|| panic!("{what}: {v}"))
}
fn j_opt<T>(v: &Value, f: impl Fn(&Value) -> T) -> Option<T> {
    if v.is_null() { None } else { Some(f(v)) }
}
fn j_strs(v: &Value, what: &str) -> Vec<String> {
    j_arr(v, what).iter().map(|s| j_str(s, what)).collect()
}
fn j_stamp(v: &Value) -> Stamp {
    let a = j_arr(v, "a stamp");
    assert_eq!(a.len(), 4, "a stamp is [sec, ns, west, offsetSec]: {v}");
    (
        a[0].as_i64().expect("sec"),
        u32::try_from(j_u64(&a[1], "ns")).expect("ns"),
        a[2].as_bool().expect("west"),
        u32::try_from(j_u64(&a[3], "offset")).expect("offset"),
    )
}
/// `Interruption` on the wire, `[line, start, stop, day, id, lost, dropped]`: the line of the `resume` that pushed
/// it (0 for the open one), and the fork's record.
fn j_interrupt(v: &Value) -> (u64, InterruptRow) {
    let a = j_arr(v, "an interruption");
    assert_eq!(a.len(), 7, "an interruption is [line, start, stop, day, id, lost, dropped]");
    (
        j_u64(&a[0], "line"),
        (j_opt(&a[1], j_stamp), j_opt(&a[2], j_stamp), a[3].as_i64().expect("day"), j_opt(&a[4], |x| j_str(x, "id")), j_u64(&a[5], "lost"), j_strs(&a[6], "dropped")),
    )
}


fn interrupt_row(i: &Interruption) -> InterruptRow {
    (i.start.as_ref().map(stamp_of), i.end.as_ref().map(stamp_of), day_number(i.day), i.id.clone(), u64::from(i.lost_min), i.dropped.clone())
}

/// The Rust's block family, from the in-tree `Replay`.
fn rust_block(r: &Replay) -> Block {
    Block {
        days: r
            .days
            .iter()
            .map(|(d, day)| {
                let block = DayBlock {
                    first_start: day.first_start.as_ref().map(stamp_of),
                    starts: day.starts.iter().map(|s| (stamp_of(&s.t), s.id.clone(), u64::from(s.pred), s.rep.map(u64::from))).collect(),
                    block_min: u64::from(day.block_min),
                    blocks_done: u64::from(day.blocks_done),
                    load_fifths: day.load_fifths,
                    by_ci: day.minutes_by_ci.iter().map(|m| u64::from(*m)).collect(),
                    ci_unknown: day.ci_unknown.iter().map(|(k, v)| (k.clone(), u64::from(*v))).collect(),
                    done: day.done.clone(),
                    lost_min: u64::from(day.lost_min),
                    dropped: day.dropped.clone(),
                    segments: day
                        .segments
                        .iter()
                        .map(|g| {
                            let (kind, args) = match &g.kind {
                                SegmentKind::Block { id } => ("block", vec![Some(id.clone())]),
                                SegmentKind::Pause { id } => ("pause", vec![Some(id.clone())]),
                                SegmentKind::Interrupt { id } => ("interrupt", vec![id.clone()]),
                                SegmentKind::Break { r#where } => ("break", vec![r#where.clone()]),
                                SegmentKind::Routine { item, inst } => ("routine", vec![Some(item.clone()), Some(inst.clone())]),
                                SegmentKind::Idle { attributed } => ("idle", vec![Some(attributed.clone())]),
                            };
                            (stamp_of(&g.start), stamp_of(&g.end), kind.to_string(), args)
                        })
                        .collect(),
                };
                (day_number(*d), block)
            })
            .collect(),
        items: r
            .items
            .iter()
            .map(|(id, it)| {
                let item = ItemBlock {
                    minutes: u64::from(it.minutes),
                    blocks: u64::from(it.blocks),
                    by_day: it.minutes_by_day.iter().map(|(d, m)| (day_number(*d), u64::from(*m))).collect(),
                    done_at: it.done_at.iter().map(stamp_of).collect(),
                    partial_done_at: it.partial_done_at.iter().map(stamp_of).collect(),
                    stops: u64::from(it.stops),
                    extended_min: u64::from(it.extended_min),
                };
                (id.clone(), item)
            })
            .collect(),
        energy: r
            .energy
            .iter()
            .map(|o| {
                (
                    o.line,
                    stamp_of(&o.t),
                    day_number(o.day),
                    u64::from(o.pred),
                    u64::from(o.rep),
                    o.hsw,
                    o.loc.clone(),
                    o.slept_min.map(u64::from),
                    o.went.map(u64::from),
                    o.id.clone(),
                    o.from_start,
                )
            })
            .collect(),
        durations: r
            .durations
            .iter()
            .map(|o| {
                (
                    o.line,
                    stamp_of(&o.t),
                    day_number(o.day),
                    o.id.clone(),
                    u64::from(o.ci),
                    o.tags.clone(),
                    u64::from(o.est_min),
                    u64::from(o.actual_min),
                    o.went.map(u64::from),
                    o.partial,
                )
            })
            .collect(),
        interrupts: r.interrupts.iter().map(interrupt_row).collect(),
        open_block: r
            .open_block
            .as_ref()
            .map(|b| (b.id.clone(), stamp_of(&b.started), u64::from(b.worked_min), b.since.as_ref().map(stamp_of), b.paused)),
        open_interrupt: r.open_interrupt.as_ref().map(interrupt_row),
        last_effective: r.last_effective_t.as_ref().map(stamp_of),
    }
}

/// C5: a location change, `(stamp, loc)`.
type LocRow = (Stamp, String);
/// C5: an `IdleRecord`, `(t, day, attributed, min)`.
type IdleRow = (Stamp, i64, String, u64);
/// C5: a `BreakRecord`, `(t, day, planned_min, actual_min, where)`.
type BreakRow = (Stamp, i64, u64, Option<u64>, Option<String>);
/// C5: a `Demotion` with its day, `(day, t, id, from, to, est_min, stamp as demoted: writes it)`.
type DemotionRow = (i64, Stamp, String, String, String, u64, Option<String>);
/// C5: a `CloseRecord` with its day, `(day, t, period, key)`.
type CloseRow = (i64, Stamp, String, String);

/// C5: one day's header and records (`DayReplay` beyond the block family).
#[derive(Clone, Debug, PartialEq, Default)]
struct DayRec {
    wake: Option<Stamp>,
    slept_min: Option<u64>,
    onset_min: Option<u64>,
    arrival: Option<Stamp>,
    loc: Option<String>,
    window: Option<(String, String)>,
    budget: Option<u64>,
    loc_changes: Vec<LocRow>,
    leak_min: u64,
    longest_leak: u64,
    idle: Vec<IdleRow>,
    breaks: Vec<BreakRow>,
    routine_min: u64,
    plans: u64,
    replans_today: u64,
    drift_min: u64,
    last_plan_hash: Option<String>,
}

/// **C5: the day header and records family.**
#[derive(Clone, Debug, PartialEq, Default)]
struct DayFam {
    days: BTreeMap<i64, DayRec>,
    /// In file order, each with the day of its line.
    demotions: Vec<DemotionRow>,
    /// In file order, each with the day of its line.
    closes: Vec<CloseRow>,
    dropped: BTreeSet<String>,
    /// `(t, day, min)`.
    longest_leak: Option<(Stamp, i64, u64)>,
    unknown: u64,
}


/// The Rust's day family, from the in-tree `Replay`. The demotions and closes need
/// each record's day, which the fork's records do not carry: they are walked beside
/// the surviving rows of their kind, in file order, and checked against them.
fn rust_day(r: &Replay) -> DayFam {
    let survivors: Vec<_> = r.view().iter().filter(|row| !row.cancelled).collect();
    let mut demotions = Vec::new();
    let mut per_id: BTreeMap<String, usize> = BTreeMap::new();
    let mut closes = Vec::new();
    for row in &survivors {
        match &row.entry.ev {
            Event::Demote { id, .. } => {
                let k = per_id.entry(id.clone()).or_insert(0);
                let d = &r.demotions.get(id).expect("the demotions of a surviving demote")[*k];
                *k += 1;
                assert_eq!(stamp_of(&d.t), stamp_of(&row.entry.t), "demotions[{id}] in file order");
                demotions.push((day_number(row.day), stamp_of(&d.t), d.id.clone(), d.from.clone(), d.to.clone(), u64::from(d.est_min), d.stamp.map(|s| s.to_string())));
            }
            Event::Close { .. } => {
                let c = &r.closes[closes.len()];
                assert_eq!(stamp_of(&c.t), stamp_of(&row.entry.t), "closes in file order");
                closes.push((day_number(row.day), stamp_of(&c.t), c.period.clone(), c.key.clone()));
            }
            _ => {}
        }
    }
    assert_eq!(closes.len(), r.closes.len(), "closes are the surviving close rows");
    for (id, v) in &r.demotions {
        assert_eq!(per_id.get(id).copied(), Some(v.len()), "demotions[{id}] are its surviving rows");
    }
    DayFam {
        days: r
            .days
            .iter()
            .map(|(d, day)| {
                let rec = DayRec {
                    wake: day.wake.as_ref().map(stamp_of),
                    slept_min: day.slept_min.map(u64::from),
                    onset_min: day.onset_min.map(u64::from),
                    arrival: day.arrival.as_ref().map(stamp_of),
                    loc: day.loc.clone(),
                    window: day.window.as_ref().map(|w| (w[0].clone(), w[1].clone())),
                    budget: day.budget.map(u64::from),
                    loc_changes: day.loc_changes.iter().map(|(t, l)| (stamp_of(t), l.clone())).collect(),
                    leak_min: u64::from(day.leak_min),
                    longest_leak: u64::from(day.longest_leak),
                    idle: day.idle.iter().map(|i| (stamp_of(&i.t), day_number(i.day), i.attributed.clone(), u64::from(i.min))).collect(),
                    breaks: day
                        .breaks
                        .iter()
                        .map(|b| (stamp_of(&b.t), day_number(b.day), u64::from(b.planned_min), b.actual_min.map(u64::from), b.r#where.clone()))
                        .collect(),
                    routine_min: u64::from(day.routine_min),
                    plans: u64::from(day.plans),
                    replans_today: u64::from(day.replans_today),
                    drift_min: u64::from(day.drift_min),
                    last_plan_hash: day.last_plan_hash.clone(),
                };
                (day_number(*d), rec)
            })
            .collect(),
        demotions,
        closes,
        dropped: r.dropped_items.clone(),
        longest_leak: r.longest_leak.as_ref().map(|l| (stamp_of(&l.t), day_number(l.day), u64::from(l.min))),
        unknown: u64::from(r.unknown),
    }
}

/// **The kernel's facts** (C6: design §8.4's view of the log, every reading grouped by where it lives: `days`,
/// `window`, `items`, `instOther`, `named`, `open`, and the all-time counts), decoded into the families the
/// earlier steps compare. The view is checked for its own consistency on the way: a dated record sits under its
/// own day, no map key repeats, a list the Rust keeps in file order is restored by the line each record carries
/// and those lines do not repeat, and the facts' line warnings are the answer's.
fn kernel_view(log: &Value) -> Facts {
    let v = &log["facts"];
    assert!(v.is_object(), "no facts: {}", &log.to_string()[..log.to_string().len().min(400)]);
    let (mut block, mut completion, mut day) = (Block::default(), Completion::default(), DayFam::default());
    let mut seams = BTreeMap::new();
    let mut rows: Vec<RowView> = Vec::new();
    let mut interrupts: Vec<(u64, InterruptRow)> = Vec::new();
    let mut demotions: Vec<(u64, DemotionRow)> = Vec::new();
    let mut closes: Vec<(u64, CloseRow)> = Vec::new();
    // W3: a day record's header carries its stamp and written offset (the codec's shape); the display the view compares
    // is the one the answer's own headers carry (`want.headersFrom: 1`), matched by line.
    let displays: BTreeMap<u64, String> = j_arr(&log["headers"], "headers")
        .iter()
        .map(|h| (j_u64(&h[0], "line"), j_str(&h[5], "display")))
        .collect();
    for p in j_arr(&v["days"], "days") {
        let p = j_arr(p, "a day");
        assert_eq!(p.len(), 9, "a day is [day, record, seam, energy, durations, interrupts, demotions, closes, headers]");
        let d = p[0].as_i64().expect("a day");
        assert!(!seams.contains_key(&d) && !block.days.contains_key(&d) && rows.iter().all(|r| r.3 != d), "a repeated day {d}");
        if !p[1].is_null() {
            let a = j_arr(&p[1], "a day record");
            assert_eq!(a.len(), 28, "a day record has 28 fields: {}", p[1]);
            let mut ci_unknown = BTreeMap::new();
            for c in j_arr(&a[6], "ciUnknown") {
                let c = j_arr(c, "a ciUnknown pair");
                assert!(ci_unknown.insert(j_str(&c[0], "id"), j_u64(&c[1], "min")).is_none(), "a repeated ciUnknown id");
            }
            block.days.insert(
                d,
                DayBlock {
                    first_start: j_opt(&a[0], j_stamp),
                    starts: j_arr(&a[1], "starts")
                        .iter()
                        .map(|r| {
                            let r = j_arr(r, "a start");
                            (j_stamp(&r[0]), j_str(&r[1], "id"), j_u64(&r[2], "pred"), j_opt(&r[3], |x| j_u64(x, "rep")))
                        })
                        .collect(),
                    block_min: j_u64(&a[2], "blockMin"),
                    blocks_done: j_u64(&a[3], "blocksDone"),
                    load_fifths: j_u64(&a[4], "loadFifths"),
                    by_ci: j_arr(&a[5], "byCi").iter().map(|c| j_u64(c, "byCi")).collect(),
                    ci_unknown,
                    done: j_strs(&a[7], "done"),
                    lost_min: j_u64(&a[8], "lostMin"),
                    dropped: j_strs(&a[9], "dropped"),
                    segments: j_arr(&a[10], "segments")
                        .iter()
                        .map(|g| {
                            let g = j_arr(g, "a segment");
                            assert_eq!(g.len(), 3, "a segment is [start, stop, kind] (W3: the codec's shape)");
                            let (kind, args) = j_seg_kind(&g[2]);
                            (j_stamp(&g[0]), j_stamp(&g[1]), kind, args)
                        })
                        .collect(),
                },
            );
            day.days.insert(
                d,
                DayRec {
                    wake: j_opt(&a[11], j_stamp),
                    slept_min: j_opt(&a[12], |x| j_u64(x, "sleptMin")),
                    onset_min: j_opt(&a[13], |x| j_u64(x, "onsetMin")),
                    arrival: j_opt(&a[14], j_stamp),
                    loc: j_opt(&a[15], |x| j_str(x, "loc")),
                    window: j_opt(&a[16], |x| {
                        let w = j_arr(x, "a window");
                        (j_str(&w[0], "window"), j_str(&w[1], "window"))
                    }),
                    budget: j_opt(&a[17], |x| j_u64(x, "budget")),
                    loc_changes: j_arr(&a[18], "locChanges")
                        .iter()
                        .map(|c| {
                            let c = j_arr(c, "a location change");
                            (j_stamp(&c[0]), j_str(&c[1], "loc"))
                        })
                        .collect(),
                    leak_min: j_u64(&a[19], "leakMin"),
                    longest_leak: j_u64(&a[20], "longestLeak"),
                    idle: j_arr(&a[21], "idle")
                        .iter()
                        .map(|r| {
                            let r = j_arr(r, "an idle record");
                            (j_stamp(&r[0]), r[1].as_i64().expect("day"), j_str(&r[2], "attributed"), j_u64(&r[3], "min"))
                        })
                        .collect(),
                    breaks: j_arr(&a[22], "breaks")
                        .iter()
                        .map(|r| {
                            let r = j_arr(r, "a break");
                            (j_stamp(&r[0]), r[1].as_i64().expect("day"), j_u64(&r[2], "planned"), j_opt(&r[3], |x| j_u64(x, "actual")), j_opt(&r[4], |x| j_str(x, "where")))
                        })
                        .collect(),
                    routine_min: j_u64(&a[23], "routineMin"),
                    plans: j_u64(&a[24], "plans"),
                    replans_today: j_u64(&a[25], "replansToday"),
                    drift_min: j_u64(&a[26], "driftMin"),
                    last_plan_hash: j_opt(&a[27], |x| j_str(x, "lastPlanHash")),
                },
            );
        }
        if !p[2].is_null() {
            seams.insert(d, j_seam(&p[2]));
        }
        for o in j_arr(&p[3], "energy") {
            let row = j_energy(o);
            assert_eq!(row.2, d, "an energy observation under its own day");
            block.energy.push(row);
        }
        for o in j_arr(&p[4], "durations") {
            let row = j_duration(o);
            assert_eq!(row.2, d, "a duration observation under its own day");
            block.durations.push(row);
        }
        for o in j_arr(&p[5], "interrupts") {
            let (line, row) = j_interrupt(o);
            assert_eq!(row.2, d, "an interruption under its own day");
            interrupts.push((line, row));
        }
        for o in j_arr(&p[6], "demotions") {
            let r = j_arr(o, "a demotion");
            demotions.push((
                j_u64(&r[0], "line"),
                (d, j_stamp(&r[1]), j_str(&r[2], "id"), j_str(&r[3], "from"), j_str(&r[4], "to"), j_u64(&r[5], "est"), j_opt(&r[6], j_demotion_stamp)),
            ));
        }
        for o in j_arr(&p[7], "closes") {
            let r = j_arr(o, "a close");
            closes.push((j_u64(&r[0], "line"), (d, j_stamp(&r[1]), j_str(&r[2], "period"), j_str(&r[3], "key"))));
        }
        for h in j_arr(&p[8], "headers") {
            let h = j_arr(h, "a header");
            assert_eq!(h.len(), 6, "a day's header is [line, tag, id, cancelled, [sec, ns], [west, offSec]] (W3: the codec's shape)");
            let line = j_u64(&h[0], "line");
            let display = displays.get(&line).unwrap_or_else(|| panic!("line {line}: a day's header with no header in the answer")).clone();
            rows.push((line, j_str(&h[1], "tag"), j_opt(&h[2], |x| j_str(x, "id")), d, h[3].as_bool().expect("cancelled"), display));
        }
    }
    fn in_line_order<T>(mut xs: Vec<(u64, T)>, what: &str) -> Vec<T> {
        xs.sort_by_key(|x| x.0);
        assert!(xs.windows(2).all(|w| w[0].0 < w[1].0), "{what}: a line carried twice");
        xs.into_iter().map(|x| x.1).collect()
    }
    block.energy = in_line_order(block.energy.drain(..).map(|o| (o.0, o)).collect(), "energy");
    block.durations = in_line_order(block.durations.drain(..).map(|o| (o.0, o)).collect(), "durations");
    block.interrupts = in_line_order(interrupts, "interrupts");
    day.demotions = in_line_order(demotions, "demotions");
    day.closes = in_line_order(closes, "closes");
    rows = in_line_order(rows.into_iter().map(|r| (r.0, r)).collect(), "headers");
    for p in j_arr(&v["items"], "items") {
        let p = j_arr(p, "an item");
        assert_eq!(p.len(), 6, "an item is [id, record, lastDone, dropped, doneFirst, doneCount]");
        let id = j_str(&p[0], "id");
        if !p[1].is_null() {
            let o = j_arr(&p[1], "an item record");
            let item = ItemBlock {
                minutes: j_u64(&o[0], "minutes"),
                blocks: j_u64(&o[1], "blocks"),
                by_day: BTreeMap::new(),
                done_at: j_arr(&o[2], "doneAt").iter().map(j_stamp).collect(),
                partial_done_at: j_arr(&o[3], "partialDoneAt").iter().map(j_stamp).collect(),
                stops: j_u64(&o[4], "stops"),
                extended_min: j_u64(&o[5], "extendedMin"),
            };
            assert!(block.items.insert(id.clone(), item).is_none(), "a repeated item {id}");
        }
        if let Some(t) = j_opt(&p[2], j_stamp) {
            assert!(completion.last_done.insert(id.clone(), t).is_none(), "a repeated lastDone");
        }
        if p[3].as_bool().expect("dropped") {
            assert!(day.dropped.insert(id.clone()), "a repeated dropped id");
        }
        let (first, count) = (p[4].as_i64(), j_u64(&p[5], "doneCount"));
        if count > 0 || first.is_some() {
            assert!(completion.done_first.insert(id.clone(), (first, count)).is_none(), "a repeated done count");
        }
    }
    for w in j_arr(&v["window"], "window") {
        let w = j_arr(w, "a window date");
        assert_eq!(w.len(), 4, "a window date is [date, itemMin, done, inst]");
        let d = w[0].as_i64().expect("a date");
        for m in j_arr(&w[1], "itemMin") {
            let m = j_arr(m, "an item's minutes");
            let id = j_str(&m[0], "id");
            let item = block.items.get_mut(&id).unwrap_or_else(|| panic!("minutes on {d} of {id}, which has no record"));
            assert!(item.by_day.insert(d, j_u64(&m[1], "min")).is_none(), "a repeated item day");
        }
        for id in j_strs(&w[2], "done") {
            assert!(completion.done_dates.entry(id).or_default().insert(d), "a repeated done date");
        }
        for r in j_arr(&w[3], "inst") {
            let (key, row) = j_instance(r);
            assert!(completion.instances.insert(key, row).is_none(), "a repeated instance");
        }
    }
    for r in j_arr(&v["instOther"], "instOther") {
        let (key, row) = j_instance(r);
        assert!(completion.instances.insert(key, row).is_none(), "a repeated instance");
    }
    for r in j_arr(&v["named"], "named") {
        // W3: the codec's shape, `[[name, id], [[latestLine, latestStamp], [datedDate, [datedLine, datedStamp]]]]`.
        let r = j_arr(r, "a named record");
        let (key, rec) = (j_arr(&r[0], "a named key"), j_arr(&r[1], "a named record's value"));
        let (latest, dated) = (j_arr(&rec[0], "the latest occurrence"), j_arr(&rec[1], "the dated occurrence"));
        let dated = j_arr(&dated[1], "the dated occurrence's line and stamp");
        let row = (j_u64(&latest[0], "latest line"), j_stamp(&latest[1]), j_u64(&dated[0], "dated line"), j_stamp(&dated[1]));
        assert!(completion.named.insert((j_str(&key[0], "name"), j_opt(&key[1], |x| j_str(x, "id"))), row).is_none(), "a repeated named key");
    }
    for x in j_arr(&v["replayWarnings"], "replayWarnings") {
        // W3: the codec's shape, `[line, raw]` (the one replay warning, `unknownInstanceStatus`).
        let x = j_arr(x, "a replay warning");
        completion.warnings.push((j_u64(&x[0], "line"), j_str(&x[1], "raw")));
    }
    block.open_block = j_opt(&v["open"]["block"], |o| {
        let o = j_arr(o, "the open block");
        (j_str(&o[0], "id"), j_stamp(&o[1]), j_u64(&o[2], "worked"), j_opt(&o[3], j_stamp), o[4].as_bool().expect("paused"))
    });
    block.open_interrupt = j_opt(&v["open"]["interrupt"], |o| {
        let (line, row) = j_interrupt(o);
        assert_eq!(line, 0, "the open interruption is pushed by no line");
        row
    });
    block.last_effective = j_opt(&v["lastEffective"], j_stamp);
    day.unknown = j_u64(&v["unknown"], "unknown");
    day.longest_leak = j_opt(&v["longestLeak"], |x| {
        let x = j_arr(x, "the longest leak");
        (j_stamp(&x[0]), x[1].as_i64().expect("day"), j_u64(&x[2], "min"))
    });
    let warnings: Vec<Value> = j_arr(&log["warnings"], "warnings").clone();
    let first = j_arr(&v["warnings"]["first"], "warnings.first");
    assert_eq!(first.as_slice(), &warnings[..warnings.len().min(256)], "the facts' line warnings are the answer's first 256");
    assert_eq!(j_u64(&v["warnings"]["overflow"], "overflow"), warnings.len().saturating_sub(256) as u64);
    // The answer's headers (`want.headersFrom: 1`) are the view's rows, with their days.
    let top: Vec<RowView> = j_arr(&log["headers"], "headers")
        .iter()
        .map(|h| {
            let h = j_arr(h, "a header");
            assert_eq!(h.len(), 6, "a header is [line, tag, id, day, cancelled, display]");
            (j_u64(&h[0], "line"), j_str(&h[1], "tag"), j_opt(&h[2], |x| j_str(x, "id")), h[3].as_i64().expect("day"), h[4].as_bool().expect("cancelled"), j_str(&h[5], "display"))
        })
        .collect();
    assert_eq!(top, rows, "the answer's headers are the days' headers in file order");
    Facts {
        cancelled: rows.iter().filter(|r| r.4).map(|r| r.0).collect(),
        days: rows.iter().map(|r| (r.0, r.3)).collect(),
        block,
        completion,
        day,
        seams,
        counts: (j_u64(&v["entryCount"], "entryCount"), j_u64(&log["lines"], "lines"), v["lastDay"].as_i64()),
        rows,
        warnings: warnings.iter().map(|w| w["line"].as_u64().expect("a line")).collect(),
    }
}

/// C6: an idle mark, `(kind, stamp, actual_min)`; a day's seam.
fn j_seam(v: &Value) -> SeamRow {
    let a = j_arr(v, "a seam");
    assert_eq!(a.len(), 3, "a seam is [sinceBreak, idleMarks, lastT]");
    let marks = j_arr(&a[1], "idleMarks")
        .iter()
        .map(|m| {
            // W3: the codec's numeral tags, `[0, t]` pause … `[4, t, actual]` break.
            let m = j_arr(m, "an idle mark");
            let kind = match j_u64(&m[0], "an idle mark's tag") {
                0 => "pause",
                1 => "interrupt",
                2 => "unpause",
                3 => "resume",
                4 => "break",
                t => panic!("an idle mark tag {t}"),
            }
            .to_string();
            let actual = if kind == "break" { j_opt(&m[2], |x| j_u64(x, "actual")) } else {
                assert_eq!(m.len(), 2, "only a break mark carries minutes");
                None
            };
            (kind, j_stamp(&m[1]), actual)
        })
        .collect();
    (j_opt(&a[0], j_stamp), marks, j_opt(&a[2], j_stamp))
}

fn j_energy(o: &Value) -> EnergyRow {
    let o = j_arr(o, "an energy observation");
    (
        j_u64(&o[0], "line"),
        j_stamp(&o[1]),
        o[2].as_i64().expect("day"),
        j_u64(&o[3], "pred"),
        j_u64(&o[4], "rep"),
        o[5].as_f64().expect("hsw"),
        j_str(&o[6], "loc"),
        j_opt(&o[7], |x| j_u64(x, "slept")),
        j_opt(&o[8], |x| j_u64(x, "went")),
        j_opt(&o[9], |x| j_str(x, "id")),
        o[10].as_bool().expect("fromStart"),
    )
}

fn j_duration(o: &Value) -> DurationRow {
    let o = j_arr(o, "a duration observation");
    (
        j_u64(&o[0], "line"),
        j_stamp(&o[1]),
        o[2].as_i64().expect("day"),
        j_str(&o[3], "id"),
        j_u64(&o[4], "ci"),
        j_strs(&o[5], "tags"),
        j_u64(&o[6], "est"),
        j_u64(&o[7], "actual"),
        j_opt(&o[8], |x| j_u64(x, "went")),
        o[9].as_bool().expect("partial"),
    )
}

/// W3: an instance in the codec's shape, `[[item, inst], [stamp, status, raw, actualMin]]`, its status a numeral (done 0,
/// pending 1, missed 2, expired 3, skipped 4).
fn j_instance(r: &Value) -> ((String, String), InstanceRow) {
    let r = j_arr(r, "an instance");
    let (key, rec) = (j_arr(&r[0], "an instance key"), j_arr(&r[1], "an instance record"));
    let status = match j_u64(&rec[1], "status") {
        0 => "done",
        1 => "pending",
        2 => "missed",
        3 => "expired",
        4 => "skipped",
        s => panic!("an instance status {s}"),
    };
    ((j_str(&key[0], "item"), j_str(&key[1], "inst")), (j_stamp(&rec[0]), status.to_string(), j_str(&rec[2], "raw"), j_opt(&rec[3], |x| j_u64(x, "actualMin"))))
}

/// W3: a segment kind in the codec's numeral tags (`[0, id]` block, `[1, id]` pause, `[2, id]` interrupt, `[3, where]`
/// break, `[4, item, inst]` routine, `[5, attributed]` idle), as its name and arguments.
fn j_seg_kind(k: &Value) -> (String, Vec<Option<String>>) {
    let k = j_arr(k, "a segment kind");
    let name = match j_u64(&k[0], "a segment kind's tag") {
        0 => "block",
        1 => "pause",
        2 => "interrupt",
        3 => "break",
        4 => "routine",
        5 => "idle",
        t => panic!("a segment kind tag {t}"),
    };
    (name.to_string(), k[1..].iter().map(|x| j_opt(x, |y| j_str(y, "a segment argument"))).collect())
}

/// W3: a demotion's stamp in the codec's shape, `[0, week]` or `[1, day]`, as `demoted:` writes it (`W37`, `D07`).
fn j_demotion_stamp(v: &Value) -> String {
    let a = j_arr(v, "a demotion stamp");
    match j_u64(&a[0], "a stamp's tag") {
        0 => format!("W{:02}", j_u64(&a[1], "week")),
        1 => format!("D{:02}", j_u64(&a[1], "day")),
        t => panic!("a stamp tag {t}"),
    }
}

/// The lines of `text` as the host sends them: split on `\n`, the empty segment after a final `\n` not sent
/// (it is not a line; `terminated` says the last line had its `\n`).
fn segments(text: &str) -> Vec<Value> {
    let mut segs: Vec<Value> = text.split('\n').map(|s| Value::String(s.to_string())).collect();
    if text.is_empty() || text.ends_with('\n') {
        segs.pop();
    }
    segs
}

/// **The kernel's `log` answer**: one genesis call over the whole text, facts and every header asked.
fn kernel_answer(text: &str, tz: Tz) -> Value {
    let segs = segments(text);
    assert!(segs.len() <= 8_192, "T5 sends one call, within the memory gate's line bound (W3, gap 102)");
    let req = json!({
        "docs": [], "now": "2026-09-15", "tz": table(tz),
        "log": {"ckpt": null, "from": 1, "lines": segs, "terminated": text.is_empty() || text.ends_with('\n'),
                "reseal": null, "want": {"facts": true, "headersFrom": 1}}
    });
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("the response is JSON");
    assert!(resp["ok"]["log"].is_object(), "no log answer: {}", &raw[..raw.len().min(400)]);
    resp["ok"]["log"].clone()
}

/// **The kernel's facts**.
fn kernel_facts(text: &str, tz: Tz) -> Facts {
    kernel_view(&kernel_answer(text, tz))
}

/// C6: a kernel stamp as chrono's `DateTime<FixedOffset>`.
fn date_time(s: &Stamp) -> DateTime<FixedOffset> {
    let off = FixedOffset::east_opt(if s.2 { -(s.3 as i32) } else { s.3 as i32 }).expect("an offset");
    DateTime::from_timestamp(s.0 - EPOCH_FROM_CE, s.1).expect("an instant").with_timezone(&off)
}

/// C6: a kernel day as a date.
fn date_of(d: i64) -> NaiveDate {
    NaiveDate::from_num_days_from_ce_opt(i32::try_from(d + 1).expect("a day")).expect("a date")
}

fn u32_of(n: u64) -> u32 {
    u32::try_from(n).expect("a u32 (P17: the decoder at S refuses minutesOverflow by name)")
}

fn u8_of(n: u64) -> u8 {
    u8::try_from(n).expect("a u8 (the kernel's `U8`)")
}

/// **C6: the kernel's facts as a `tm_core::log::Replay`** (the decoder `kernel_log::decode_facts` will be at S),
/// so the fork's own `PartialEq` and `ported_facts()` compare the whole of it. Two fields are not the kernel's:
/// `events`, whose occurrence lists the kernel does not keep (design §8.4: the latest per `(name, id?)`, compared
/// through every `latest_named` query above), and `warnings`' text, which names the warned line's written stamp
/// (compared above by line and status). Both are taken from the fork, as are the line bookkeeping `rows` and
/// `line_count` (compared as view rows).
fn kernel_replay(f: &Facts, tz: Tz, r: &Replay) -> Replay {
    let segment = |g: &(Stamp, Stamp, String, Vec<Option<String>>)| {
        let arg = |i: usize| g.3.get(i).cloned().flatten();
        LogSegment {
            start: date_time(&g.0),
            end: date_time(&g.1),
            kind: match g.2.as_str() {
                "block" => SegmentKind::Block { id: arg(0).expect("an id") },
                "pause" => SegmentKind::Pause { id: arg(0).expect("an id") },
                "interrupt" => SegmentKind::Interrupt { id: arg(0) },
                "break" => SegmentKind::Break { r#where: arg(0) },
                "routine" => SegmentKind::Routine { item: arg(0).expect("an item"), inst: arg(1).expect("an inst") },
                "idle" => SegmentKind::Idle { attributed: arg(0).expect("an attribution") },
                other => panic!("a segment kind {other}"),
            },
        }
    };
    let interruption = |i: &InterruptRow| Interruption {
        start: i.0.as_ref().map(date_time),
        end: i.1.as_ref().map(date_time),
        day: date_of(i.2),
        id: i.3.clone(),
        lost_min: u32_of(i.4),
        dropped: i.5.clone(),
    };
    let status = |s: &str| match s {
        "pending" => InstanceStatus::Pending,
        "done" => InstanceStatus::Done,
        "missed" => InstanceStatus::Missed,
        "expired" => InstanceStatus::Expired,
        "skipped" => InstanceStatus::Skipped,
        other => panic!("a status {other}"),
    };
    let days = f
        .block
        .days
        .iter()
        .map(|(d, b)| {
            let x = &f.day.days[d];
            let rec = DayReplay {
                date: date_of(*d),
                wake: x.wake.as_ref().map(date_time),
                slept_min: x.slept_min.map(u32_of),
                onset_min: x.onset_min.map(u32_of),
                arrival: x.arrival.as_ref().map(date_time),
                loc: x.loc.clone(),
                window: x.window.clone().map(|w| [w.0, w.1]),
                budget: x.budget.map(u32_of),
                loc_changes: x.loc_changes.iter().map(|(t, l)| (date_time(t), l.clone())).collect(),
                first_start: b.first_start.as_ref().map(date_time),
                starts: b
                    .starts
                    .iter()
                    .map(|s| StartRecord { t: date_time(&s.0), id: s.1.clone(), pred: u8_of(s.2), rep: s.3.map(u8_of) })
                    .collect(),
                block_min: u32_of(b.block_min),
                blocks_done: u32_of(b.blocks_done),
                load_fifths: b.load_fifths,
                minutes_by_ci: std::array::from_fn(|i| u32_of(b.by_ci[i])),
                ci_unknown: b.ci_unknown.iter().map(|(k, m)| (k.clone(), u32_of(*m))).collect(),
                done: b.done.clone(),
                lost_min: u32_of(b.lost_min),
                dropped: b.dropped.clone(),
                leak_min: u32_of(x.leak_min),
                longest_leak: u32_of(x.longest_leak),
                idle: x.idle.iter().map(|i| IdleRecord { t: date_time(&i.0), day: date_of(i.1), attributed: i.2.clone(), min: u32_of(i.3) }).collect(),
                breaks: x
                    .breaks
                    .iter()
                    .map(|k| BreakRecord { t: date_time(&k.0), day: date_of(k.1), planned_min: u32_of(k.2), actual_min: k.3.map(u32_of), r#where: k.4.clone() })
                    .collect(),
                routine_min: u32_of(x.routine_min),
                plans: u32_of(x.plans),
                replans_today: u32_of(x.replans_today),
                drift_min: u32_of(x.drift_min),
                last_plan_hash: x.last_plan_hash.clone(),
                segments: b.segments.iter().map(segment).collect(),
            };
            (date_of(*d), rec)
        })
        .collect();
    let mut demotions: BTreeMap<String, Vec<Demotion>> = BTreeMap::new();
    for x in &f.day.demotions {
        demotions.entry(x.2.clone()).or_default().push(Demotion {
            t: date_time(&x.1),
            id: x.2.clone(),
            from: x.3.clone(),
            to: x.4.clone(),
            est_min: u32_of(x.5),
            stamp: x.6.as_ref().map(|s| tm_core::model::Stamp::parse(s).expect("a stamp")),
        });
    }
    let mut instances: BTreeMap<String, BTreeMap<String, InstanceRecord>> = BTreeMap::new();
    for ((item, inst), row) in &f.completion.instances {
        instances.entry(item.clone()).or_default().insert(
            inst.clone(),
            InstanceRecord { t: date_time(&row.0), status: status(&row.1), raw_status: row.2.clone(), actual_min: row.3.map(u32_of) },
        );
    }
    Replay {
        tz,
        range: None,
        days,
        items: f
            .block
            .items
            .iter()
            .map(|(id, it)| {
                let item = ItemReplay {
                    id: id.clone(),
                    minutes: u32_of(it.minutes),
                    blocks: u32_of(it.blocks),
                    minutes_by_day: it.by_day.iter().map(|(d, m)| (date_of(*d), u32_of(*m))).collect(),
                    done_at: it.done_at.iter().map(date_time).collect(),
                    partial_done_at: it.partial_done_at.iter().map(date_time).collect(),
                    stops: u32_of(it.stops),
                    extended_min: u32_of(it.extended_min),
                };
                (id.clone(), item)
            })
            .collect(),
        instances,
        energy: f
            .block
            .energy
            .iter()
            .map(|o| EnergyObs {
                line: o.0,
                t: date_time(&o.1),
                day: date_of(o.2),
                pred: u8_of(o.3),
                rep: u8_of(o.4),
                hsw: o.5,
                loc: o.6.clone(),
                slept_min: o.7.map(u32_of),
                went: o.8.map(u8_of),
                id: o.9.clone(),
                from_start: o.10,
            })
            .collect(),
        durations: f
            .block
            .durations
            .iter()
            .map(|o| DurationObs {
                line: o.0,
                t: date_time(&o.1),
                day: date_of(o.2),
                id: o.3.clone(),
                ci: u8_of(o.4),
                tags: o.5.clone(),
                est_min: u32_of(o.6),
                actual_min: u32_of(o.7),
                went: o.8.map(u8_of),
                partial: o.9,
            })
            .collect(),
        interrupts: f.block.interrupts.iter().map(interruption).collect(),
        events: r.events.clone(),
        demotions,
        closes: f.day.closes.iter().map(|c| CloseRecord { t: date_time(&c.1), period: c.2.clone(), key: c.3.clone() }).collect(),
        dropped_items: f.day.dropped.clone(),
        done_items: f.completion.last_done.keys().cloned().collect(),
        last_done: f.completion.last_done.iter().map(|(k, t)| (k.clone(), date_time(t))).collect(),
        done_dates: f.completion.done_dates.iter().map(|(k, ds)| (k.clone(), ds.iter().map(|d| date_of(*d)).collect())).collect(),
        longest_leak: f.day.longest_leak.as_ref().map(|l| LeakRecord { t: date_time(&l.0), day: date_of(l.1), min: u32_of(l.2) }),
        open_block: f.block.open_block.as_ref().map(|b| OpenBlock {
            id: b.0.clone(),
            started: date_time(&b.1),
            worked_min: u32_of(b.2),
            since: b.3.as_ref().map(date_time),
            paused: b.4,
        }),
        open_interrupt: f.block.open_interrupt.as_ref().map(interruption),
        unknown: u32_of(f.day.unknown),
        warnings: r.warnings.clone(),
        seams: f
            .seams
            .iter()
            .map(|(d, s)| {
                let seam = DaySeam {
                    since_break: s.0.as_ref().map(date_time),
                    idle_marks: s
                        .1
                        .iter()
                        .map(|(kind, t, actual)| {
                            let t = date_time(t);
                            match kind.as_str() {
                                "pause" => IdleMark::Pause(t),
                                "interrupt" => IdleMark::Interrupt(t),
                                "unpause" => IdleMark::Unpause(t),
                                "resume" => IdleMark::Resume(t),
                                "break" => IdleMark::Break { t, actual_min: actual.map(u32_of) },
                                other => panic!("an idle mark {other}"),
                            }
                        })
                        .collect(),
                    last_t: s.2.as_ref().map(date_time),
                };
                (date_of(*d), seam)
            })
            .collect(),
        last_effective_t: f.block.last_effective.as_ref().map(date_time),
        rows: r.rows.clone(),
        line_count: r.line_count,
    }
}

/// **The Rust's facts**, through the test chokepoint.
fn rust_facts(text: &str, tz: Tz) -> Facts {
    let r = replay::replay_of_text(text, tz);
    Facts {
        cancelled: r.view().iter().filter(|row| row.cancelled).map(|row| row.line).collect(),
        days: r.view().iter().map(|row| (row.line, day_number(row.day))).collect(),
        block: rust_block(&r),
        completion: rust_completion(&r, tz),
        day: rust_day(&r),
        seams: r
            .seams
            .iter()
            .map(|(d, s)| {
                let marks = s
                    .idle_marks
                    .iter()
                    .map(|m| match m {
                        IdleMark::Pause(t) => ("pause".to_string(), stamp_of(t), None),
                        IdleMark::Interrupt(t) => ("interrupt".to_string(), stamp_of(t), None),
                        IdleMark::Unpause(t) => ("unpause".to_string(), stamp_of(t), None),
                        IdleMark::Resume(t) => ("resume".to_string(), stamp_of(t), None),
                        IdleMark::Break { t, actual_min } => ("break".to_string(), stamp_of(t), actual_min.map(u64::from)),
                    })
                    .collect();
                (day_number(*d), (s.since_break.as_ref().map(stamp_of), marks, s.last_t.as_ref().map(stamp_of)))
            })
            .collect(),
        rows: r
            .view()
            .iter()
            .map(|row| (row.line, row.entry.ev.name().to_string(), row.entry.ev.primary_id().map(str::to_string), day_number(row.day), row.cancelled, row.display()))
            .collect(),
        counts: (r.entry_count() as u64, r.line_count(), r.days.keys().last().map(|d| day_number(*d))),
        warnings: replay::warning_lines_of_text(text),
    }
}

/// Compare one log; the kernel's facts are returned for the arms' own checks.
fn assert_parity(name: &str, text: &str, tz: Tz) -> Facts {
    assert_parity_answer(name, text, tz, &kernel_answer(text, tz))
}

/// Compare one log with a kernel `log` answer built any way (W3: a windowed answer merged with its sealed records).
fn assert_parity_answer(name: &str, text: &str, tz: Tz, answer: &Value) -> Facts {
    let (k, r) = (kernel_view(answer), rust_facts(text, tz));
    // C5: the kernel creates every day the fork creates, and no other: its block
    // records and its day records are one set of days, the Rust's.
    let (kd, rd): (BTreeSet<_>, BTreeSet<_>) = (k.block.days.keys().collect(), r.block.days.keys().collect());
    assert!(k.block.days.keys().eq(k.day.days.keys()), "{name} ({}): the kernel's block and day records name different days", tz.name());
    if kd != rd {
        panic!(
            "{name} ({}): the days differ\n kernel only: {:?}\n rust only: {:?}",
            tz.name(),
            kd.difference(&rd).collect::<Vec<_>>(),
            rd.difference(&kd).collect::<Vec<_>>()
        );
    }
    if k.day != r.day {
        let (kf, rf) = (&k.day, &r.day);
        let mut why = Vec::new();
        for (d, x) in &rf.days {
            if kf.days.get(d) != Some(x) {
                why.push(format!("day {d}:\n  kernel {:?}\n  rust   {:?}", kf.days.get(d), x));
            }
        }
        if kf.demotions != rf.demotions {
            why.push(format!("demotions:\n  kernel {:?}\n  rust   {:?}", kf.demotions, rf.demotions));
        }
        if kf.closes != rf.closes {
            why.push(format!("closes:\n  kernel {:?}\n  rust   {:?}", kf.closes, rf.closes));
        }
        if (&kf.dropped, &kf.longest_leak, kf.unknown) != (&rf.dropped, &rf.longest_leak, rf.unknown) {
            why.push(format!(
                "dropped/longest leak/unknown:\n  kernel {:?} {:?} {}\n  rust   {:?} {:?} {}",
                kf.dropped, kf.longest_leak, kf.unknown, rf.dropped, rf.longest_leak, rf.unknown
            ));
        }
        why.truncate(5);
        panic!("{name} ({}): the day family differs\n{}", tz.name(), why.join("\n"));
    }
    if k.block != r.block {
        let (kb, rb) = (&k.block, &r.block);
        let mut why = Vec::new();
        for (d, b) in &rb.days {
            if kb.days.get(d) != Some(b) {
                why.push(format!("day {d}:\n  kernel {:?}\n  rust   {:?}", kb.days.get(d), b));
            }
        }
        for (i, b) in &rb.items {
            if kb.items.get(i) != Some(b) {
                why.push(format!("item {i}:\n  kernel {:?}\n  rust   {:?}", kb.items.get(i), b));
            }
        }
        for i in kb.items.keys().filter(|i| !rb.items.contains_key(*i)) {
            why.push(format!("item {i}: only the kernel has it"));
        }
        if kb.energy != rb.energy {
            why.push(format!("energy:\n  kernel {:?}\n  rust   {:?}", kb.energy, rb.energy));
        }
        if kb.durations != rb.durations {
            why.push(format!("durations:\n  kernel {:?}\n  rust   {:?}", kb.durations, rb.durations));
        }
        if kb.interrupts != rb.interrupts {
            why.push(format!("interrupts:\n  kernel {:?}\n  rust   {:?}", kb.interrupts, rb.interrupts));
        }
        if (&kb.open_block, &kb.open_interrupt, &kb.last_effective) != (&rb.open_block, &rb.open_interrupt, &rb.last_effective) {
            why.push(format!(
                "open/last:\n  kernel {:?} {:?} {:?}\n  rust   {:?} {:?} {:?}",
                kb.open_block, kb.open_interrupt, kb.last_effective, rb.open_block, rb.open_interrupt, rb.last_effective
            ));
        }
        why.truncate(5);
        panic!("{name} ({}): the block family differs\n{}", tz.name(), why.join("\n"));
    }
    if k.completion != r.completion {
        let (kc, rc) = (&k.completion, &r.completion);
        let mut why = Vec::new();
        let keys: BTreeSet<_> = kc.last_done.keys().chain(rc.last_done.keys()).collect();
        for i in keys.into_iter().filter(|i| kc.last_done.get(*i) != rc.last_done.get(*i)) {
            why.push(format!("last_done {i}: kernel {:?} rust {:?}", kc.last_done.get(i), rc.last_done.get(i)));
        }
        let keys: BTreeSet<_> = kc.done_dates.keys().chain(rc.done_dates.keys()).collect();
        for i in keys.into_iter().filter(|i| kc.done_dates.get(*i) != rc.done_dates.get(*i)) {
            why.push(format!("done_dates {i}: kernel {:?} rust {:?}", kc.done_dates.get(i), rc.done_dates.get(i)));
        }
        let keys: BTreeSet<_> = kc.instances.keys().chain(rc.instances.keys()).collect();
        for i in keys.into_iter().filter(|i| kc.instances.get(*i) != rc.instances.get(*i)) {
            why.push(format!("instance {i:?}: kernel {:?} rust {:?}", kc.instances.get(i), rc.instances.get(i)));
        }
        let keys: BTreeSet<_> = kc.named.keys().chain(rc.named.keys()).collect();
        for i in keys.into_iter().filter(|i| kc.named.get(*i) != rc.named.get(*i)) {
            why.push(format!("named {i:?}: kernel {:?} rust {:?}", kc.named.get(i), rc.named.get(i)));
        }
        if kc.warnings != rc.warnings {
            why.push(format!("replay warnings:\n  kernel {:?}\n  rust   {:?}", kc.warnings, rc.warnings));
        }
        why.truncate(5);
        panic!("{name} ({}): the completion family differs\n{}", tz.name(), why.join("\n"));
    }
    // C4: every `latest_named` query the fork answers (every name, every id it was
    // addressed to and one it was not), from the kernel's per-key records.
    let rr = replay::replay_of_text(text, tz);
    let ids: BTreeSet<String> = rr.events.values().flatten().filter_map(|e| e.id.clone()).chain(["zz-absent".to_string()]).collect();
    let names: BTreeSet<&str> = rr.event_names().collect();
    assert_eq!(names, k.completion.named.keys().map(|(n, _)| n.as_str()).collect::<BTreeSet<_>>(), "{name}: event_names");
    for n in names.iter().copied().chain(["zz-absent"]) {
        for id in &ids {
            let fork = rr.latest_named(n, id, tz).map(|l| (stamp_of(&l.latest), stamp_of(&l.latest_dated)));
            assert_eq!(kernel_latest_named(&k.completion, n, id, tz), fork, "{name}: latest_named({n}, {id})");
            LATEST_NAMED_QUERIES.with(|q| q.set(q.get() + 1));
        }
    }
    if k.cancelled != r.cancelled {
        let (ks, rs): (BTreeSet<_>, BTreeSet<_>) = (k.cancelled.iter().collect(), r.cancelled.iter().collect());
        let lines: Vec<&str> = text.split('\n').collect();
        let show = |n: &&u64| format!("{n}: {}", lines.get(**n as usize - 1).copied().unwrap_or("?"));
        panic!(
            "{name} ({}): cancelled differs\n kernel only: {:?}\n rust only: {:?}",
            tz.name(),
            ks.difference(&rs).map(show).collect::<Vec<_>>(),
            rs.difference(&ks).map(show).collect::<Vec<_>>()
        );
    }
    if k.days != r.days {
        let lines: Vec<&str> = text.split('\n').collect();
        let wrong: Vec<String> = k
            .days
            .iter()
            .zip(&r.days)
            .filter(|(a, b)| a != b)
            .take(5)
            .map(|(a, b)| format!("line {}: kernel {} rust {} ({})", a.0, a.1, b.1, lines.get(a.0 as usize - 1).copied().unwrap_or("?")))
            .collect();
        panic!("{name} ({}): days differ ({} vs {} rows)\n {}", tz.name(), k.days.len(), r.days.len(), wrong.join("\n "));
    }
    // C6: the seams, the view rows and the counts.
    if k.seams != r.seams {
        let keys: BTreeSet<_> = k.seams.keys().chain(r.seams.keys()).collect();
        let why: Vec<String> = keys
            .into_iter()
            .filter(|d| k.seams.get(*d) != r.seams.get(*d))
            .take(5)
            .map(|d| format!("seam of day {d}:\n  kernel {:?}\n  rust   {:?}", k.seams.get(d), r.seams.get(d)))
            .collect();
        panic!("{name} ({}): the seams differ\n{}", tz.name(), why.join("\n"));
    }
    if k.rows != r.rows {
        let wrong: Vec<String> = k.rows.iter().zip(&r.rows).filter(|(a, b)| a != b).take(5).map(|(a, b)| format!("kernel {a:?}\n  rust   {b:?}")).collect();
        panic!("{name} ({}): the view rows differ ({} vs {} rows)\n  {}", tz.name(), k.rows.len(), r.rows.len(), wrong.join("\n  "));
    }
    assert_eq!(k.counts, r.counts, "{name}: entry count, line count, last day");
    assert_eq!(k.completion.done_first, r.completion.done_first, "{name}: first done dates and counts");
    assert_eq!(k, r, "{name}");
    // C6: the whole `Replay`, through the fork's own `PartialEq` (every field placed on one side or the other by
    // its destructuring) and `ported_facts()` (D14: every field nothing reads).
    let rr = replay::replay_of_text(text, tz);
    let kr = kernel_replay(&k, tz, &rr);
    assert!(kr == rr, "{name} ({}): the kernel's Replay is not the fork's", tz.name());
    assert_eq!(kr.ported_facts(), rr.ported_facts(), "{name}: the ported facts (D14)");
    k
}

/// C3: how much of the block family a run compared, summed over its logs.
#[derive(Default)]
struct Tally {
    days: usize,
    items: usize,
    item_days: usize,
    segments: usize,
    ci_unknown: usize,
    energy: usize,
    durations: usize,
    interrupts: usize,
    open_blocks: usize,
    open_interrupts: usize,
    /// C4.
    done_items: usize,
    done_dates: usize,
    instances: usize,
    named: usize,
    replay_warnings: usize,
    /// C4: instances whose last record in file order is stamped before an earlier-logged
    /// record of the same instance (quirk Q6(b) showing; [`q6b_separations`]).
    retro_instances: usize,
    /// C4: `(name, id?)` keys whose latest by instant is not their latest by date (carried note 3 showing).
    clock_back_keys: usize,
    /// C5.
    wakes: usize,
    arrivals: usize,
    loc_changes: usize,
    idle: usize,
    breaks: usize,
    routine_days: usize,
    plan_days: usize,
    demotions: usize,
    demotion_stamps: usize,
    closes: usize,
    dropped: usize,
    longest_leaks: usize,
    unknown: u64,
    energy_events: usize,
    /// C5: energy observations whose sleep is a wake logged after them (late binding showing; [`day_separations`]).
    late_sleeps: usize,
    /// C5: idle records on a day other than their own entry's (a gap on the day it began; [`day_separations`]).
    early_gaps: usize,
    /// C6: seams, the days whose since-break anchor is a break's end (not a start), the idle marks by kind
    /// (pause, interrupt, unpause, resume, break), the view rows and the cancelled ones.
    seams: usize,
    break_anchors: usize,
    marks: [usize; 5],
    rows: usize,
    cancelled_rows: usize,
}

impl Tally {
    /// C6.
    fn add_view(&mut self, f: &Facts) {
        self.seams += f.seams.len();
        for s in f.seams.values() {
            for (kind, _, _) in &s.1 {
                let i = ["pause", "interrupt", "unpause", "resume", "break"].iter().position(|k| k == kind).expect("a mark kind");
                self.marks[i] += 1;
            }
            // The anchor is a break's end when it is the last break mark's `t + actual_min`.
            if let (Some(anchor), Some((_, t, actual))) = (s.0, s.1.iter().rev().find(|m| m.0 == "break")) {
                self.break_anchors += usize::from(date_time(&anchor) == date_time(t) + Duration::minutes(actual.unwrap_or(0) as i64));
            }
        }
        self.rows += f.rows.len();
        self.cancelled_rows += f.rows.iter().filter(|r| r.4).count();
    }
    fn add_completion(&mut self, c: &Completion) {
        self.done_items += c.last_done.len();
        self.done_dates += c.done_dates.values().map(BTreeSet::len).sum::<usize>();
        self.instances += c.instances.len();
        self.named += c.named.len();
        self.replay_warnings += c.warnings.len();
        self.clock_back_keys += c.named.values().filter(|k| k.0 != k.2).count();
    }
    fn add_day(&mut self, d: &DayFam, b: &Block) {
        self.wakes += d.days.values().filter(|x| x.wake.is_some()).count();
        self.arrivals += d.days.values().filter(|x| x.arrival.is_some()).count();
        self.loc_changes += d.days.values().map(|x| x.loc_changes.len()).sum::<usize>();
        self.idle += d.days.values().map(|x| x.idle.len()).sum::<usize>();
        self.breaks += d.days.values().map(|x| x.breaks.len()).sum::<usize>();
        self.routine_days += d.days.values().filter(|x| x.routine_min > 0).count();
        self.plan_days += d.days.values().filter(|x| x.plans > 0).count();
        self.demotions += d.demotions.len();
        self.demotion_stamps += d.demotions.iter().filter(|x| x.6.is_some()).count();
        self.closes += d.closes.len();
        self.dropped += d.dropped.len();
        self.longest_leaks += usize::from(d.longest_leak.is_some());
        self.unknown += d.unknown;
        self.energy_events += b.energy.iter().filter(|o| !o.10).count();
    }
    fn add(&mut self, b: &Block) {
        self.days += b.days.len();
        self.items += b.items.len();
        self.item_days += b.items.values().map(|i| i.by_day.len()).sum::<usize>();
        self.segments += b.days.values().map(|d| d.segments.len()).sum::<usize>();
        self.ci_unknown += b.days.values().map(|d| d.ci_unknown.len()).sum::<usize>();
        self.energy += b.energy.len();
        self.durations += b.durations.len();
        self.interrupts += b.interrupts.len();
        self.open_blocks += usize::from(b.open_block.is_some());
        self.open_interrupts += usize::from(b.open_interrupt.is_some());
    }
}

impl std::fmt::Display for Tally {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "block family: {} days ({} segments, {} ci-unknown pairs), {} items ({} item days), {} energy observations, {} durations, {} interruptions, {} open blocks, {} open interruptions; \
             completion family: {} done items ({} done dates), {} instances ({} whose last record in file order is not their latest by instant), {} named keys ({} whose latest by instant is not their latest by date), {} replay warnings; \
             day family: {} wakes, {} arrivals, {} location changes, {} idle records ({} on a day before their own entry's), {} breaks, {} days with routine minutes, {} days with plans, {} demotions ({} stamped), {} closes, {} dropped ids, {} longest leaks, {} unknown events, {} energy-event observations ({} reading a wake logged after them); \
             view: {} seams ({} anchored at a break's end), idle marks pause/interrupt/unpause/resume/break {:?}, {} rows ({} cancelled)",
            self.days, self.segments, self.ci_unknown, self.items, self.item_days, self.energy, self.durations, self.interrupts, self.open_blocks, self.open_interrupts,
            self.done_items, self.done_dates, self.instances, self.retro_instances, self.named, self.clock_back_keys, self.replay_warnings,
            self.wakes, self.arrivals, self.loc_changes, self.idle, self.early_gaps, self.breaks, self.routine_days, self.plan_days, self.demotions, self.demotion_stamps,
            self.closes, self.dropped, self.longest_leaks, self.unknown, self.energy_events, self.late_sleeps,
            self.seams, self.break_anchors, self.marks, self.rows, self.cancelled_rows
        )
    }
}

/// **C5's separations in a log**, from the Rust reader: `(late_sleeps, early_gaps)`,
/// the energy observations whose day's first logged wake is on a later line (late
/// binding), and the idle records dated on a day other than their entry's (a gap on the
/// day it began).
fn day_separations(text: &str, tz: Tz) -> (usize, usize) {
    let r = replay::replay_of_text(text, tz);
    let survivors: Vec<_> = r.view().iter().filter(|row| !row.cancelled).collect();
    let mut late = 0;
    let mut early = 0;
    for row in &survivors {
        match &row.entry.ev {
            Event::Energy { .. } => {
                let wake = survivors.iter().find(|w| matches!(w.entry.ev, Event::Wake { .. }) && w.day == row.day);
                late += usize::from(wake.is_some_and(|w| w.line > row.line));
            }
            Event::Idle { .. } => {
                let rec = r.days.values().flat_map(|d| d.idle.iter()).find(|i| stamp_of(&i.t) == stamp_of(&row.entry.t));
                early += usize::from(rec.is_some_and(|i| i.day != row.day));
            }
            _ => {}
        }
    }
    (late, early)
}

/// **Quirk Q6(b) in a log**: how many instances' last surviving record in file
/// order is stamped strictly before another surviving record of the same instance,
/// so the instance (last in file order) and the latest by instant differ.
fn q6b_separations(text: &str, tz: Tz) -> usize {
    let r = replay::replay_of_text(text, tz);
    let mut by_inst: BTreeMap<(String, String), Vec<(i64, u32)>> = BTreeMap::new();
    for row in r.view().iter().filter(|row| !row.cancelled) {
        let key = match &row.entry.ev {
            Event::Routine { item, inst, .. } | Event::Skip { item, inst } => (item.clone(), inst.clone()),
            _ => continue,
        };
        by_inst.entry(key).or_default().push(instant_of(&stamp_of(&row.entry.t)));
    }
    by_inst.values().filter(|ts| ts.last().is_some_and(|last| ts.iter().any(|t| t > last))).count()
}

/// How many entries of `text` the day index puts on a date other than their own
/// local date in `tz`: what shows the index, not the calendar, was compared.
fn off_their_own_date(text: &str, tz: Tz) -> usize {
    replay::replay_of_text(text, tz)
        .view()
        .iter()
        .filter(|row| row.day != row.entry.t.with_timezone(&tz).date_naive())
        .count()
}

/// The kernel's day of physical line `line`.
fn day_of_line(k: &Facts, line: u64) -> i64 {
    k.days.iter().find(|(l, _)| *l == line).map(|(_, d)| *d).expect("the line has a day")
}

// ---------------------------------------------------------------------------
// Writing lines.

/// The writer: entries in file order, each stamped in the writer's zone (the
/// `Local` of the machine that appended it).
struct Writer {
    writer: Tz,
    lines: Vec<String>,
}

impl Writer {
    fn new(writer: Tz) -> Writer {
        Writer { writer, lines: Vec::new() }
    }
    fn stamp(&self, t: DateTime<Utc>) -> DateTime<FixedOffset> {
        t.with_timezone(&self.writer).fixed_offset()
    }
    /// Append `ev` at `t` with the Rust writer; returns its physical line.
    fn push(&mut self, t: DateTime<Utc>, ev: Event) -> u64 {
        let stamp = self.stamp(t);
        self.push_at(stamp, ev)
    }
    /// Append `ev` at a written stamp (a chosen offset).
    fn push_at(&mut self, stamp: DateTime<FixedOffset>, ev: Event) -> u64 {
        self.lines.push(LogEntry::new(stamp, ev).to_json().expect("serde writes it"));
        self.lines.len() as u64
    }
    /// Append a raw line (an unknown tag, or a stamp the writer cannot spell).
    fn push_raw(&mut self, line: String) -> u64 {
        self.lines.push(line);
        self.lines.len() as u64
    }
    fn text(&self) -> String {
        loggen::text(&self.lines)
    }
}

fn ev_start(id: &str) -> Event {
    Event::Start {
        id: id.into(),
        pred: 3,
        rep: Some(3),
        hsw: 2.5,
        slept_min: 420,
        loc: "lounge".into(),
        blocks_done: 0,
        since_break_min: 0,
    }
}
fn ev_done(id: &str, actual_min: u32, partial: bool) -> Event {
    Event::Done { id: id.into(), est_min: 50, actual_min, went: Some(1), tags: vec![], ci: 3, partial }
}
/// A `done` with every field chosen (C3's edge arms).
fn ev_done_at(id: &str, actual_min: u32, partial: bool, ci: u8, went: Option<u8>) -> Event {
    Event::Done { id: id.into(), est_min: 30, actual_min, went, tags: vec!["t".into()], ci, partial }
}
fn ev_undo(of: &str, id: Option<&str>) -> Event {
    Event::Undo { of: of.into(), id: id.map(str::to_string) }
}
fn ev_wake(slept_min: u32) -> Event {
    Event::Wake { slept_min, onset_min: None }
}
fn ev_close(period: &str, key: &str) -> Event {
    Event::Close { period: period.into(), key: key.into() }
}

// ---------------------------------------------------------------------------
// The generated sequences.

/// splitmix64: a seeded, dependency-free stream.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len() as u64) as usize]
    }
}

/// The arms a generated sequence mixes (design §14.4's list, one variant each).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Arm {
    /// A wake at the clock.
    Wake,
    /// A wake written after later entries, dated before them.
    OutOfOrderWake,
    /// start, pauses, done or stop.
    Block,
    /// start, `extend`, done.
    Extend,
    /// start, stop, then a partial `done` (CRIT 22).
    PartialDoneAfterStop,
    /// A `break` and an `idle` dated before the last entry.
    RetroBreakIdle,
    /// `tm undo` of the last command: its events' undos, most recent first, with ids.
    UndoLastCommand,
    /// A command, an automatic `close` (housekeeping), then the command's undo
    /// (quirk Q6(f) when the command is a `close`).
    HousekeepingBetween,
    /// `tm undo` of a verb that logged nothing, named like an event: `undo{of:"move"}`
    /// cancels an older `move` (quirk Q6(d)).
    SilentVerbUndo,
    /// `undo{of:"rank"}`: a silent verb no event is named like; dangles.
    SilentVerbUndoDangling,
    /// `undo{of:"undo"}`: no redo.
    UndoOfUndo,
    /// An undo whose id nothing carries.
    UndoOfAbsentId,
    /// `undo{of:"note"}` and `undo{of:"plan"}`: not state changes, still masked.
    UndoOfNonStateChange,
    /// An unknown tag and its undo.
    UnknownAndUndo,
    /// A `:60` stamp inside a block (CRIT 29).
    LeapInsideBlock,
    /// Everything else a day holds: plan, note, energy, event, routine, skip,
    /// interrupt and resume, drop, edit, demote, loc, arrive, move, readopt.
    Misc,
    /// C3: the block machine's edges, one of fourteen cases a time (a retro
    /// `done`, a `done` or `stop` for another id, a start or pause inside an
    /// interruption, a `done` while paused, a pause split by an interruption,
    /// two interrupts and two resumes, a stray `unpause`, a start without `rep`
    /// and a `done` at ci 7, zero-length and backwards stretches, a block across
    /// midnight, two 90-second sub-segments (site R8), and a `stop` then a
    /// 0-minute `done` then a real one).
    BlockEdges,
    /// C4: the completion family's edges, one of ten cases a time (a retro
    /// routine `done` of one instance, unknown statuses, a `pending` after a `done`,
    /// a `skip` after a `done`, instances that are not dates to `parse_date`, a retro
    /// and an equal-instant `done`, every known status with minutes, events with
    /// and without an id at retro and equal instants, an undone routine, and a
    /// partial `done` beside a completion).
    Completions,
    /// C4: `event`s and a routine `done` across the zone's clock going back over
    /// midnight (St John's before 2011; in a zone with no such transition, its
    /// fall-back), so the latest by instant is not the latest by date (carried
    /// note 3).
    ClockBack,
    /// C5: the day family's edges, one of ten cases a time (late-bound sleep and
    /// out-of-order wakes of one day, arrivals and locations, plans, idle gaps
    /// with equal leaks and a gap begun on an earlier day, breaks and `:60`
    /// stamps, routine minutes, demote keys, drops, closes and unknown events,
    /// an energy line on a day nothing else touches, and a block after midnight).
    DayRecords,
}

const ARMS: [Arm; 20] = [
    Arm::Wake,
    Arm::OutOfOrderWake,
    Arm::Block,
    Arm::Extend,
    Arm::PartialDoneAfterStop,
    Arm::RetroBreakIdle,
    Arm::UndoLastCommand,
    Arm::HousekeepingBetween,
    Arm::SilentVerbUndo,
    Arm::SilentVerbUndoDangling,
    Arm::UndoOfUndo,
    Arm::UndoOfAbsentId,
    Arm::UndoOfNonStateChange,
    Arm::UnknownAndUndo,
    Arm::LeapInsideBlock,
    Arm::Misc,
    Arm::BlockEdges,
    Arm::Completions,
    Arm::ClockBack,
    Arm::DayRecords,
];

/// One generated log and what the Rust must have cancelled because of the arms
/// that name a target (checked against both readers).
struct Generated {
    tz: Tz,
    text: String,
    arms: Vec<Arm>,
    /// Lines a silent-verb undo must cancel (the older event of its tag).
    silent_targets: Vec<u64>,
    /// Quirk Q6(f): `(week close, automatic close)` lines; the undo of the week
    /// close cancels the automatic one and leaves the week's standing.
    housekeeping: Vec<(u64, u64)>,
    /// C3: the [`block_edge`] cases this sequence ran.
    edges: Vec<u64>,
    /// C4: the [`completion_edge`] cases this sequence ran.
    completions: Vec<u64>,
    /// C5: the [`day_edge`] cases this sequence ran.
    day_edges: Vec<u64>,
    /// C7: the clock after the last entry, where a triple's command starts.
    now: DateTime<Utc>,
}

/// Move the clock on by 1 to 90 minutes and return it.
fn tick(now: &mut DateTime<Utc>, rng: &mut Rng) -> DateTime<Utc> {
    *now += Duration::minutes(1 + rng.below(90) as i64);
    *now
}

/// The zones sequences are written in and read in.
const SEQ_ZONES: [Tz; 5] =
    [chrono_tz::America::Chicago, chrono_tz::Europe::Berlin, chrono_tz::Asia::Kolkata, chrono_tz::America::St_Johns, chrono_tz::UTC];

fn generate(seed: u64) -> Generated {
    let mut rng = Rng(seed.wrapping_mul(0x2545_f491_4f6c_dd1d) ^ 0x5d9);
    let tz = *rng.pick(&SEQ_ZONES);
    // One sequence in four is written by a machine in another zone (§6.4's last case).
    let writer = if rng.below(4) == 0 { *rng.pick(&SEQ_ZONES) } else { tz };
    let mut w = Writer::new(writer);
    let ids = ["1", "2", "3", "17", "a1"];
    // Start somewhere in 2026, near a transition one time in four.
    let starts = [
        Utc.with_ymd_and_hms(2026, 3, 7, 10, 0, 0),
        Utc.with_ymd_and_hms(2026, 10, 31, 10, 0, 0),
        Utc.with_ymd_and_hms(2026, 6, 15, 11, 0, 0),
        Utc.with_ymd_and_hms(2026, 1, 20, 12, 0, 0),
    ];
    let mut now = rng.pick(&starts).single().expect("a UTC instant") + Duration::minutes(rng.below(600) as i64);
    let mut arms = Vec::new();
    let mut silent_targets = Vec::new();
    let mut housekeeping = Vec::new();
    let mut edges = Vec::new();
    let mut completions = Vec::new();
    let mut day_edges = Vec::new();
    // Events that a silent-verb undo can target: (tag, line) of the latest move/readopt.
    let mut last_move: Option<u64> = None;
    w.push(now, ev_wake(420));
    let steps = 6 + rng.below(18);
    // Every arm is forced once across the run: sequence `seed` starts with arm `seed % 16`.
    let mut forced = Some(ARMS[(seed % ARMS.len() as u64) as usize]);
    for _ in 0..steps {
        let arm = forced.take().unwrap_or_else(|| *rng.pick(&ARMS));
        arms.push(arm);
        let id = *rng.pick(&ids);
        match arm {
            Arm::Wake => {
                let t = tick(&mut now, &mut rng) + Duration::hours(6);
                now = t;
                w.push(t, ev_wake(300 + rng.below(200) as u32));
            }
            Arm::OutOfOrderWake => {
                let t = now - Duration::minutes(30 + rng.below(900) as i64);
                w.push(t, ev_wake(400));
            }
            Arm::Block => {
                w.push(tick(&mut now, &mut rng), ev_start(id));
                for _ in 0..rng.below(3) {
                    w.push(tick(&mut now, &mut rng), Event::Pause { id: id.into() });
                    w.push(tick(&mut now, &mut rng), Event::Unpause { id: id.into() });
                }
                match rng.below(3) {
                    0 => {
                        w.push(tick(&mut now, &mut rng), ev_done(id, 40, false));
                    }
                    1 => {
                        w.push(tick(&mut now, &mut rng), Event::Stop { id: id.into(), remaining_min: 20 });
                    }
                    _ => {}
                }
            }
            Arm::Extend => {
                w.push(tick(&mut now, &mut rng), ev_start(id));
                w.push(tick(&mut now, &mut rng), Event::Extend { id: id.into(), by_min: 15 });
                w.push(tick(&mut now, &mut rng), ev_done(id, 65, false));
            }
            Arm::PartialDoneAfterStop => {
                w.push(tick(&mut now, &mut rng), ev_start(id));
                w.push(tick(&mut now, &mut rng), Event::Stop { id: id.into(), remaining_min: 25 });
                w.push(tick(&mut now, &mut rng), ev_done(id, 30, true));
            }
            Arm::RetroBreakIdle => {
                let t = tick(&mut now, &mut rng);
                w.push(t - Duration::minutes(40), Event::Break { planned_min: 10, actual_min: Some(12), r#where: Some("walk".into()) });
                w.push(t, Event::Idle { attributed: (*rng.pick(&["leak", "work", "break"])).into(), min: 25 });
            }
            Arm::UndoLastCommand => {
                // A `tm done` that logged a done and a routine; undone most recent first.
                w.push(tick(&mut now, &mut rng), ev_done(id, 30, false));
                w.push(tick(&mut now, &mut rng), Event::Routine { item: "stretch".into(), inst: "2026-09-07".into(), status: "done".into(), actual_min: None });
                let t = tick(&mut now, &mut rng);
                w.push(t, ev_undo("routine", Some("stretch")));
                w.push(t, ev_undo("done", Some(id)));
            }
            Arm::HousekeepingBetween => {
                let key = now.with_timezone(&tz).date_naive().to_string();
                if rng.below(2) == 0 {
                    // quirk Q6(f): `tm close week`, the next verb's automatic close, `tm undo`.
                    let week = w.push(tick(&mut now, &mut rng), ev_close("week", "2026-W37"));
                    let auto = w.push(tick(&mut now, &mut rng), ev_close("day", &key));
                    w.push(tick(&mut now, &mut rng), ev_undo("close", None));
                    housekeeping.push((week, auto));
                } else {
                    w.push(tick(&mut now, &mut rng), ev_done(id, 45, false));
                    w.push(tick(&mut now, &mut rng), ev_close("day", &key));
                    w.push(tick(&mut now, &mut rng), ev_undo("done", Some(id)));
                }
            }
            Arm::SilentVerbUndo => {
                let target = match last_move {
                    Some(l) if rng.below(2) == 0 => l,
                    _ => w.push(tick(&mut now, &mut rng), Event::Move { id: id.into(), from: "week/2026-W37.md".into(), to: "backlog.md".into() }),
                };
                // Anything but a move in between: the undo reaches back over it.
                w.push(tick(&mut now, &mut rng), Event::Note { text: "between".into() });
                w.push(tick(&mut now, &mut rng), ev_undo("move", None));
                silent_targets.push(target);
                last_move = None;
            }
            Arm::SilentVerbUndoDangling => {
                w.push(tick(&mut now, &mut rng), ev_undo("rank", None));
            }
            Arm::UndoOfUndo => {
                w.push(tick(&mut now, &mut rng), ev_undo("undo", None));
            }
            Arm::UndoOfAbsentId => {
                w.push(tick(&mut now, &mut rng), ev_undo("done", Some("zz")));
            }
            Arm::UndoOfNonStateChange => {
                w.push(tick(&mut now, &mut rng), Event::Note { text: "n".into() });
                w.push(tick(&mut now, &mut rng), Event::Plan { hash: "h".into(), replans_today: 1, drift_min: 0 });
                w.push(tick(&mut now, &mut rng), ev_undo("note", None));
                w.push(tick(&mut now, &mut rng), ev_undo("plan", None));
            }
            Arm::UnknownAndUndo => {
                let stamp = w.stamp(tick(&mut now, &mut rng));
                w.push_raw(format!(r#"{{"t":"{}","ev":"mood","level":3,"id":"{id}"}}"#, stamp.to_rfc3339()));
                w.push(tick(&mut now, &mut rng), ev_undo("mood", if rng.below(2) == 0 { Some(id) } else { None }));
            }
            Arm::LeapInsideBlock => {
                w.push(tick(&mut now, &mut rng), ev_start(id));
                // 23:59:60 is not a leap second chrono knows; it reads `:60` as the
                // 59th second plus a leap nanosecond on any minute (T3, P23).
                let t = tick(&mut now, &mut rng);
                let stamp = w.stamp(t);
                let spelled = format!("{}:60{}", stamp.format("%Y-%m-%dT%H:%M"), stamp.format("%:z"));
                w.push_raw(format!(r#"{{"t":"{spelled}","ev":"pause","id":"{id}"}}"#));
                w.push(tick(&mut now, &mut rng), Event::Unpause { id: id.into() });
                w.push(tick(&mut now, &mut rng), ev_done(id, 50, false));
            }
            Arm::BlockEdges => {
                for _ in 0..1 + rng.below(3) {
                    let case = rng.below(14);
                    edges.push(case);
                    block_edge(case, &mut w, &mut now, &mut rng, id);
                }
            }
            Arm::Completions => {
                for _ in 0..1 + rng.below(3) {
                    let case = rng.below(COMPLETION_EDGES);
                    completions.push(case);
                    completion_edge(case, &mut w, &mut now, &mut rng, id, tz);
                }
            }
            Arm::ClockBack => clock_back(&mut w, tz, id, &mut rng),
            Arm::DayRecords => {
                for _ in 0..1 + rng.below(3) {
                    let case = rng.below(DAY_EDGES);
                    day_edges.push(case);
                    day_edge(case, &mut w, &mut now, &mut rng, id, tz);
                }
            }
            Arm::Misc => {
                let t = tick(&mut now, &mut rng);
                match rng.below(14) {
                    0 => w.push(t, Event::Plan { hash: "p".into(), replans_today: 2, drift_min: 5 }),
                    1 => w.push(t, Event::Note { text: "note".into() }),
                    2 => w.push(t, Event::Energy { pred: 3, rep: 4, hsw: 3.25, loc: "home".into() }),
                    3 => w.push(t, Event::Named { name: "arrival".into(), id: Some(id.into()) }),
                    4 => w.push(t, Event::Routine { item: "stretch".into(), inst: "#2".into(), status: "pending".into(), actual_min: Some(5) }),
                    5 => w.push(t, Event::Skip { item: "stretch".into(), inst: "2026-09-08".into() }),
                    6 => {
                        w.push(t, Event::Interrupt { id: Some(id.into()) });
                        w.push(t + Duration::minutes(7), Event::Resume { lost_min: 7, dropped: vec![] })
                    }
                    7 => w.push(t, Event::Drop { id: id.into() }),
                    8 => w.push(t, Event::Edit { id: id.into(), field: "est".into(), from: "50".into(), to: "60".into() }),
                    9 => w.push(t, Event::Demote { id: id.into(), from: "2026-W37".into(), to: "2026-W38".into(), est_min: 50 }),
                    10 => w.push(t, Event::Loc { loc: "home".into() }),
                    11 => w.push(t, Event::Arrive { loc: "lounge".into(), window: ["08:00".into(), "16:00".into()], budget: 6 }),
                    12 => {
                        let l = w.push(t, Event::Move { id: id.into(), from: "a.md".into(), to: "b.md".into() });
                        last_move = Some(l);
                        l
                    }
                    _ => w.push(t, Event::Readopt { id: id.into() }),
                };
            }
        }
    }
    Generated { tz, text: w.text(), arms, silent_targets, housekeeping, edges, completions, day_edges, now }
}

/// How many cases [`day_edge`] has.
const DAY_EDGES: u64 = 10;

/// A line stamped `:60` on the minute of `t` in the writer's zone (chrono reads it
/// as the 59th second plus a leap nanosecond, T3 and P23), with the rest of the
/// object after `t`.
fn leap_line(w: &Writer, t: DateTime<Utc>, rest: &str) -> String {
    let stamp = w.stamp(t);
    format!(r#"{{"t":"{}:60{}",{rest}}}"#, stamp.format("%Y-%m-%dT%H:%M"), stamp.format("%:z"))
}

/// One of [`Arm::DayRecords`]' cases, by number.
fn day_edge(case: u64, w: &mut Writer, now: &mut DateTime<Utc>, rng: &mut Rng, id: &str, tz: Tz) {
    match case {
        // Late binding and quirk Q6(a) in the day's fields: an `energy` line, then (appended after
        // it) a wake 40 minutes earlier and one 55 minutes earlier, and another `energy`: both
        // observations read the first wake logged, whose sleep the day keeps too.
        0 => {
            let t = tick(now, rng);
            w.push(t, Event::Energy { pred: 2, rep: 3, hsw: 1.5, loc: "home".into() });
            w.push(t - Duration::minutes(40), Event::Wake { slept_min: 380, onset_min: Some(15) });
            w.push(t - Duration::minutes(55), Event::Wake { slept_min: 300, onset_min: None });
            w.push(tick(now, rng), Event::Energy { pred: 4, rep: 4, hsw: 0.0, loc: "lounge".into() });
        }
        // Arrivals and locations: the first arrival sets the window and budget, every one moves.
        1 => {
            w.push(tick(now, rng), Event::Arrive { loc: "lounge".into(), window: ["08:00".into(), "16:00".into()], budget: 6 });
            w.push(tick(now, rng), Event::Loc { loc: "home".into() });
            w.push(tick(now, rng), Event::Arrive { loc: "office".into(), window: ["09:00".into(), "17:30".into()], budget: 4 });
        }
        // Plans: replans that fall and rise, drift, the last hash.
        2 => {
            for (hash, replans, drift) in [("h1", 3, 5), ("h2", 1, 0), ("h3", 4, 2)] {
                w.push(tick(now, rng), Event::Plan { hash: hash.into(), replans_today: replans, drift_min: drift });
            }
        }
        // Idle gaps: two equal leaks (the first maximum stays), another attribution, and a leak of 20
        // hours, which began on an earlier day.
        3 => {
            let t = tick(now, rng);
            w.push(t, Event::Idle { attributed: "leak".into(), min: 25 });
            w.push(t + Duration::minutes(30), Event::Idle { attributed: "leak".into(), min: 25 });
            w.push(t + Duration::minutes(35), Event::Idle { attributed: (*rng.pick(&["work", "break", "routine", "interrupt", ""])).into(), min: 10 });
            w.push(t + Duration::minutes(40), Event::Idle { attributed: "leak".into(), min: 20 * 60 });
            *now = t + Duration::minutes(40);
        }
        // Breaks planned only, with an actual and a place, and `:60` stamps on a break, a gap and a
        // routine's minutes (a leap second before adding or subtracting minutes).
        4 => {
            w.push(tick(now, rng), Event::Break { planned_min: 10, actual_min: None, r#where: None });
            w.push(tick(now, rng), Event::Break { planned_min: 15, actual_min: Some(0), r#where: Some("walk".into()) });
            for rest in [
                r#""ev":"break","planned_min":5"#,
                r#""ev":"idle","attributed":"leak","min":7"#,
                r##""ev":"routine","item":"stretch","inst":"#6","status":"done","actual_min":3"##,
            ] {
                let t = tick(now, rng);
                let line = leap_line(w, t, rest);
                w.push_raw(line);
            }
        }
        // Routine minutes: a `done` whose minutes began long before (another day), a `done` without
        // minutes, and a `pending` and an unknown status with minutes (no segment, no minutes).
        5 => {
            w.push(tick(now, rng), Event::Routine { item: "stretch".into(), inst: "#4".into(), status: "done".into(), actual_min: Some(600 + rng.below(900) as u32) });
            w.push(tick(now, rng), Event::Routine { item: "stretch".into(), inst: now.with_timezone(&tz).date_naive().to_string(), status: "done".into(), actual_min: None });
            w.push(tick(now, rng), Event::Routine { item: "water".into(), inst: "#1".into(), status: "pending".into(), actual_min: Some(5) });
            w.push(tick(now, rng), Event::Routine { item: "water".into(), inst: "#2".into(), status: "Done".into(), actual_min: Some(5) });
        }
        // Demote keys: a week, a date, a month, a week 2027 does not have, one 2026 has, signed years
        // before the origin and past 9999, a padded date and year 0's 29 February; and a routine done
        // on a signed year past 9999.
        6 => {
            for from in ["2026-W37", "2026-09-07", "2026-09", "2027-W53", "2026-W53", "-001-09-07", "+10000-1-7", " 2026-9-07", "0000-02-29", "-001-02-29"] {
                w.push(tick(now, rng), Event::Demote { id: id.into(), from: from.into(), to: "backlog.md".into(), est_min: 30 });
            }
            w.push(tick(now, rng), Event::Routine { item: "stretch".into(), inst: "+10000-1-7".into(), status: "done".into(), actual_min: None });
        }
        // Drops, closes and unknown events, and undos of a close and of an unknown tag.
        7 => {
            w.push(tick(now, rng), Event::Drop { id: id.into() });
            w.push(tick(now, rng), ev_close("week", "2026-W37"));
            w.push(tick(now, rng), ev_close("day", &now.with_timezone(&tz).date_naive().to_string()));
            let t = tick(now, rng);
            let stamp = w.stamp(t);
            w.push_raw(format!(r#"{{"t":"{}","ev":"mood","level":2}}"#, stamp.to_rfc3339()));
            let t = tick(now, rng);
            let stamp = w.stamp(t);
            w.push_raw(format!(r#"{{"t":"{}","ev":"weather","id":"{id}","sky":"grey"}}"#, stamp.to_rfc3339()));
            if rng.below(2) == 0 {
                w.push(tick(now, rng), ev_undo("close", None));
            }
            if rng.below(2) == 0 {
                w.push(tick(now, rng), ev_undo("mood", None));
            }
        }
        // An `energy` line on a date three days ahead that nothing else touches: an observation and no day.
        8 => {
            w.push(*now + Duration::days(3), Event::Energy { pred: 1, rep: 2, hsw: 9.0, loc: "home".into() });
        }
        // Quirk Q6(g): a block after midnight in the read zone, before the next wake.
        _ => {
            let local = now.with_timezone(&tz);
            let to_midnight = 24 * 60 - i64::from(local.hour() * 60 + local.minute());
            *now += Duration::minutes(to_midnight + 10);
            w.push(*now, ev_start(id));
            *now += Duration::minutes(30);
            w.push(*now, ev_done_at(id, 30, false, 2, None));
        }
    }
}

/// How many cases [`completion_edge`] has.
const COMPLETION_EDGES: u64 = 10;

fn ev_routine(item: &str, inst: &str, status: &str, actual_min: Option<u32>) -> Event {
    Event::Routine { item: item.into(), inst: inst.into(), status: status.into(), actual_min }
}

/// One of [`Arm::Completions`]' cases, by number.
fn completion_edge(case: u64, w: &mut Writer, now: &mut DateTime<Utc>, rng: &mut Rng, id: &str, tz: Tz) {
    let item = *rng.pick(&["stretch", "water", id]);
    let today = now.with_timezone(&tz).date_naive();
    let date_inst = (today - Duration::days(rng.below(3) as i64)).to_string();
    match case {
        // Quirk Q6(b): a routine `done`, then the same instance `done` again, stamped earlier (a
        // retro append): the instance is the later line, `last_done` the later instant.
        0 => {
            let t = tick(now, rng);
            w.push(t, ev_routine(item, &date_inst, "done", Some(10)));
            w.push(t - Duration::minutes(30 + rng.below(120) as i64), ev_routine(item, &date_inst, "done", None));
        }
        // Statuses the fork does not read: a warning each, read as `Pending`.
        1 => {
            let status = *rng.pick(&["maybe", "Done", "", "skip ", "\"quoted\"\\", "é"]);
            w.push(tick(now, rng), ev_routine(item, "#1", status, if rng.below(2) == 0 { Some(5) } else { None }));
        }
        // A `pending` after a `done`: the instance reads pending, the done date stays.
        2 => {
            w.push(tick(now, rng), ev_routine(item, &date_inst, "done", None));
            w.push(tick(now, rng), ev_routine(item, &date_inst, "pending", None));
        }
        // A `skip` after a `done`.
        3 => {
            w.push(tick(now, rng), ev_routine(item, &date_inst, "done", Some(3)));
            w.push(tick(now, rng), Event::Skip { item: item.into(), inst: date_inst.clone() });
        }
        // Instances `parse_date` does or does not read: an ordinal, a padded date, a date with a
        // no-break space (10 characters, 11 bytes), and a single-digit month.
        4 => {
            let inst = *rng.pick(&["#3", " 2026-9-01", "2026-9-\u{a0}01", "2026-9-01", "2026-09-31", "W37"]);
            w.push(tick(now, rng), ev_routine(item, inst, "done", None));
        }
        // A retro `done` and two `done`s at one instant written at two offsets: `last_done` is the
        // latest instant, the first line of equal instants.
        5 => {
            let t = tick(now, rng);
            w.push(t, ev_done_at(id, 0, false, 2, None));
            w.push(t - Duration::minutes(45), ev_done_at(id, 0, false, 2, None));
            let later = t + Duration::minutes(5);
            w.push_at(later.with_timezone(&east(3600)), ev_done_at(id, 0, false, 2, None));
            w.push_at(later.with_timezone(&east(-7200)), ev_done_at(id, 0, false, 2, None));
            *now = later;
        }
        // Every known status, with minutes.
        6 => {
            for status in ["done", "pending", "missed", "expired", "skipped", "skip"] {
                w.push(tick(now, rng), ev_routine(item, &format!("#{}", rng.below(4)), status, Some(1 + rng.below(20) as u32)));
            }
        }
        // `event`s with and without an id, one retro and two at one instant at two offsets: a later
        // line wins a tie.
        7 => {
            let name = *rng.pick(&["arrival", "parcel"]);
            let t = tick(now, rng);
            w.push(t, Event::Named { name: name.into(), id: Some(id.into()) });
            w.push(t - Duration::minutes(90), Event::Named { name: name.into(), id: None });
            let later = t + Duration::minutes(3);
            w.push_at(later.with_timezone(&east(-3600)), Event::Named { name: name.into(), id: None });
            w.push_at(later.with_timezone(&east(5400)), Event::Named { name: name.into(), id: Some(id.into()) });
            *now = later;
        }
        // An undone routine `done`: its completion, instance and warning never happened.
        8 => {
            w.push(tick(now, rng), ev_routine(item, &date_inst, "done", None));
            w.push(tick(now, rng), ev_undo("routine", Some(item)));
        }
        // A partial `done` beside a completion: only the completion marks done.
        _ => {
            w.push(tick(now, rng), ev_done_at(id, 20, true, 3, None));
            if rng.below(2) == 0 {
                w.push(tick(now, rng), ev_done_at(id, 15, false, 3, None));
            }
        }
    }
}

/// The instant the zone's local date goes backwards, else its last fall-back
/// transition, else none; probed once per zone per test binary (the hourly
/// probe is the slow part).
fn clock_back_instant(tz: Tz) -> Option<DateTime<Utc>> {
    static FOUND: OnceLock<Mutex<HashMap<String, Option<DateTime<Utc>>>>> = OnceLock::new();
    let found = FOUND.get_or_init(|| Mutex::new(HashMap::new()));
    *found.lock().expect("the clock-back cache").entry(tz.name().to_string()).or_insert_with(|| probe_clock_back_instant(tz))
}

fn probe_clock_back_instant(tz: Tz) -> Option<DateTime<Utc>> {
    if let Some((at, _, _)) = backwards_date_transition(tz) {
        return DateTime::from_timestamp(at, 0);
    }
    let t = tz_table::probe(tz);
    let mut prev = t.base;
    let mut last = None;
    for &(at, off) in &t.transitions {
        if off < prev && (2000..2100).contains(&DateTime::from_timestamp(at, 0)?.year()) {
            last = DateTime::from_timestamp(at, 0);
        }
        prev = off;
    }
    last
}

/// [`Arm::ClockBack`]: an event a minute before the zone's clock goes back and
/// one half an hour after, a later instant on an earlier local date where the
/// zone has such a transition, and a routine `done` beside them.
fn clock_back(w: &mut Writer, tz: Tz, id: &str, rng: &mut Rng) {
    let Some(at) = clock_back_instant(tz) else {
        return;
    };
    let name = *rng.pick(&["arrival", "parcel"]);
    let addressed = if rng.below(2) == 0 { Some(id.to_string()) } else { None };
    w.push(at - Duration::seconds(30), Event::Named { name: name.into(), id: addressed.clone() });
    w.push(at + Duration::minutes(29), Event::Named { name: name.into(), id: addressed });
    w.push(at + Duration::minutes(31), ev_routine("stretch", "#9", "done", None));
}

/// One of [`Arm::BlockEdges`]' fourteen cases, by number.
fn block_edge(case: u64, w: &mut Writer, now: &mut DateTime<Utc>, rng: &mut Rng, id: &str) {
    let other = if id == "2" { "3" } else { "2" };
    let went = if rng.below(2) == 0 { Some(3) } else { None };
    match case {
        // A retro `done` with no minutes and no block, then one with a block of another id open.
        0 => {
            w.push(tick(now, rng), ev_done_at(id, 0, false, 2, None));
            w.push(tick(now, rng), ev_start(other));
            w.push(tick(now, rng), ev_done_at(id, 0, rng.below(2) == 0, 4, went));
        }
        // A `done` for another id while a block is open leaves it open.
        1 => {
            w.push(tick(now, rng), ev_start(id));
            w.push(tick(now, rng), ev_done_at(other, 25, false, 3, went));
            if rng.below(2) == 0 {
                w.push(tick(now, rng), Event::Stop { id: id.into(), remaining_min: 5 });
            }
        }
        // A `stop` for another id is ignored.
        2 => {
            w.push(tick(now, rng), ev_start(id));
            w.push(tick(now, rng), Event::Stop { id: other.into(), remaining_min: 5 });
            w.push(tick(now, rng), ev_done_at(id, 30, false, 5, went));
        }
        // A start inside an interruption runs from the resume.
        3 => {
            w.push(tick(now, rng), Event::Interrupt { id: None });
            w.push(tick(now, rng), ev_start(id));
            w.push(tick(now, rng), Event::Resume { lost_min: 4, dropped: vec![other.into()] });
            w.push(tick(now, rng), ev_done_at(id, 20, false, 1, went));
        }
        // A pause inside an interruption, then resume and unpause.
        4 => {
            w.push(tick(now, rng), ev_start(id));
            w.push(tick(now, rng), Event::Interrupt { id: Some(id.into()) });
            w.push(tick(now, rng), Event::Pause { id: id.into() });
            w.push(tick(now, rng), Event::Resume { lost_min: 0, dropped: vec![] });
            w.push(tick(now, rng), Event::Unpause { id: id.into() });
            w.push(tick(now, rng), Event::Stop { id: id.into(), remaining_min: 0 });
        }
        // A `done` while paused (partial or not).
        5 => {
            w.push(tick(now, rng), ev_start(id));
            w.push(tick(now, rng), Event::Pause { id: id.into() });
            w.push(tick(now, rng), ev_done_at(id, 40, rng.below(2) == 0, 3, went));
        }
        // An interruption splits a pause; `resume` restarts it where it left off.
        6 => {
            w.push(tick(now, rng), ev_start(id));
            w.push(tick(now, rng), Event::Pause { id: id.into() });
            w.push(tick(now, rng), Event::Interrupt { id: None });
            w.push(tick(now, rng), Event::Resume { lost_min: 2, dropped: vec![] });
            w.push(tick(now, rng), Event::Unpause { id: id.into() });
            w.push(tick(now, rng), ev_done_at(id, 35, false, 4, went));
        }
        // Two interrupts and two resumes: the second interrupt is ignored, the second resume has no start.
        7 => {
            w.push(tick(now, rng), Event::Interrupt { id: Some(other.into()) });
            w.push(tick(now, rng), Event::Interrupt { id: Some(id.into()) });
            w.push(tick(now, rng), Event::Resume { lost_min: 6, dropped: vec![id.into()] });
            w.push(tick(now, rng), Event::Resume { lost_min: 1, dropped: vec![] });
            // Sometimes one more, which a later arm may or may not resume (an open interruption).
            if rng.below(2) == 0 {
                w.push(tick(now, rng), Event::Interrupt { id: None });
            }
        }
        // A stray `unpause` does not reset the clock.
        8 => {
            w.push(tick(now, rng), ev_start(id));
            w.push(tick(now, rng), Event::Unpause { id: id.into() });
            w.push(tick(now, rng), ev_done_at(id, 15, false, 2, went));
        }
        // A start without `rep` (no observation) and a `done` at ci 7 (clamped to 5) without `went`.
        9 => {
            w.push(
                tick(now, rng),
                Event::Start { id: id.into(), pred: 2, rep: None, hsw: -0.5, slept_min: 0, loc: "home".into(), blocks_done: 3, since_break_min: 9 },
            );
            w.push(tick(now, rng), ev_done_at(id, 45, false, 7, None));
        }
        // Zero-length and backwards stretches: a pause and an unpause at the start's second, and a
        // `done` stamped before it.
        10 => {
            let t = tick(now, rng);
            w.push(t, ev_start(id));
            w.push(t, Event::Pause { id: id.into() });
            w.push(t, Event::Unpause { id: id.into() });
            w.push(t - Duration::minutes(5), ev_done_at(id, 10, false, 3, went));
        }
        // A block across midnight in the writer's zone: credited to the day of its `done`.
        11 => {
            let local = now.with_timezone(&w.writer);
            let to_midnight = 24 * 60 - i64::from(local.hour() * 60 + local.minute());
            *now += Duration::minutes(to_midnight - 20);
            w.push(*now, ev_start(id));
            *now += Duration::minutes(50 + rng.below(40) as i64);
            w.push(*now, ev_done_at(id, 70, false, 2, went));
        }
        // Site R8 (quirk Q6c): two 90-second sub-segments at second resolution, worth 2 minutes, not 3.
        12 => {
            let t = tick(now, rng) + Duration::seconds(17);
            w.push(t, ev_start(id));
            w.push(t + Duration::seconds(90), Event::Pause { id: id.into() });
            w.push(t + Duration::seconds(120), Event::Unpause { id: id.into() });
            w.push(t + Duration::seconds(210), Event::Stop { id: id.into(), remaining_min: 0 });
            *now = t + Duration::seconds(210);
        }
        // A `stop`, a `done` with no minutes (no replacement, the cut stands), then a real `done`,
        // which replaces the cut.
        _ => {
            w.push(tick(now, rng), ev_start(id));
            w.push(tick(now, rng), Event::Stop { id: id.into(), remaining_min: 10 });
            w.push(tick(now, rng), ev_done_at(id, 0, false, 3, None));
            w.push(tick(now, rng), ev_done_at(id, 50, rng.below(2) == 0, 3, went));
        }
    }
}

// ---------------------------------------------------------------------------
// §6.4's zone cases, each its own arm.

fn utc(y: i32, m: u32, d: u32, h: u32, mi: u32, s: u32) -> DateTime<Utc> {
    Utc.with_ymd_and_hms(y, m, d, h, mi, s).single().expect("a UTC instant")
}

/// An offset east of UTC, in seconds.
fn east(secs: i32) -> FixedOffset {
    FixedOffset::east_opt(secs).expect("under a day")
}

/// **A transition where the local date goes backwards**: the zone's clock falls
/// back across midnight, so an instant just before it reads a later date than
/// the instant at it. Found in the zone's probed table, never assumed.
fn backwards_date_transition(tz: Tz) -> Option<(i64, i32, i32)> {
    let t = tz_table::probe(tz);
    let mut prev = t.base;
    for &(at, off) in &t.transitions {
        let before = DateTime::from_timestamp(at - 1, 0)?.with_timezone(&east(prev)).date_naive();
        let after = DateTime::from_timestamp(at, 0)?.with_timezone(&east(off)).date_naive();
        if after < before && (1970..2100).contains(&before.year_ce().1) {
            return Some((at, prev, off));
        }
        prev = off;
    }
    None
}


/// One of §6.4's zone cases: a log, the zone it is read in, and the days some of
/// its lines must have, worked out by hand from the fork's rule (so the two
/// readers cannot agree on a wrong day unnoticed).
struct ZoneCase {
    name: String,
    text: String,
    tz: Tz,
    expect: Vec<(u64, NaiveDate)>,
    /// C4: `(name, id?)` keys and the lines of their latest occurrence by instant
    /// and by local date, worked out by hand.
    named: Vec<(&'static str, Option<&'static str>, u64, u64)>,
    /// C5: the days of the day family's idle records, in the order the days hold them, worked out by hand.
    gaps: Vec<NaiveDate>,
}

fn date(y: i32, m: u32, d: u32) -> NaiveDate {
    NaiveDate::from_ymd_opt(y, m, d).expect("a date")
}

/// §6.4's zone cases (CRIT 11). Each carries undos, so the C1 mask is exercised
/// on every one; C2's day index is what they are for, and each names the days
/// its interesting lines must have.
fn zone_cases() -> Vec<ZoneCase> {
    let chicago = chrono_tz::America::Chicago;
    let mut out = Vec::new();

    // (1) A 01:30 wake on the fall-back day, the ambiguous hour used twice.
    {
        let mut w = Writer::new(chicago);
        w.push(utc(2026, 10, 31, 11, 0, 0), ev_wake(420));
        w.push(utc(2026, 11, 1, 6, 30, 0), ev_wake(300)); // 01:30 CDT
        w.push(utc(2026, 11, 1, 6, 45, 0), ev_start("1"));
        w.push(utc(2026, 11, 1, 7, 30, 0), ev_done("1", 45, false)); // 01:30 CST
        w.push(utc(2026, 11, 1, 7, 40, 0), ev_undo("done", Some("1")));
        w.push(utc(2026, 11, 1, 7, 50, 0), ev_done("1", 60, false)); // 01:50 CST
        let expect = vec![(1, date(2026, 10, 31)), (2, date(2026, 11, 1)), (4, date(2026, 11, 1)), (6, date(2026, 11, 1))];
        out.push(ZoneCase { name: "fall-back 01:30 twice".to_string(), text: w.text(), tz: chicago, expect, named: vec![], gaps: vec![] });
    }
    // (2) A wake after midnight, under 24 hours after the previous one: once
    //     undone (the day stays the first wake's), once standing (it starts a day).
    for undo_the_wake in [true, false] {
        let mut w = Writer::new(chicago);
        w.push(utc(2026, 9, 7, 11, 0, 0), ev_wake(420)); // 06:00 CDT
        w.push(utc(2026, 9, 8, 5, 30, 0), ev_wake(200)); // 00:30 CDT next day, 18.5 h later
        w.push(utc(2026, 9, 8, 6, 0, 0), ev_start("2"));
        w.push(utc(2026, 9, 8, 6, 50, 0), ev_done("2", 50, false));
        let (label, day) = if undo_the_wake {
            w.push(utc(2026, 9, 8, 7, 0, 0), ev_undo("wake", None));
            ("undone", date(2026, 9, 7))
        } else {
            w.push(utc(2026, 9, 8, 7, 0, 0), ev_undo("done", Some("2")));
            ("standing", date(2026, 9, 8))
        };
        let expect = vec![(2, day), (3, day), (4, day)];
        out.push(ZoneCase { name: format!("wake after midnight under 24h, {label}"), text: w.text(), tz: chicago, expect, named: vec![], gaps: vec![] });
    }
    // (3) Events 23–25 real hours after a wake, across both transitions: before
    //     24 hours the wake's date, from 24 hours the entry's own.
    for (label, wake, own) in [
        ("spring", utc(2026, 3, 7, 14, 0, 0), date(2026, 3, 8)),
        ("fall", utc(2026, 10, 31, 13, 0, 0), date(2026, 11, 1)),
    ] {
        let mut w = Writer::new(chicago);
        w.push(wake, ev_wake(420));
        for (k, mins) in [23 * 60, 23 * 60 + 59, 24 * 60, 24 * 60 + 1, 25 * 60].into_iter().enumerate() {
            w.push(wake + Duration::minutes(mins), Event::Note { text: format!("n{k}") });
        }
        w.push(wake + Duration::minutes(25 * 60 + 5), ev_undo("note", None));
        let woke = wake.with_timezone(&chicago).date_naive();
        let expect = vec![(1, woke), (2, woke), (3, woke), (4, own), (5, own), (6, own)];
        out.push(ZoneCase { name: format!("23-25h after a wake, {label} transition"), text: w.text(), tz: chicago, expect, named: vec![], gaps: vec![] });
    }
    // (4) A fold at midnight where consecutive dedup differs from earliest-per-date:
    //     a wake just after midnight before the fold, one before midnight after it.
    let mut folds = 0;
    for tz in [chrono_tz::America::Havana, chrono_tz::Asia::Beirut, chrono_tz::America::St_Johns] {
        let Some((at, before, after)) = backwards_date_transition(tz) else { continue };
        folds += 1;
        let at = DateTime::from_timestamp(at, 0).expect("in range");
        // A wake the evening before, a wake the second before the fold (old
        // offset, the later date), and a wake at the fold (new offset, the date
        // before): by instant the dates run D-1, D, D-1, so consecutive dedup keeps
        // three wakes and earliest-per-date two.
        let wakes = [at - Duration::hours(3), at - Duration::seconds(1), at];
        let dates: Vec<_> = wakes.iter().map(|t| t.with_timezone(&tz).date_naive()).collect();
        let consecutive = 1 + dates.windows(2).filter(|p| p[0] != p[1]).count();
        let per_date = dates.iter().collect::<BTreeSet<_>>().len();
        assert_ne!(consecutive, per_date, "{}: the fold arm must separate the two dedup rules", tz.name());
        eprintln!("T5 fold arm: {} at {} ({:+} s to {:+} s), dates {dates:?}", tz.name(), at, before, after);
        // Once with the undo taking the third wake (both rules then agree: the start
        // is on the second wake's date), once with it taking the done (the third
        // wake stands, and only consecutive dedup puts the start on its date).
        for undo_the_wake in [true, false] {
            let mut w = Writer::new(tz);
            w.push_at(wakes[0].with_timezone(&east(before)), ev_wake(400));
            w.push_at(wakes[1].with_timezone(&east(before)), ev_wake(10));
            w.push_at(wakes[2].with_timezone(&east(after)), ev_wake(20));
            w.push_at((at + Duration::minutes(30)).with_timezone(&east(after)), ev_start("3"));
            w.push_at((at + Duration::minutes(80)).with_timezone(&east(after)), ev_done("3", 50, false));
            let (label, day) = if undo_the_wake {
                w.push_at((at + Duration::minutes(90)).with_timezone(&east(after)), ev_undo("wake", None));
                ("third wake undone", dates[1])
            } else {
                w.push_at((at + Duration::minutes(90)).with_timezone(&east(after)), ev_undo("done", Some("3")));
                ("third wake standing", dates[2])
            };
            // Line 3, the third wake: its own date while it stands; undone, the
            // second wake's day (a second before it).
            let expect = vec![(2, dates[1]), (3, day), (4, day), (5, day)];
            out.push(ZoneCase { name: format!("fold at midnight, {}, {label}", tz.name()), text: w.text(), tz, expect, named: vec![], gaps: vec![] });
        }
    }
    assert!(folds > 0, "no zone of the fold arm has a backwards-date transition in [1970, 2100)");
    // (5) One day with written offsets -05:00 then +02:00.
    {
        let mut w = Writer::new(chicago);
        let base = utc(2026, 9, 7, 11, 0, 0);
        w.push_at(base.with_timezone(&east(-5 * 3600)), ev_wake(420));
        w.push_at((base + Duration::hours(2)).with_timezone(&east(-5 * 3600)), ev_start("a1"));
        w.push_at((base + Duration::hours(3)).with_timezone(&east(2 * 3600)), ev_done("a1", 60, false));
        w.push_at((base + Duration::hours(4)).with_timezone(&east(2 * 3600)), ev_undo("done", None));
        w.push_at((base + Duration::hours(5)).with_timezone(&east(-5 * 3600)), ev_done("a1", 55, false));
        let expect = (1..=5).map(|l| (l, date(2026, 9, 7))).collect();
        out.push(ZoneCase { name: "offsets -05:00 then +02:00".to_string(), text: w.text(), tz: chicago, expect, named: vec![], gaps: vec![] });
    }
    // (6) cfg.tz different from the writer's Local: written in Berlin, read in
    //     Chicago. The wake is 23:00 on the 6th in Chicago (06:00 on the 7th in
    //     Berlin), so the start at midnight is the 6th's.
    {
        let mut w = Writer::new(chrono_tz::Europe::Berlin);
        let base = utc(2026, 9, 7, 4, 0, 0);
        w.push(base, ev_wake(420));
        w.push(base + Duration::hours(1), ev_start("17"));
        w.push(base + Duration::hours(2), ev_done("17", 50, false));
        w.push(base + Duration::hours(20), ev_wake(380));
        w.push(base + Duration::hours(21), ev_undo("done", Some("17")));
        let expect = vec![(1, date(2026, 9, 6)), (2, date(2026, 9, 6)), (3, date(2026, 9, 6)), (4, date(2026, 9, 7)), (5, date(2026, 9, 7))];
        out.push(ZoneCase { name: "cfg.tz Chicago, written in Berlin".to_string(), text: w.text(), tz: chicago, expect, named: vec![], gaps: vec![] });
    }
    // (7) A `:60` stamp at the 24-hour edge (carried note 1): chrono's
    //     `signed_duration_since` counts a leap second only before a later clock of
    //     the day, so the 24 hours are chrono's, not a difference of nanoseconds.
    //     `02:59:60.5` the next day is 23 h 59 min 59.5 s after a 03:00:00 wake (the
    //     wake's day; by nanoseconds 24 h 0.5 s); `03:01:00` the next day is 24 h
    //     0.5 s after a `03:00:60.5` wake (its own day; by nanoseconds 23 h 59 min
    //     59.5 s).
    {
        let tz = chrono_tz::UTC;
        let mut w = Writer::new(tz);
        w.push(utc(2026, 9, 7, 3, 0, 0), ev_wake(420));
        w.push_raw(r#"{"t":"2026-09-08T02:59:60.5Z","ev":"note","text":"leap"}"#.to_string());
        w.push_raw(r#"{"t":"2026-09-10T03:00:60.5Z","ev":"wake","slept_min":400}"#.to_string());
        w.push(utc(2026, 9, 11, 3, 1, 0), Event::Note { text: "edge".into() });
        w.push(utc(2026, 9, 11, 3, 2, 0), Event::Note { text: "undone".into() });
        w.push(utc(2026, 9, 11, 3, 3, 0), ev_undo("note", None));
        let expect = vec![(1, date(2026, 9, 7)), (2, date(2026, 9, 7)), (3, date(2026, 9, 10)), (4, date(2026, 9, 11))];
        out.push(ZoneCase { name: "a :60 stamp at the 24-hour edge".to_string(), text: w.text(), tz, expect, named: vec![], gaps: vec![] });
    }
    // (8) C4, carried note 3: St John's clock going back across midnight (00:01 NDT to 23:01
    //     NST before 2011; the first such transition of the probed table, 1987-10-25). `event
    //     arrival` 30 s before the change is dated D; one 29 minutes after it, a later instant,
    //     is dated D − 1; a third, addressed to `3`, after both. The key addressed to nobody has
    //     line 3 latest by instant and line 2 latest by date; `latest_named(arrival, 3)` merges
    //     in line 4. A retro routine `done` of line 5's instance separates the instance from
    //     `last_done`. Every entry is under 24 hours after the wake, so on the wake's day, D − 1.
    {
        let tz = chrono_tz::America::St_Johns;
        let (at, before, after) = backwards_date_transition(tz).expect("St John's goes back across midnight");
        let at = DateTime::from_timestamp(at, 0).expect("in range");
        let mut w = Writer::new(tz);
        w.push_at((at - Duration::hours(2)).with_timezone(&east(before)), ev_wake(400));
        w.push_at((at - Duration::seconds(30)).with_timezone(&east(before)), Event::Named { name: "arrival".into(), id: None });
        w.push_at((at + Duration::minutes(29)).with_timezone(&east(after)), Event::Named { name: "arrival".into(), id: None });
        w.push_at((at + Duration::minutes(40)).with_timezone(&east(after)), Event::Named { name: "arrival".into(), id: Some("3".into()) });
        w.push_at((at + Duration::minutes(50)).with_timezone(&east(after)), ev_routine("stretch", "#1", "done", None));
        w.push_at((at - Duration::minutes(50)).with_timezone(&east(before)), ev_routine("stretch", "#1", "done", Some(4)));
        w.push_at((at + Duration::minutes(55)).with_timezone(&east(after)), ev_routine("stretch", "#2", "done", None));
        w.push_at((at + Duration::minutes(56)).with_timezone(&east(after)), ev_undo("routine", Some("stretch")));
        let d7 = (at - Duration::seconds(30)).with_timezone(&tz).date_naive();
        assert_eq!((at + Duration::minutes(29)).with_timezone(&tz).date_naive(), d7 - Duration::days(1), "the clock went back across midnight");
        out.push(ZoneCase {
            name: "St John's clock back across midnight, events and completions".to_string(),
            text: w.text(),
            tz,
            expect: vec![(2, d7 - Duration::days(1)), (3, d7 - Duration::days(1)), (6, d7 - Duration::days(1))],
            named: vec![("arrival", None, 3, 2), ("arrival", Some("3"), 4, 4)],
            gaps: vec![],
        });
    }
    // (9) C5: a gap, a routine and a break across Chicago's fall-back hour. Wakes at 06:00 CDT on
    //     31 October and at 01:05 CDT on 1 November (19 hours later, a new date, so a new day). A
    //     `leak` gap of 90 minutes answered at 01:20 CST began at 00:50 CDT, before the second
    //     wake: its record is the 31st's. A routine `done` of 50 minutes at 01:30 CST began at 01:40
    //     CDT, after it; a break of 60 minutes from 01:45 CDT ends at 01:45 CST, the hour used twice.
    {
        let mut w = Writer::new(chicago);
        w.push(utc(2026, 10, 31, 11, 0, 0), ev_wake(420));
        w.push(utc(2026, 11, 1, 6, 5, 0), ev_wake(200));
        w.push(utc(2026, 11, 1, 7, 20, 0), Event::Idle { attributed: "leak".into(), min: 90 });
        w.push(utc(2026, 11, 1, 7, 30, 0), Event::Routine { item: "stretch".into(), inst: "#1".into(), status: "done".into(), actual_min: Some(50) });
        w.push(utc(2026, 11, 1, 6, 45, 0), Event::Break { planned_min: 60, actual_min: None, r#where: None });
        w.push(utc(2026, 11, 1, 7, 50, 0), Event::Note { text: "undone".into() });
        w.push(utc(2026, 11, 1, 7, 51, 0), ev_undo("note", None));
        let expect = vec![(1, date(2026, 10, 31)), (2, date(2026, 11, 1)), (3, date(2026, 11, 1)), (4, date(2026, 11, 1)), (5, date(2026, 11, 1))];
        out.push(ZoneCase {
            name: "a gap, a routine and a break across the fall-back hour".to_string(),
            text: w.text(),
            tz: chicago,
            expect,
            named: vec![],
            gaps: vec![date(2026, 10, 31)],
        });
    }
    out
}

// ---------------------------------------------------------------------------
// The tests.

/// The seven corpus logs.
// ---------------------------------------------------------------------------
// C7: the undo law's `(L, E, M)` triples (design §7.3).

/// How many `(L, E, M)` triples T5 runs (design §7.3, §14.4 row C7): the even ones meet `untouchedBy`, the odd
/// ones do not.
const TRIPLES: u64 = 64;

/// Kernel `Replay.matches`: `undo{of, id?}` takes `m` when `m`'s tag is `of` and, when `id` is given, `m`'s
/// primary id is `id` (fork `undo_mask`'s test, without its undo clause: undos never reach the stack).
fn undo_matches(of: &str, id: Option<&str>, m: &Event) -> bool {
    m.name() == of && id.is_none_or(|x| m.primary_id() == Some(x))
}

/// Kernel `Replay.untouchedBy E M`: no event of `M` is an undo, and none matches the undo `tm undo` writes for
/// an event of `E`.
fn untouched_by(e: &[Event], m: &[Event]) -> bool {
    m.iter().all(|x| !matches!(x, Event::Undo { .. }) && e.iter().all(|y| !undo_matches(y.name(), y.primary_id(), x)))
}

/// Kernel `Replay.undosFor E`: what `tm undo` appends for a command's events (`tm/src/cli/undo.rs`), one
/// `undo{of: name, id: primary id}` per event, most recent first.
fn undos_for(e: &[Event]) -> Vec<Event> {
    e.iter().rev().map(|y| ev_undo(y.name(), y.primary_id())).collect()
}

/// One triple: a generated prefix `L`, a command's events `E`, events `M` the command did not write, and
/// `tm undo`'s appends.
struct Triple {
    tz: Tz,
    kind: &'static str,
    e: Vec<Event>,
    m: Vec<Event>,
    /// `L ++ E ++ M ++ undosFor E`.
    undone: String,
    /// `L ++ M`, with `E`'s lines blank: every entry keeps the line it has in the undone log, as the kernel's
    /// law states it (entries carry their lines).
    without: String,
    /// `L ++ E ++ M`: the log before `tm undo`.
    before: String,
    /// Lines the fork's mask must cancel in the undone log, and lines it must leave standing.
    cancelled: Vec<u64>,
    standing: Vec<u64>,
}

fn ev_named(name: &str, id: Option<&str>) -> Event {
    Event::Named { name: name.into(), id: id.map(str::to_string) }
}

/// **Triple `seed`.** `L` is generated sequence `1000 + seed`. An even seed takes a command from seven kinds
/// (`tm done`'s done and routine, a start, a week close, a drop, a move, an interrupt and its resume, and two
/// events of one name whose undos overlap, so their order matters) and 0 to 4 events for `M` from a pool that
/// holds the automatic close, keeping those `untouchedBy` allows. An odd seed breaks the hypothesis one of four
/// ways: quirk Q6(f)'s automatic close after a week close; `M` repeating the command's `done`; the command's
/// event without an id and `M`'s with one; and an undo in `M` that takes the command's event, so `tm undo`'s own
/// reaches into `L`.
fn triple(seed: u64) -> Triple {
    let g = generate(1_000 + seed);
    let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9) ^ 0xc7);
    let mut w = Writer::new(g.tz);
    for l in g.text.lines() {
        w.push_raw(l.to_string());
    }
    let mut now = g.now;
    let id = *rng.pick(&["1", "2", "17"]);
    let key = now.with_timezone(&g.tz).date_naive().to_string();
    let (kind, e, m, pre): (&'static str, Vec<Event>, Vec<Event>, Vec<Event>) = if seed % 2 == 0 {
        let (kind, e) = match rng.below(7) {
            0 => ("done", vec![ev_done(id, 30, false), ev_routine("stretch", "2026-09-07", "done", None)]),
            1 => ("start", vec![ev_start(id)]),
            2 => ("close week", vec![ev_close("week", "2026-W37")]),
            3 => ("drop", vec![Event::Drop { id: id.into() }]),
            4 => ("move", vec![Event::Move { id: id.into(), from: "week/2026-W37.md".into(), to: "backlog.md".into() }]),
            5 => ("interrupt", vec![Event::Interrupt { id: Some(id.into()) }, Event::Resume { lost_min: 5, dropped: vec![] }]),
            _ => ("overlapping events", vec![ev_named("arrival", None), ev_named("arrival", Some(id))]),
        };
        let pool = [
            ev_close("day", &key),
            Event::Note { text: "between".into() },
            ev_wake(400),
            Event::Plan { hash: "m".into(), replans_today: 1, drift_min: 0 },
            ev_done("m9", 20, false),
            ev_named("lunch", None),
            Event::Energy { pred: 3, rep: 4, hsw: 3.25, loc: "home".into() },
            ev_start("m9"),
            Event::Drop { id: "m9".into() },
        ];
        let m: Vec<Event> = (0..rng.below(5)).map(|_| rng.pick(&pool).clone()).filter(|x| untouched_by(&e, std::slice::from_ref(x))).collect();
        (kind, e, m, vec![])
    } else {
        match (seed / 2) % 4 {
            0 => ("housekeeping close (Q6(f))", vec![ev_close("week", "2026-W37")], vec![ev_close("day", &key)], vec![]),
            1 => ("M repeats the done", vec![ev_done(id, 30, false)], vec![ev_done(id, 45, false)], vec![]),
            2 => ("an id-less event, then one with an id", vec![ev_named("arrival", None)], vec![ev_named("arrival", Some("m9"))], vec![]),
            _ => ("an undo in M", vec![ev_done(id, 30, false)], vec![ev_undo("done", None)], vec![ev_done(id, 25, false), ev_done("b", 25, false)]),
        }
    };
    // `L`'s tail (the undo-in-M case's two dones), the command, the events after it, and `tm undo` at one instant.
    let pre_lines: Vec<u64> = pre.into_iter().map(|x| w.push(tick(&mut now, &mut rng), x)).collect();
    let e_lines: Vec<u64> = e.iter().map(|x| w.push(tick(&mut now, &mut rng), x.clone())).collect();
    let m_lines: Vec<u64> = m.iter().map(|x| w.push(tick(&mut now, &mut rng), x.clone())).collect();
    let before = w.text();
    let t = tick(&mut now, &mut rng);
    let u_lines: Vec<u64> = undos_for(&e).into_iter().map(|x| w.push(t, x)).collect();
    let undone = w.text();
    let mut blanked = w.lines.clone();
    blanked.truncate(*u_lines.first().expect("a command has events") as usize - 1);
    for l in &e_lines {
        blanked[*l as usize - 1] = String::new();
    }
    let without = loggen::text(&blanked);
    let law = untouched_by(&e, &m);
    assert_eq!(law, seed % 2 == 0, "triple {seed} ({kind}): untouchedBy is {law}");
    let (cancelled, standing) = if law {
        (e_lines.iter().chain(&u_lines).copied().collect(), m_lines.clone())
    } else {
        match (seed / 2) % 4 {
            // The undo takes `M`'s event, the latest match, and leaves the command's standing.
            0..=2 => (m_lines.iter().chain(&u_lines).copied().collect(), e_lines.clone()),
            // `M`'s undo takes the command's `done`; `tm undo`'s takes `L`'s `done` of the id, and `L`'s last `done` stands.
            _ => (vec![pre_lines[0], e_lines[0], m_lines[0], u_lines[0]], vec![pre_lines[1]]),
        }
    };
    Triple { tz: g.tz, kind, e, m, undone, without, before, cancelled, standing }
}

/// The facts the undo law speaks of: everything but the line bookkeeping (the cancelled lines, every line's day and
/// view row, the entry and line counts), which appending undos changes (Replay.lean's `factsView`).
fn law_view(k: &Facts) -> (&Block, &Completion, &DayFam, &BTreeMap<i64, SeamRow>, Option<i64>) {
    (&k.block, &k.completion, &k.day, &k.seams, k.counts.2)
}

fn corpus_logs() -> Vec<(String, String)> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../kernel/corpus");
    [
        "logs/energy-14d.jsonl",
        "logs/malformed.jsonl",
        "logs/review-14d.jsonl",
        "logs/three-days.jsonl",
        "plan-home-day/.tm/log.jsonl",
        "plan-recur/.tm/log.jsonl",
        "plan-travel-day/.tm/log.jsonl",
    ]
    .iter()
    .map(|p| (p.to_string(), std::fs::read_to_string(root.join(p)).expect("corpus log")))
    .collect()
}

/// **T5 over the corpus logs**: every one in full.
#[test]
fn t5_the_corpus_logs_replay_as_the_fork_does() {
    let (mut cancelled, mut days, mut off, mut tally) = (0, 0, 0, Tally::default());
    for (name, text) in corpus_logs() {
        let k = assert_parity(&name, &text, chrono_tz::America::Chicago);
        tally.retro_instances += q6b_separations(&text, chrono_tz::America::Chicago);
        cancelled += k.cancelled.len();
        days += k.days.len();
        off += off_their_own_date(&text, chrono_tz::America::Chicago);
        tally.add(&k.block);
        tally.add_completion(&k.completion);
        tally.add_day(&k.day, &k.block);
        tally.add_view(&k);
        let (late, early) = day_separations(&text, chrono_tz::America::Chicago);
        tally.late_sleeps += late;
        tally.early_gaps += early;
    }
    assert!(tally.durations > 0 && tally.items > 0, "the corpus has blocks");
    eprintln!("T5 corpus: 7 logs, {cancelled} cancelled lines, {days} days compared ({off} off their own local date); {tally}; {} latest_named queries; 0 exceptions", latest_named_queries());
}

/// **T5 over the generated 1-month and 6-month logs** (40 a day, seed 7).
#[test]
fn t5_the_generated_month_and_half_year_replay_as_the_fork_does() {
    for (label, days) in [("1mo", 30), ("6mo", 182)] {
        let lines = loggen::log(loggen::Rate::Forty, days);
        let text = loggen::text(&lines);
        let start = std::time::Instant::now();
        let k = assert_parity(label, &text, chrono_tz::America::Chicago);
        assert!(!k.cancelled.is_empty(), "{label}: the generator writes undos");
        let ms = start.elapsed().as_secs_f64() * 1000.0;
        let mut tally = Tally::default();
        tally.add(&k.block);
        tally.add_completion(&k.completion);
        tally.add_day(&k.day, &k.block);
        tally.add_view(&k);
        let (late, early) = day_separations(&text, chrono_tz::America::Chicago);
        tally.late_sleeps += late;
        tally.early_gaps += early;
        tally.retro_instances += q6b_separations(&text, chrono_tz::America::Chicago);
        eprintln!(
            "T5 {label}: {} lines, {} bytes, {} cancelled, {} days compared ({} off their own local date); {tally}; {} latest_named queries so far; {ms:.0} ms for both readers, 0 exceptions",
            lines.len(),
            text.len(),
            k.cancelled.len(),
            k.days.len(),
            off_their_own_date(&text, chrono_tz::America::Chicago),
            latest_named_queries(),
        );
    }
}

/// **T5 over 256 generated sequences**, every arm forced at least once.
#[test]
fn t5_generated_sequences_replay_as_the_fork_does() {
    let mut counts: BTreeMap<Arm, usize> = BTreeMap::new();
    let mut zones: BTreeMap<&str, usize> = BTreeMap::new();
    let (mut lines, mut cancelled, mut silent, mut auto, mut days, mut off) = (0, 0, 0, 0, 0, 0);
    let mut tally = Tally::default();
    let mut edges: BTreeMap<u64, usize> = BTreeMap::new();
    let mut completions: BTreeMap<u64, usize> = BTreeMap::new();
    let mut day_edges: BTreeMap<u64, usize> = BTreeMap::new();
    for seed in 0..SEQUENCES {
        let g = generate(seed);
        let k = assert_parity(&format!("sequence {seed}"), &g.text, g.tz);
        tally.add(&k.block);
        tally.add_completion(&k.completion);
        tally.add_day(&k.day, &k.block);
        tally.add_view(&k);
        let (late, early) = day_separations(&g.text, g.tz);
        tally.late_sleeps += late;
        tally.early_gaps += early;
        for e in &g.day_edges {
            *day_edges.entry(*e).or_default() += 1;
        }
        tally.retro_instances += q6b_separations(&g.text, g.tz);
        for e in &g.edges {
            *edges.entry(*e).or_default() += 1;
        }
        for e in &g.completions {
            *completions.entry(*e).or_default() += 1;
        }
        for a in &g.arms {
            *counts.entry(*a).or_default() += 1;
        }
        *zones.entry(g.tz.name()).or_default() += 1;
        lines += g.text.lines().count();
        cancelled += k.cancelled.len();
        days += k.days.len();
        off += off_their_own_date(&g.text, g.tz);
        // Quirk Q6(d): the silent-verb undo cancels the older move, in both readers.
        for t in &g.silent_targets {
            assert!(k.cancelled.contains(t), "sequence {seed}: the silent-verb undo left line {t} standing");
            silent += 1;
        }
        // Quirk Q6(f): the undo of the week close cancels the automatic close.
        for (week, auto_close) in &g.housekeeping {
            assert!(k.cancelled.contains(auto_close), "sequence {seed}: the automatic close on line {auto_close} stands");
            if !k.cancelled.contains(week) {
                auto += 1;
            }
        }
    }
    for arm in ARMS {
        assert!(counts.get(&arm).copied().unwrap_or(0) > 0, "arm {arm:?} never ran");
    }
    assert!(silent > 0, "quirk Q6(d) never exercised");
    assert!(auto > 0, "quirk Q6(f) never left a week close standing");
    assert_eq!(edges.len(), 14, "every block edge case ran: {edges:?}");
    assert!(tally.ci_unknown > 0 && tally.interrupts > 0 && tally.open_blocks > 0 && tally.open_interrupts > 0, "the block edges ran: {tally}");
    assert_eq!(completions.len() as u64, COMPLETION_EDGES, "every completion edge case ran: {completions:?}");
    assert!(
        tally.retro_instances > 0 && tally.clock_back_keys > 0 && tally.replay_warnings > 0 && tally.done_dates > 0,
        "quirk Q6(b), the clock going back and the replay warnings were exercised: {tally}"
    );
    assert_eq!(day_edges.len() as u64, DAY_EDGES, "every day edge case ran: {day_edges:?}");
    assert!(
        tally.break_anchors > 0 && tally.marks.iter().all(|m| *m > 0) && tally.cancelled_rows > 0,
        "C6: a break's end as the anchor, every kind of idle mark and cancelled rows were exercised: {tally}"
    );
    assert!(
        tally.late_sleeps > 0 && tally.early_gaps > 0 && tally.demotion_stamps > 0 && tally.longest_leaks > 0 && tally.unknown > 0 && tally.arrivals > 0,
        "late binding, gaps on the day they began, demote stamps, leaks, unknown events and arrivals were exercised: {tally}"
    );
    eprintln!(
        "T5 sequences: {SEQUENCES} logs, {lines} lines, {cancelled} cancelled, {days} days compared ({off} off their own local date), {silent} silent-verb undos \
         cancelling an older move, {auto} week closes left standing by an undo that took the automatic close; {tally}; block edge cases {edges:?}; completion edge cases {completions:?}; day edge cases {day_edges:?}; {} latest_named queries; arms {counts:?}; zones {zones:?}; 0 exceptions",
        latest_named_queries()
    );
}

/// **T5 over §6.4's zone cases**, each its own arm, with the days each case
/// names checked against the kernel's facts.
#[test]
fn t5_the_zone_cases_replay_as_the_fork_does() {
    let cases = zone_cases();
    let (mut days, mut named, mut off, mut tally, mut named_keys) = (0, 0, 0, Tally::default(), 0);
    for c in &cases {
        let k = assert_parity(&c.name, &c.text, c.tz);
        tally.add(&k.block);
        tally.add_completion(&k.completion);
        tally.add_day(&k.day, &k.block);
        tally.add_view(&k);
        let (late, early) = day_separations(&c.text, c.tz);
        tally.late_sleeps += late;
        tally.early_gaps += early;
        tally.retro_instances += q6b_separations(&c.text, c.tz);
        assert!(!k.cancelled.is_empty(), "{}: every zone case carries an undo", c.name);
        for (line, d) in &c.expect {
            assert_eq!(day_of_line(&k, *line), day_number(*d), "{}: line {line} should be on {d}", c.name);
            named += 1;
        }
        let gap_days: Vec<i64> = k.day.days.iter().flat_map(|(d, rec)| rec.idle.iter().map(move |i| {
            assert_eq!(i.1, *d, "{}: an idle record is on its own day", c.name);
            *d
        })).collect();
        if !c.gaps.is_empty() {
            assert_eq!(gap_days, c.gaps.iter().map(|d| day_number(*d)).collect::<Vec<_>>(), "{}: the gaps' days", c.name);
            named += c.gaps.len();
        }
        for (n, id, latest, dated) in &c.named {
            let rec = k.completion.named.get(&(n.to_string(), id.map(str::to_string))).expect("the named key");
            assert_eq!((rec.0, rec.2), (*latest, *dated), "{}: {n} {id:?}", c.name);
            named_keys += 1;
        }
        days += k.days.len();
        off += off_their_own_date(&c.text, c.tz);
    }
    eprintln!(
        "T5 zone cases: {} ({:?}), {days} days compared, {named} named days checked, {named_keys} named-event keys checked by hand, {off} entries off their own local date; {tally}; {} latest_named queries; 0 exceptions",
        cases.len(),
        cases.iter().map(|c| &c.name).collect::<Vec<_>>(),
        latest_named_queries()
    );
}

/// **C7: T5 over [`TRIPLES`] `(L, E, M)` triples** (design §7.3). Every undone log, every log without the command,
/// and every log before the undo is compared in full with the fork. A triple that meets `untouchedBy` must satisfy
/// the undo law: the undone log and the log without the command agree on every fact but the line bookkeeping
/// (Replay.lean's `undoing_a_command_replays_the_log_without_it`). A triple that does not must reproduce the fork's
/// cancellation, line by line, and there the two logs disagree (`the_undo_law_fails_without_untouchedBy`).
#[test]
fn t5_undo_triples_meet_the_law_or_reproduce_the_forks_cancellation() {
    let mut kinds: BTreeMap<(bool, &str), usize> = BTreeMap::new();
    let (mut lines, mut m_events, mut auto_closes, mut e_mattered, mut law_count, mut broken) = (0, 0, 0, 0, 0, 0);
    for seed in 0..TRIPLES {
        let tr = triple(seed);
        let name = format!("triple {seed} ({})", tr.kind);
        let law = untouched_by(&tr.e, &tr.m);
        let undone = assert_parity(&format!("{name}, undone"), &tr.undone, tr.tz);
        let without = assert_parity(&format!("{name}, without the command"), &tr.without, tr.tz);
        let before = assert_parity(&format!("{name}, before the undo"), &tr.before, tr.tz);
        for l in &tr.cancelled {
            assert!(undone.cancelled.contains(l), "{name}: line {l} should be cancelled");
        }
        for l in &tr.standing {
            assert!(!undone.cancelled.contains(l), "{name}: line {l} should stand");
        }
        if law {
            assert!(law_view(&undone) == law_view(&without), "{name}: untouchedBy holds, and the undone log's facts are not the log's without the command");
            law_count += 1;
        } else {
            assert!(law_view(&undone) != law_view(&without), "{name}: untouchedBy fails, and yet the undone log's facts are the log's without the command");
            broken += 1;
        }
        e_mattered += usize::from(law_view(&before) != law_view(&without));
        *kinds.entry((law, tr.kind)).or_default() += 1;
        lines += tr.undone.lines().count();
        m_events += tr.m.len();
        auto_closes += tr.m.iter().filter(|x| matches!(x, Event::Close { period, .. } if period == "day")).count();
    }
    assert_eq!((law_count, broken), (TRIPLES / 2, TRIPLES / 2), "half meet untouchedBy, half do not");
    assert!(kinds.len() == 11, "every command kind and every violation ran: {kinds:?}");
    assert!(auto_closes > 0 && e_mattered > TRIPLES as usize / 2, "housekeeping ran and the commands changed facts: {auto_closes} automatic closes, {e_mattered} commands that mattered");
    eprintln!(
        "T5 triples: {TRIPLES} (L, E, M) triples, {lines} undone lines, {m_events} events in M ({auto_closes} automatic closes); {law_count} meet untouchedBy and satisfy the law, {broken} do not and reproduce the fork's cancellation; {e_mattered} commands whose facts the undo took back; kinds {kinds:?}; 0 exceptions"
    );
}

/// The generator is deterministic: a sequence is its seed.
#[test]
fn t5_a_sequence_is_its_seed() {
    assert_eq!(generate(41).text, generate(41).text);
    assert_ne!(generate(41).text, generate(42).text);
}

/// **The fast twin on a hostile log** (Replay.lean's `survivors_eq_survivorsFast`,
/// rule D9-21): 4,000 `done`s of distinct ids, then 2,000 undos of ids nothing
/// carries and 2,000 of a tag nothing carries (W3: 8,000 lines, under the memory gate's 8,192). The specification's `eraseP` scans
/// the whole stack for each undo (25 million matches); the per-tag and per-(tag,
/// id) stacks answer each in constant time. Under 1 MiB, one call (gap 102's
/// memory gate). `#[ignore]`d: a measurement, run by hand and recorded in the
/// README; the parity it checks is the same as the tests above.
#[test]
#[ignore]
fn t5_a_hostile_undo_log_is_answered_in_linear_time() {
    let tz = chrono_tz::UTC;
    let mut w = Writer::new(tz);
    let t0 = utc(2026, 9, 7, 9, 0, 0);
    // W3: 8,000 lines, within the memory gate's line bound of 8,192 (was 5,000, 2,500 and 2,500).
    for i in 0..4_000 {
        w.push(t0, ev_done(&format!("i{i}"), 30, false));
    }
    for i in 0..2_000 {
        w.push(t0, ev_undo("done", Some(&format!("absent{i}"))));
    }
    for _ in 0..2_000 {
        w.push(t0, ev_undo("rank", None));
    }
    let text = w.text();
    let start = std::time::Instant::now();
    let k = kernel_facts(&text, tz);
    let kernel_ms = start.elapsed().as_secs_f64() * 1000.0;
    let start = std::time::Instant::now();
    let r = rust_facts(&text, tz);
    let rust_ms = start.elapsed().as_secs_f64() * 1000.0;
    assert_eq!(k, r);
    assert!(text.len() < 1 << 20, "under 1 MiB");
    assert_eq!(k.cancelled.len(), 4_000);
    eprintln!("T5 hostile: {} lines, {} bytes, kernel {kernel_ms:.0} ms, rust {rust_ms:.0} ms", w.lines.len(), text.len());
}

/// **The block family over many items** (C3; a measurement, `#[ignore]`d and
/// recorded in the README). 3,500 blocks of distinct ids, a `start` and a
/// `done` each: every credit looks its item up in `Replay.HMap`, one bucket of
/// an array sized to the log, so an id with no locality costs one bucket's scan
/// (W4's tree maps are the design's lever). Under 1 MiB, one call (gap 102's
/// memory gate). The parity it checks is the same as the tests above.
#[test]
#[ignore]
fn t5_a_block_log_of_distinct_ids_is_measured() {
    let tz = chrono_tz::UTC;
    let mut w = Writer::new(tz);
    let mut now = utc(2026, 9, 7, 0, 0, 0);
    for i in 0..3_500 {
        let id = format!("i{i}");
        w.push(now, ev_start(&id));
        now += Duration::minutes(1);
        w.push(now, ev_done(&id, 1, false));
        now += Duration::minutes(1);
    }
    let text = w.text();
    assert!(text.len() < 1 << 20, "under 1 MiB: {}", text.len());
    let start = std::time::Instant::now();
    let k = kernel_facts(&text, tz);
    let kernel_ms = start.elapsed().as_secs_f64() * 1000.0;
    let start = std::time::Instant::now();
    let r = rust_facts(&text, tz);
    let rust_ms = start.elapsed().as_secs_f64() * 1000.0;
    assert_eq!(k.block.items.len(), 3_500);
    assert_eq!(k, r);
    eprintln!("T5 distinct ids: {} lines, {} bytes, kernel {kernel_ms:.0} ms, rust {rust_ms:.0} ms", w.lines.len(), text.len());
}

/// **Parity P34, the named exception** (C5): an `idle` gap whose minutes reach
/// before 0001-01-01T00:00:00Z. `idle.min` is a `u32`, so 4,294,967,295 minutes
/// (about 8,166 years) before 2026-09-07 is a negative year: chrono's
/// `t - Duration::minutes(min)` gives it, and the fork puts the `Idle` segment, the
/// `IdleRecord` and the longest leak on that day. The kernel's instants start at the
/// origin (`Cal.subMinutes` saturates there), so it puts them on day 0,
/// 0001-01-01, with the segment starting at the origin. Everything else is compared
/// as in the tests above, with the one day and the one start put back.
#[test]
fn t5_p34_a_gap_before_the_origin_is_the_named_exception() {
    let tz = chrono_tz::UTC;
    let mut w = Writer::new(tz);
    w.push(utc(2026, 9, 7, 9, 0, 0), Event::Idle { attributed: "leak".into(), min: u32::MAX });
    let text = w.text();
    let (k, mut r) = (kernel_facts(&text, tz), rust_facts(&text, tz));
    let fork_day = r.day.longest_leak.as_ref().expect("the fork's longest leak").1;
    assert!(fork_day < 0, "the fork dates the gap in a negative year: day {fork_day}");
    assert_eq!(k.day.longest_leak.as_ref().map(|l| l.1), Some(0), "the kernel dates it at the origin");
    let origin: Stamp = (0, 0, false, 0);
    let mut block = r.block.days.remove(&fork_day).expect("the fork's day of the gap");
    assert!(block.segments[0].0 .0 < 0, "the fork's segment starts before the origin");
    block.segments[0].0 = origin;
    r.block.days.insert(0, block);
    let mut rec = r.day.days.remove(&fork_day).expect("the fork's record of the gap");
    rec.idle[0].1 = 0;
    r.day.days.insert(0, rec);
    if let Some(l) = r.day.longest_leak.as_mut() {
        l.1 = 0;
    }
    // C6: the gap's day is the only day with a record, so it is the last day too.
    assert_eq!(r.counts.2, Some(fork_day), "the fork's last day is the gap's");
    r.counts.2 = Some(0);
    assert_eq!(k, r, "P34 is the only difference");
}

/// **Parity P33, the named exception** (C4): a routine `done` whose `inst` names a
/// date before 0001-01-01. chrono's `parse_date` reads `0000-09-07` (year 0) as a
/// date, so the fork records the completion on it; the kernel's days start at
/// 0001-01-01 (`Cal.Day`), `Log.instDate?` reads no such date, and the completion is
/// recorded on its wake-attributed day. Everything else about the log is compared
/// as in the tests above; `done_dates` is compared with the one date put back.
#[test]
fn t5_p33_a_done_date_before_the_origin_is_the_named_exception() {
    let tz = chrono_tz::UTC;
    let mut w = Writer::new(tz);
    w.push(utc(2026, 9, 7, 9, 0, 0), ev_routine("stretch", "0000-09-07", "done", None));
    let text = w.text();
    let (k, mut r) = (kernel_facts(&text, tz), rust_facts(&text, tz));
    let fork = r.completion.done_dates.get("stretch").cloned().expect("the fork's done date");
    assert_eq!(fork, BTreeSet::from([day_number(date(0, 9, 7))]), "the fork dates it in year 0");
    assert_eq!(k.completion.done_dates.get("stretch"), Some(&BTreeSet::from([day_number(date(2026, 9, 7))])), "the kernel dates it on its day");
    r.completion.done_dates.insert("stretch".to_string(), BTreeSet::from([day_number(date(2026, 9, 7))]));
    // C6: the date is also the item's first done date.
    assert_eq!(r.completion.done_first.get("stretch"), Some(&(Some(day_number(date(0, 9, 7))), 1)), "the fork's first done date is in year 0");
    r.completion.done_first.insert("stretch".to_string(), (Some(day_number(date(2026, 9, 7))), 1));
    assert_eq!(k, r, "P33 is the only difference");
}


// ---------------------------------------------------------------------------
// W3: the window across the wire (design §9.6–§9.8, §10, §11.1; README "Stage 5 D9 W3").

/// W3: render-only calls (no resume, so no checkpoint and no `now` needed by the kernel) over a whole log, at most 4,096
/// lines each: every line's display and every line warning, as the one-call answer carries them.
fn displays_and_warnings(s: &kernel_log::Split, table: &Value) -> (BTreeMap<u64, String>, Vec<Value>) {
    let (mut displays, mut warnings) = (BTreeMap::new(), Vec::new());
    let n = s.lines.len();
    let mut k = 0;
    while k < n {
        let m = (n - k).min(4096);
        let want = kernel_log::Want { facts: false, headers_from: None, render: (k as u64 + 1..=(k + m) as u64).collect() };
        let req = kernel_log::request("2026-09-15", table, None, k as u64 + 1, &s.lines[k..k + m], k + m < n || s.terminated, None, &want, None);
        let a = kernel_log::log_call(&req).expect("the kernel answers").expect("a render-only call is not refused");
        for r in a.render.as_array().expect("render") {
            if let Some(d) = r[2].as_str() {
                displays.insert(r[0].as_u64().expect("a line"), d.to_string());
            }
        }
        warnings.extend(a.warnings.as_array().expect("warnings").iter().cloned());
        k += m;
    }
    (displays, warnings)
}

/// **W3: a windowed answer as the whole replay's** (§11.1's `All` scope): the snapshot's day records below its ledger day
/// and window records below its horizon, then the answer's own (which win where both hold a key), every day record's
/// headers with their day and the display a render-only call gives, and every line warning. `kernel_view` then reads it
/// exactly as it reads a one-call answer.
fn windowed_log(facts: &Value, days: &BTreeMap<u64, String>, window: &BTreeMap<u64, String>, s: &kernel_log::Split, table: &Value) -> Value {
    let mut facts = facts.clone();
    let parse = |t: &String| serde_json::from_str::<Value>(t).expect("a sealed record reads");
    let mut all_days: BTreeMap<u64, Value> = days.iter().map(|(d, t)| (*d, parse(t))).collect();
    for d in facts["days"].as_array().expect("facts.days") {
        all_days.insert(d[0].as_u64().expect("a day"), d.clone());
    }
    let mut all_window: BTreeMap<u64, Value> = window.iter().map(|(d, t)| (*d, parse(t))).collect();
    for w in facts["window"].as_array().expect("facts.window") {
        all_window.insert(w[0].as_u64().expect("a date"), w.clone());
    }
    let (displays, warnings) = displays_and_warnings(s, table);
    let mut headers: Vec<(u64, Value)> = Vec::new();
    for (d, rec) in &all_days {
        for h in rec[8].as_array().expect("a record's headers") {
            let line = h[0].as_u64().expect("a line");
            let display = displays.get(&line).unwrap_or_else(|| panic!("line {line} has no display"));
            headers.push((line, json!([line, h[1], h[2], d, h[3], display])));
        }
    }
    headers.sort_by_key(|h| h.0);
    facts["days"] = Value::Array(all_days.into_values().collect());
    facts["window"] = Value::Array(all_window.into_values().collect());
    json!({"lines": s.lines.len(), "warnings": warnings, "facts": facts, "headers": headers.into_iter().map(|h| h.1).collect::<Vec<_>>()})
}

/// The kernel day after the last dated line of `lines`.
fn day_after(lines: &[String]) -> u64 {
    let last = lines
        .iter()
        .rev()
        .find_map(|l| serde_json::from_str::<Value>(l).ok()?.get("t")?.as_str().and_then(|t| DateTime::parse_from_rfc3339(t).ok()))
        .expect("a dated line");
    kernel_log::day_of(last.date_naive()) + 1
}

/// Compare a replay through the cache with the fork's, merged with every record its snapshot stands on (§11.1's `All`).
fn assert_windowed(name: &str, cache: &kernel_log::ReplayCache, r: &kernel_log::Replayed, text: &str, tz: Tz, table: &Value) -> Facts {
    let s = kernel_log::split(text.as_bytes());
    let facts = r.answer.facts.as_ref().unwrap_or_else(|| panic!("{name}: facts asked"));
    let (days, window) = cache.records_of(r).unwrap_or_else(|| panic!("{name}: the snapshot's records load"));
    assert_parity_answer(name, text, tz, &windowed_log(facts, &days, &window, &s, table))
}

/// **The windowed T5** (W3; design §9.6–§9.8, §11.1, §14.5 row W3's T7 and T10 in part): a year of the generated log in
/// Chicago through [`kernel_log::ReplayCache`] on disk, every answer merged with the records the cache holds and compared
/// with the fork's whole replay (`Ctx::replay_of`):
/// genesis (two chunks), a hot call, a reseal five days on (§9.6's back-off), an old-date read of a sealed week (`sealed`,
/// D13), a hand undo of a folded `done` (G1's `undoReach`, then genesis), a `now` below the ledger day (genesis, not
/// persisted), and a prefix edited on disk (the digest, then genesis).
#[test]
fn t5_windowed_genesis_hot_reseal_old_date_and_fallbacks_replay_as_the_fork_does() {
    let tz = chrono_tz::America::Chicago;
    let table = table(tz);
    let lines = loggen::log(loggen::Rate::Forty, 365);
    let dir = tempfile::tempdir().expect("a temp dir");
    let cdir = dir.path().join(kernel_log::CACHE_DIR);
    let mut cache = kernel_log::ReplayCache::new(Some(cdir.clone()));
    let want = kernel_log::Want { facts: true, headers_from: None, render: vec![] };
    let start = std::time::Instant::now();

    // Genesis over eleven months.
    let a_lines = &lines[..lines.len() - 40 * 30];
    let text_a = loggen::text(a_lines);
    let now_a = day_after(a_lines);
    let ra = cache.replay(text_a.as_bytes(), now_a, &table, None, &want).expect("genesis answers");
    assert_eq!(ra.outcome, kernel_log::Outcome::Genesis, "{:?}", ra.rebuilt_because);
    assert!(cdir.join(kernel_log::CKPT_FILE).exists(), "genesis writes ckpt.json");
    // §9.4: L' is at most F = min(now − keepDays, M − keepDays), M the log's last header day (here `now` − 1).
    assert!(ra.snapshot.meta.ledger_day <= now_a - kernel_log::KEEP_DAYS && ra.snapshot.meta.ledger_day + 4 >= now_a, "ledger day {}", ra.snapshot.meta.ledger_day);
    assert!(ra.days.len() > 300 && ra.snapshot.manifest.len() >= 10, "{} day records, {} months", ra.days.len(), ra.snapshot.manifest.len());
    assert_windowed("windowed genesis", &cache, &ra, &text_a, tz, &table);

    // A hot call the same day: the stored checkpoint and its tail, no reseal.
    let rb = cache.replay(text_a.as_bytes(), now_a, &table, None, &want).expect("a hot call answers");
    assert_eq!(rb.outcome, kernel_log::Outcome::Hot);
    assert_eq!(rb.snapshot.gen, ra.snapshot.gen);
    assert_windowed("windowed hot call", &cache, &rb, &text_a, tz, &table);

    // Five more days, and `now` past them: the back-off's second clause reseals.
    let c_lines = &lines[..lines.len() - 40 * 25];
    let text_c = loggen::text(c_lines);
    let now_c = day_after(c_lines);
    let rc = cache.replay(text_c.as_bytes(), now_c, &table, None, &want).expect("a reseal answers");
    assert_eq!(rc.outcome, kernel_log::Outcome::Resealed);
    assert_eq!(rc.snapshot.prev_gen, ra.snapshot.gen);
    assert!(rc.snapshot.meta.ledger_day > ra.snapshot.meta.ledger_day, "the ledger day moves forward");
    assert_windowed("windowed reseal", &cache, &rc, &text_c, tz, &table);

    // An old-date read: a sealed week (the eighth to the fourteenth day of the log), sent as `sealed` with the tail.
    let snap = cache.read_snapshot().expect("the resealed snapshot");
    let (sd, sw) = cache.all_records(&snap).map(|(_, d, w)| (d, w)).expect("its records load");
    let from = *sd.keys().next().expect("a sealed day") + 7;
    let (days, window) = kernel_log::ReplayCache::sealed_between(&snap, &sd, &sw, from, from + 6);
    assert!(!days.is_empty() && days.len() + window.len() <= kernel_log::MAX_SEALED_IN, "{} day and {} window records", days.len(), window.len());
    let s_c = kernel_log::split(text_c.as_bytes());
    let cut = snap.meta.cut as usize;
    let req = kernel_log::request(&kernel_log::date_of(now_c), &table, Some(&snap.ckpt), cut as u64 + 1, &s_c.lines[cut..], s_c.terminated, None, &want, Some((&days, &window)));
    let old = kernel_log::log_call(&req).expect("the kernel answers").expect("an old-date read is not refused");
    let old_facts = old.facts.expect("facts");
    let merged_days: BTreeSet<u64> = old_facts["days"].as_array().expect("days").iter().map(|d| d[0].as_u64().expect("a day")).collect();
    for rec in &days {
        let d = serde_json::from_str::<Value>(rec).expect("a record")[0].as_u64().expect("a day");
        assert!(merged_days.contains(&d), "the sealed day {d} is merged into the facts");
    }
    let (sd_rest, sw_rest) = (sd.clone(), sw.clone());
    assert_parity_answer("windowed old-date read", &text_c, tz, &windowed_log(&old_facts, &sd_rest, &sw_rest, &s_c, &table));

    // A hand undo of a `done` folded into the checkpoint, with no later `done` of that id: G1 refuses, genesis answers.
    let folded: Vec<(usize, String)> = c_lines[..cut]
        .iter()
        .enumerate()
        .filter_map(|(i, l)| {
            let v: Value = serde_json::from_str(l).ok()?;
            (v["ev"] == "done").then(|| (i, v["id"].as_str().map(str::to_string)))?.1.map(|id| (i, id))
        })
        .collect();
    let (_, id) = folded
        .iter()
        .rev()
        .find(|(i, id)| {
            !c_lines[*i + 1..].iter().any(|l| serde_json::from_str::<Value>(l).is_ok_and(|v| v["ev"] == "done" && v["id"] == id.as_str()))
        })
        .expect("a folded done whose id is never done again");
    let last_t = serde_json::from_str::<Value>(c_lines.last().expect("a line")).expect("json")["t"].as_str().expect("t").to_string();
    let mut e_lines = c_lines.to_vec();
    e_lines.push(format!(r#"{{"t":"{last_t}","ev":"undo","of":"done","id":"{id}"}}"#));
    let text_e = loggen::text(&e_lines);
    let re = cache.replay(text_e.as_bytes(), now_c, &table, None, &want).expect("the fallback answers");
    assert_eq!(re.outcome, kernel_log::Outcome::Genesis);
    assert!(re.rebuilt_because.as_deref().is_some_and(|w| w.starts_with("undoReach")), "{:?}", re.rebuilt_because);
    assert_windowed("windowed far undo", &cache, &re, &text_e, tz, &table);

    // `now` below the ledger day: genesis at that `now`, and ckpt.json is not written.
    let before = std::fs::read(cdir.join(kernel_log::CKPT_FILE)).expect("ckpt.json");
    let low = re.snapshot.meta.ledger_day - 1;
    let rf = cache.replay(text_e.as_bytes(), low, &table, None, &want).expect("the unpersisted genesis answers");
    assert_eq!(rf.outcome, kernel_log::Outcome::GenesisUnpersisted, "{:?}", rf.rebuilt_because);
    assert_eq!(std::fs::read(cdir.join(kernel_log::CKPT_FILE)).expect("ckpt.json"), before, "not persisted");
    assert_windowed("windowed now below the ledger day", &cache, &rf, &text_e, tz, &table);

    // A byte of the prefix edited on disk (the first letter of the first location): the digest sends the next call to
    // genesis.
    let at = text_e.find(r#""loc":""#).expect("an early location") + r#""loc":""#.len();
    assert!((at as u64) < rf.snapshot.prefix_bytes.max(re.snapshot.prefix_bytes), "the edit is inside the stored prefix");
    let mut text_g = text_e.clone();
    text_g.replace_range(at..at + 1, "Q");
    let rg = cache.replay(text_g.as_bytes(), now_c, &table, None, &want).expect("genesis answers");
    assert_eq!(rg.outcome, kernel_log::Outcome::Genesis);
    assert_eq!(rg.rebuilt_because.as_deref(), Some("the prefix's digest differs"));
    assert_windowed("windowed edited prefix", &cache, &rg, &text_g, tz, &table);

    eprintln!(
        "T5 windowed: {} lines, genesis {} day records over {} months, reseal to ledger day {}, old-date read of {} day records; {:.1} s",
        lines.len(),
        ra.days.len(),
        ra.snapshot.manifest.len(),
        rc.snapshot.meta.ledger_day,
        days.len(),
        start.elapsed().as_secs_f64()
    );
}

/// **T0 (b)** (W3; design §14.5 row W3, CRIT 10), on a 2 MiB thread: genesis over a generated 200,000-line log (61 events
/// a day) in chunks of at most 8,192 lines and 1 MiB, every call resealing and emitting its records, the last with facts;
/// one call at exactly the resend cap's 8,192 lines (and one line past it, refused `tooManyLines`); and one reseal
/// emitting 1,997 day records.
#[test]
fn t0b_genesis_over_200000_lines_in_chunks_runs_on_a_2mib_thread() {
    // One continuous run of the generator (`LogGen::days` starts at 2026-01-01 on every call, so calls in a loop would
    // write a log that goes back in time every 30 days, which no CLI writes and whose refusals genesis cannot answer).
    let mut lines = loggen::LogGen::new(loggen::Rate::SixtyOne, loggen::SEED).days(3_400);
    assert!(lines.len() >= 200_000, "{} lines", lines.len());
    lines.truncate(200_000);
    let text = loggen::text(&lines);
    let now = kernel_log::date_of(day_after(&lines));
    let entries = replay::replay_of_text(&text, chrono_tz::UTC).entry_count() as u64;
    let table = table(chrono_tz::UTC);
    let wake_days: Vec<String> = (0..2_000)
        .map(|i| {
            let d = NaiveDate::from_ymd_opt(2020, 1, 1).expect("a date") + Duration::days(i);
            format!(r#"{{"t":"{}T06:00:00Z","ev":"wake","slept_min":420}}"#, d.format("%Y-%m-%d"))
        })
        .collect();
    let handle = std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(move || {
            let s = kernel_log::split(text.as_bytes());
            let policy = kernel_log::Policy { keep_days: kernel_log::KEEP_DAYS, max_line: None };
            let facts = kernel_log::Want { facts: true, headers_from: None, render: vec![] };
            let t = std::time::Instant::now();
            let g = kernel_log::genesis(&now, &table, &s, policy, &facts).expect("genesis answers");
            let genesis_ms = t.elapsed().as_secs_f64() * 1000.0;
            let answered = g.answer.facts.as_ref().expect("the last call's facts")["entryCount"].as_u64().expect("entryCount");
            // One call at exactly the cap, and one line past it.
            let at_cap = kernel_log::request(&now, &table, None, 1, &s.lines[..kernel_log::RESEND_LINES], true, Some(policy), &facts, None);
            assert!(s.bytes_between(0, kernel_log::RESEND_LINES) <= kernel_log::RESEND_BYTES, "the line bound binds first here");
            let t = std::time::Instant::now();
            let a = kernel_log::log_call(&at_cap).expect("the kernel answers").expect("a call at the cap is answered");
            let cap_ms = t.elapsed().as_secs_f64() * 1000.0;
            assert!(a.reseal.is_some(), "the call at the cap reseals");
            let past = kernel_log::request(&now, &table, None, 1, &s.lines[..kernel_log::RESEND_LINES + 1], true, Some(policy), &facts, None);
            let refused = kernel_log::log_call(&past).expect("the kernel answers").expect_err("one line past the cap is refused");
            assert!(matches!(&refused, kernel_log::Refusal::Fault(v) if v["log"] == "tooManyLines"), "{refused:?}");
            // One reseal emitting 2,000 day records: a wake a day for 2,000 days, sealed from nothing.
            let w = kernel_log::split(loggen::text(&wake_days).as_bytes());
            let req = kernel_log::request("2026-01-01", &table, None, 1, &w.lines, true, Some(policy), &kernel_log::Want::default(), None);
            let rs = kernel_log::log_call(&req).expect("the kernel answers").expect("answered").reseal.expect("a reseal");
            (g.calls, g.pops, g.largest_call, g.top.days.len(), g.top.window.len(), answered, genesis_ms, cap_ms, rs.days.len())
        })
        .expect("a 2 MiB thread");
    let (calls, pops, largest, days, window, answered, genesis_ms, cap_ms, sealed_days) = handle.join().expect("no stack overflow");
    assert!(calls >= 25, "{calls} calls");
    assert!(largest <= kernel_log::RESEND_LINES, "{largest}");
    assert_eq!(answered, entries, "the last call answers for every entry");
    assert!(days >= 3_000 && window >= 3_000, "{days} day and {window} window records");
    // F = min(now − keepDays, M − keepDays), M the last wake's day: the last two days stay open, the other 1,997 are sealed.
    assert_eq!(sealed_days, 1_997, "one reseal emits a record a day below F");
    eprintln!(
        "T0 (b): 200,000 lines, {calls} calls, {pops} pops, largest call {largest} lines, {days} day and {window} window records, genesis {genesis_ms:.0} ms; a call at the cap {cap_ms:.0} ms; one reseal of {sealed_days} day records"
    );
}

/// **D18's named fault, reached through a real guard** (W-5 audit repair; OWNER Q9 (iii), §17 P31, gap 120): a
/// hand-written **retro wake** — Q9 (iii)'s own example — appended at the end of a 400-day log and dated on the log's
/// first day. A wake decides the day the lines after it are attributed to, and its own day is long since sealed, so it
/// cannot be folded without re-deciding days the checkpoint has closed: the guard refuses it (`sealedDay`, G3 — the
/// wake's day key lies below the checkpoint's ledger day, which is what refuses first here, measured rather than
/// assumed), and the pop walks back past every checkpoint whose ledger day is above that day — to `Ckpt.empty`. The
/// resend from there through the refusing chunk's end is more lines than the cap allows, so it **is not sent**:
/// genesis fails with `ReachTooFar`, naming the line and the guard that could not be answered.
///
/// Two controls make this the *edit's* fault and not the log's: the same log as the CLI wrote it is answered in chunks
/// with no pop at all (gap 120's block — a CLI-written log cannot reach the cap), and the fork replays the edited log
/// (§17 P31's right-hand column: this is a parity row, not a defect). A retro `done` is deliberately **not** the edit
/// used here — measured at this repair, not assumed: day attribution is wake-based, so a retro-dated `done` lands on
/// the open day and is folded with no refusal at all (a 300-day log so edited answers, 12,297 lines).
#[test]
fn t0b_a_hand_edit_no_window_can_reach_is_the_named_fault_reach_too_far() {
    let tz = chrono_tz::UTC;
    let table = table(tz);
    let lines = loggen::log(loggen::Rate::Forty, 400);
    // The pop reaches no further back than `Ckpt.empty`, so the resend passes the cap only if the whole log does.
    assert!(lines.len() > kernel_log::RESEND_LINES + 4_096, "the resend must be able to pass the cap: {} lines", lines.len());
    let now = kernel_log::date_of(day_after(&lines));
    let policy = kernel_log::Policy { keep_days: kernel_log::KEEP_DAYS, max_line: None };
    let want = kernel_log::Want { facts: true, headers_from: None, render: vec![] };

    // The control: the log as the CLI wrote it is answered, in chunks, with no pop and no call past the cap.
    let clean = loggen::text(&lines);
    let s_clean = kernel_log::split(clean.as_bytes());
    let g = kernel_log::genesis(&now, &table, &s_clean, policy, &want).expect("a CLI-written log is answered");
    assert_eq!(g.pops, 0, "a CLI-written log needs no pop (gap 120's block)");
    assert!(g.largest_call <= kernel_log::RESEND_LINES, "largest call {} lines", g.largest_call);

    // The hand edit: a wake dated on the log's first day, appended last. `now` stays the clean log's, so the edit is
    // retro and does not move the day the rebuild is asked about.
    let first_t = serde_json::from_str::<Value>(&lines[0]).expect("json")["t"].as_str().expect("t").to_string();
    let mut edited = lines.clone();
    edited.push(format!(r#"{{"t":"{first_t}","ev":"wake","slept_min":420}}"#));
    let text = loggen::text(&edited);
    let s = kernel_log::split(text.as_bytes());
    let e = match kernel_log::genesis(&now, &table, &s, policy, &want) {
        Ok(g) => panic!("genesis answered instead of naming the fault: {} calls, {} pops, largest call {} lines", g.calls, g.pops, g.largest_call),
        Err(e) => e,
    };
    let kernel_log::GenesisError::ReachTooFar { line, kind, reach, bytes } = &e else { panic!("the named fault, not {e:?}") };
    assert_eq!(*line, edited.len() as u64, "the fault names the hand-edited line");
    assert_eq!(kind, "sealedDay", "the guard the pop could not answer");
    assert!(*reach > kernel_log::RESEND_LINES as u64, "the resend is past the line bound: {reach} lines, cap {}", kernel_log::RESEND_LINES);
    assert!(*bytes > 0, "the fault reports the resend's size");
    // **The margin over the cap is thin by design, and that is recorded, not relied on by luck.** `CHUNK_LINES` is
    // exactly half `RESEND_LINES`, so a pop of two levels resends about two chunks — just over the cap by the lines
    // `keepDays` left unfolded. Measured at this repair: 8,356 lines against the 8,192 cap, a margin of 164 (2.0%); a
    // 600-day log gives 8,390, a margin of 198, so the margin does not grow with the log. The generator is seeded
    // (`loggen::SEED`) and the rate fixed, so this is deterministic. If a later step changes that 1:2 ratio or
    // `keepDays`, this assertion is what will say so.
    assert!(*reach <= 2 * kernel_log::CHUNK_LINES as u64 + 512, "the reach is about two chunks: {reach}");

    // §17 P31: the fork replays such a log. The kernel's answer is a named fault, and that difference is the parity row.
    let forked = replay::replay_of_text(&text, tz);
    assert_eq!(forked.line_count(), edited.len() as u64, "the fork reads every line of the edited log");
    eprintln!(
        "ReachTooFar: {} lines, the edit at line {line}, {kind}, resend {reach} lines / {bytes} bytes (cap {} lines / {} bytes)",
        edited.len(), kernel_log::RESEND_LINES, kernel_log::RESEND_BYTES
    );
}

/// **The resend cap's sibling branch, on the cache** (W-5 audit repair; `kernel_log.rs`'s `ReplayCache::replay`, §9.7):
/// a stored checkpoint whose tail has grown past the resend cap is **not** sent in one call — the call would be refused
/// `tooManyLines` — so the cache rebuilds from genesis instead, naming why. The control is a tail *under* the cap, which
/// resumes from the stored checkpoint and rebuilds nothing. Both answers are compared with the fork's whole replay.
#[test]
fn t5_a_tail_past_the_resend_cap_rebuilds_instead_of_resending() {
    let tz = chrono_tz::UTC;
    let table = table(tz);
    let lines = loggen::log(loggen::Rate::Forty, 500);
    let dir = tempfile::tempdir().expect("a temp dir");
    let cdir = dir.path().join(kernel_log::CACHE_DIR);
    let mut cache = kernel_log::ReplayCache::new(Some(cdir));
    let want = kernel_log::Want { facts: true, headers_from: None, render: vec![] };

    // A checkpoint over the first 150 days.
    let head = &lines[..40 * 150];
    let text_a = loggen::text(head);
    let ra = cache.replay(text_a.as_bytes(), day_after(head), &table, None, &want).expect("genesis answers");
    assert_eq!(ra.outcome, kernel_log::Outcome::Genesis, "{:?}", ra.rebuilt_because);
    assert_windowed("a tail under the cap: genesis", &cache, &ra, &text_a, tz, &table);

    // The control: 100 more days is a tail under the cap, so it resumes from the stored checkpoint.
    let mid = &lines[..40 * 250];
    let text_b = loggen::text(mid);
    let rb = cache.replay(text_b.as_bytes(), day_after(mid), &table, None, &want).expect("a resume answers");
    let cut_b = rb.snapshot.meta.cut as usize;
    assert!(mid.len() - (ra.snapshot.meta.cut as usize) <= kernel_log::RESEND_LINES, "this tail is under the cap");
    assert_ne!(rb.outcome, kernel_log::Outcome::Genesis, "a tail under the cap is resumed, not rebuilt");
    assert_eq!(rb.rebuilt_because, None, "nothing to rebuild");
    assert_windowed("a tail under the cap: resumed", &cache, &rb, &text_b, tz, &table);

    // The tail past the cap: 250 more days. One call cannot carry it, so the cache rebuilds.
    let text_c = loggen::text(&lines);
    assert!(lines.len() - cut_b > kernel_log::RESEND_LINES, "the tail is past the cap: {} lines", lines.len() - cut_b);
    let rc = cache.replay(text_c.as_bytes(), day_after(&lines), &table, None, &want).expect("the rebuild answers");
    assert_eq!(rc.outcome, kernel_log::Outcome::Genesis, "{:?}", rc.rebuilt_because);
    assert_eq!(rc.rebuilt_because.as_deref(), Some("a tail past the resend cap"), "named, not silent");
    assert_windowed("a tail past the cap: rebuilt", &cache, &rc, &text_c, tz, &table);
}
