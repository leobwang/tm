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

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

#[allow(dead_code)]
#[path = "support/loggen.rs"]
mod loggen;

#[allow(dead_code)]
#[path = "support/replay.rs"]
mod replay;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::{Mutex, OnceLock};

use chrono::{DateTime, Datelike, Duration, FixedOffset, NaiveDate, TimeZone, Timelike, Utc};
use chrono_tz::Tz;
use serde_json::{json, Value};
use tm_core::log::{Event, Interruption, LogEntry, Replay, SegmentKind};

/// How many generated sequences T5 runs (design §14.4).
const SEQUENCES: u64 = 256;

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

/// C3: one day's block fields (`DayReplay`). Segments are the block family's
/// kinds, `(start, end, kind, id)`, in `DayReplay::segments`' order.
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
    segments: Vec<(Stamp, Stamp, String, Option<String>)>,
}

impl DayBlock {
    /// What `DayReplay::new` holds: a day created by an arm of another family.
    fn empty() -> DayBlock {
        DayBlock { by_ci: vec![0; 6], ..DayBlock::default() }
    }
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

/// **C3: the block family.** `days` holds every day the reader created; the
/// kernel creates only the days a block-family arm touches, so [`assert_parity`]
/// requires the kernel's days to be the Rust's days, less days whose block
/// fields are all [`DayBlock::empty`]. `energy` is the start observations
/// (`from_start`); the `energy` event's are C5's.
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
fn j_interrupt(v: &Value) -> InterruptRow {
    let a = j_arr(v, "an interruption");
    (
        j_opt(&a[0], j_stamp),
        j_opt(&a[1], j_stamp),
        a[2].as_i64().expect("day"),
        j_opt(&a[3], |x| j_str(x, "id")),
        j_u64(&a[4], "lost"),
        j_strs(&a[5], "dropped"),
    )
}

/// The kernel's `facts.block`. Maps are read as maps and a repeated key fails.
fn kernel_block(b: &Value) -> Block {
    let mut days = BTreeMap::new();
    for p in j_arr(&b["days"], "block.days") {
        let p = j_arr(p, "a day");
        let o = &p[1];
        let mut ci_unknown = BTreeMap::new();
        for c in j_arr(&o["ciUnknown"], "ciUnknown") {
            let c = j_arr(c, "a ciUnknown pair");
            assert!(ci_unknown.insert(j_str(&c[0], "id"), j_u64(&c[1], "min")).is_none(), "a repeated ciUnknown id: {o}");
        }
        let day = DayBlock {
            first_start: j_opt(&o["firstStart"], j_stamp),
            starts: j_arr(&o["starts"], "starts")
                .iter()
                .map(|r| {
                    let r = j_arr(r, "a start");
                    (j_stamp(&r[0]), j_str(&r[1], "id"), j_u64(&r[2], "pred"), j_opt(&r[3], |x| j_u64(x, "rep")))
                })
                .collect(),
            block_min: j_u64(&o["blockMin"], "blockMin"),
            blocks_done: j_u64(&o["blocksDone"], "blocksDone"),
            load_fifths: j_u64(&o["loadFifths"], "loadFifths"),
            by_ci: j_arr(&o["byCi"], "byCi").iter().map(|c| j_u64(c, "byCi")).collect(),
            ci_unknown,
            done: j_strs(&o["done"], "done"),
            lost_min: j_u64(&o["lostMin"], "lostMin"),
            dropped: j_strs(&o["dropped"], "dropped"),
            segments: j_arr(&o["segments"], "segments")
                .iter()
                .map(|g| {
                    let g = j_arr(g, "a segment");
                    (j_stamp(&g[0]), j_stamp(&g[1]), j_str(&g[2], "kind"), j_opt(&g[3], |x| j_str(x, "id")))
                })
                .collect(),
        };
        assert!(days.insert(p[0].as_i64().expect("a day"), day).is_none(), "a repeated day");
    }
    let mut items: BTreeMap<String, ItemBlock> = BTreeMap::new();
    for p in j_arr(&b["items"], "block.items") {
        let p = j_arr(p, "an item");
        let o = &p[1];
        let item = ItemBlock {
            minutes: j_u64(&o["minutes"], "minutes"),
            blocks: j_u64(&o["blocks"], "blocks"),
            by_day: BTreeMap::new(),
            done_at: j_arr(&o["doneAt"], "doneAt").iter().map(j_stamp).collect(),
            partial_done_at: j_arr(&o["partialDoneAt"], "partialDoneAt").iter().map(j_stamp).collect(),
            stops: j_u64(&o["stops"], "stops"),
            extended_min: j_u64(&o["extendedMin"], "extendedMin"),
        };
        assert!(items.insert(j_str(&p[0], "id"), item).is_none(), "a repeated item");
    }
    for p in j_arr(&b["itemDays"], "block.itemDays") {
        let p = j_arr(p, "an item day");
        let item = items.entry(j_str(&p[0], "id")).or_default();
        assert!(item.by_day.insert(p[1].as_i64().expect("day"), j_u64(&p[2], "min")).is_none(), "a repeated item day");
    }
    Block {
        days,
        items,
        energy: j_arr(&b["energy"], "energy")
            .iter()
            .map(|o| {
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
            })
            .collect(),
        durations: j_arr(&b["durations"], "durations")
            .iter()
            .map(|o| {
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
            })
            .collect(),
        interrupts: j_arr(&b["interrupts"], "interrupts").iter().map(j_interrupt).collect(),
        open_block: j_opt(&b["openBlock"], |o| {
            let o = j_arr(o, "the open block");
            (j_str(&o[0], "id"), j_stamp(&o[1]), j_u64(&o[2], "worked"), j_opt(&o[3], j_stamp), o[4].as_bool().expect("paused"))
        }),
        open_interrupt: j_opt(&b["openInterrupt"], j_interrupt),
        last_effective: j_opt(&b["lastEffective"], j_stamp),
    }
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
                        .filter_map(|g| {
                            let (kind, id) = match &g.kind {
                                SegmentKind::Block { id } => ("block", Some(id.clone())),
                                SegmentKind::Pause { id } => ("pause", Some(id.clone())),
                                SegmentKind::Interrupt { id } => ("interrupt", id.clone()),
                                _ => return None,
                            };
                            Some((stamp_of(&g.start), stamp_of(&g.end), kind.to_string(), id))
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
            .filter(|o| o.from_start)
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

/// **The kernel's facts**: one genesis `log` call over the whole text, lines
/// split on `\n` as the in-tree reader's `parse_bytes` splits them.
fn kernel_facts(text: &str, tz: Tz) -> Facts {
    let segs: Vec<Value> = text.split('\n').map(|s| Value::String(s.to_string())).collect();
    assert!(segs.len() <= 32_768, "T5 sends one call; W3's chunked genesis is not built yet");
    let req = json!({
        "docs": [], "tz": table(tz),
        "log": {"ckpt": null, "from": 1, "lines": segs, "terminated": text.ends_with('\n'),
                "reseal": null, "want": {"facts": true}}
    });
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("the response is JSON");
    let facts = &resp["ok"]["log"]["facts"];
    assert!(facts.is_object(), "no facts: {}", &raw[..raw.len().min(400)]);
    Facts {
        cancelled: facts["cancelled"]
            .as_array()
            .expect("facts.cancelled")
            .iter()
            .map(|n| n.as_u64().expect("a line"))
            .collect(),
        days: facts["days"]
            .as_array()
            .expect("facts.days")
            .iter()
            .map(|p| {
                let p = p.as_array().expect("a [line, day] pair");
                assert_eq!(p.len(), 2, "a [line, day] pair");
                (p[0].as_u64().expect("a line"), p[1].as_i64().expect("a day"))
            })
            .collect(),
        block: kernel_block(&facts["block"]),
        warnings: resp["ok"]["log"]["warnings"]
            .as_array()
            .expect("warnings")
            .iter()
            .map(|w| w["line"].as_u64().expect("a line"))
            .collect(),
    }
}

/// **The Rust's facts**, through the test chokepoint.
fn rust_facts(text: &str, tz: Tz) -> Facts {
    let r = replay::replay_of_text(text, tz);
    Facts {
        cancelled: r.view().iter().filter(|row| row.cancelled).map(|row| row.line).collect(),
        days: r.view().iter().map(|row| (row.line, day_number(row.day))).collect(),
        block: rust_block(&r),
        warnings: replay::warning_lines_of_text(text),
    }
}

/// Compare one log; the kernel's facts are returned for the arms' own checks.
fn assert_parity(name: &str, text: &str, tz: Tz) -> Facts {
    let (k, mut r) = (kernel_facts(text, tz), rust_facts(text, tz));
    // C3: a day the kernel's block family did not create must be one another
    // family created in the Rust (its block fields all `DayReplay::new`'s), and
    // every day the kernel created must exist in the Rust.
    for d in k.block.days.keys() {
        assert!(r.block.days.contains_key(d), "{name} ({}): the kernel created block day {d}, the Rust has no such day", tz.name());
    }
    r.block.days.retain(|d, b| k.block.days.contains_key(d) || *b != DayBlock::empty());
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
    assert_eq!(k, r, "{name}");
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
}

impl Tally {
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
            "block family: {} days ({} segments, {} ci-unknown pairs), {} items ({} item days), {} start observations, {} durations, {} interruptions, {} open blocks, {} open interruptions",
            self.days, self.segments, self.ci_unknown, self.items, self.item_days, self.energy, self.durations, self.interrupts, self.open_blocks, self.open_interrupts
        )
    }
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
}

const ARMS: [Arm; 17] = [
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
    Generated { tz, text: w.text(), arms, silent_targets, housekeeping, edges }
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
        out.push(ZoneCase { name: "fall-back 01:30 twice".to_string(), text: w.text(), tz: chicago, expect });
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
        out.push(ZoneCase { name: format!("wake after midnight under 24h, {label}"), text: w.text(), tz: chicago, expect });
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
        out.push(ZoneCase { name: format!("23-25h after a wake, {label} transition"), text: w.text(), tz: chicago, expect });
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
            out.push(ZoneCase { name: format!("fold at midnight, {}, {label}", tz.name()), text: w.text(), tz, expect });
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
        out.push(ZoneCase { name: "offsets -05:00 then +02:00".to_string(), text: w.text(), tz: chicago, expect });
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
        out.push(ZoneCase { name: "cfg.tz Chicago, written in Berlin".to_string(), text: w.text(), tz: chicago, expect });
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
        out.push(ZoneCase { name: "a :60 stamp at the 24-hour edge".to_string(), text: w.text(), tz, expect });
    }
    out
}

// ---------------------------------------------------------------------------
// The tests.

/// The seven corpus logs.
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
        cancelled += k.cancelled.len();
        days += k.days.len();
        off += off_their_own_date(&text, chrono_tz::America::Chicago);
        tally.add(&k.block);
    }
    assert!(tally.durations > 0 && tally.items > 0, "the corpus has blocks");
    eprintln!("T5 corpus: 7 logs, {cancelled} cancelled lines, {days} days compared ({off} off their own local date); {tally}; 0 exceptions");
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
        eprintln!(
            "T5 {label}: {} lines, {} bytes, {} cancelled, {} days compared ({} off their own local date); {tally}; {ms:.0} ms for both readers, 0 exceptions",
            lines.len(),
            text.len(),
            k.cancelled.len(),
            k.days.len(),
            off_their_own_date(&text, chrono_tz::America::Chicago),
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
    for seed in 0..SEQUENCES {
        let g = generate(seed);
        let k = assert_parity(&format!("sequence {seed}"), &g.text, g.tz);
        tally.add(&k.block);
        for e in &g.edges {
            *edges.entry(*e).or_default() += 1;
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
    eprintln!(
        "T5 sequences: {SEQUENCES} logs, {lines} lines, {cancelled} cancelled, {days} days compared ({off} off their own local date), {silent} silent-verb undos \
         cancelling an older move, {auto} week closes left standing by an undo that took the automatic close; {tally}; block edge cases {edges:?}; arms {counts:?}; zones {zones:?}; 0 exceptions"
    );
}

/// **T5 over §6.4's zone cases**, each its own arm, with the days each case
/// names checked against the kernel's facts.
#[test]
fn t5_the_zone_cases_replay_as_the_fork_does() {
    let cases = zone_cases();
    let (mut days, mut named, mut off, mut tally) = (0, 0, 0, Tally::default());
    for c in &cases {
        let k = assert_parity(&c.name, &c.text, c.tz);
        tally.add(&k.block);
        assert!(!k.cancelled.is_empty(), "{}: every zone case carries an undo", c.name);
        for (line, d) in &c.expect {
            assert_eq!(day_of_line(&k, *line), day_number(*d), "{}: line {line} should be on {d}", c.name);
            named += 1;
        }
        days += k.days.len();
        off += off_their_own_date(&c.text, c.tz);
    }
    eprintln!(
        "T5 zone cases: {} ({:?}), {days} days compared, {named} named days checked, {off} entries off their own local date; {tally}; 0 exceptions",
        cases.len(),
        cases.iter().map(|c| &c.name).collect::<Vec<_>>()
    );
}

/// The generator is deterministic: a sequence is its seed.
#[test]
fn t5_a_sequence_is_its_seed() {
    assert_eq!(generate(41).text, generate(41).text);
    assert_ne!(generate(41).text, generate(42).text);
}

/// **The fast twin on a hostile log** (Replay.lean's `survivors_eq_survivorsFast`,
/// rule D9-21): 5,000 `done`s of distinct ids, then 2,500 undos of ids nothing
/// carries and 2,500 of a tag nothing carries. The specification's `eraseP` scans
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
    for i in 0..5_000 {
        w.push(t0, ev_done(&format!("i{i}"), 30, false));
    }
    for i in 0..2_500 {
        w.push(t0, ev_undo("done", Some(&format!("absent{i}"))));
    }
    for _ in 0..2_500 {
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
    assert_eq!(k.cancelled.len(), 5_000);
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
