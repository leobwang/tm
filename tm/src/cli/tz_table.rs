//! **The zone table: Rust probes `cfg.tz`, the kernel reads a table** (stage 5
//! D9 step B4; design `kernel/design/stage5/stage5-D9-D10-design.md` §6.1, §10.1).
//!
//! The kernel carries no time-zone database. It attributes instants to local
//! days through a [`ZoneTable`]: the offset in force at 1800-01-01T00:00:00Z
//! (`base`) and every change after it up to 2200-01-01T00:00:00Z, each at its
//! UTC second (`Cal.lean`'s `TzTable`, `offsetAt`, `localDate`). chrono-tz 0.10.4
//! does not export its spans, so the table is **probed**:
//!
//! * sample `tz.offset_from_utc_datetime(t).fix().local_minus_utc()` at every
//!   UTC hour of `[1800, 2200)` — 3,506,328 samples;
//! * where a sample differs from the offset in force, bisect the hour to the
//!   second (at most 12 probes), record the change, and look again inside the
//!   same hour from there, so two changes in one hour (A → B → C) are both kept.
//!
//! **The stated assumption** (§6.1): a zone whose offset changes and changes back
//! inside one hour (A → B → A) is missed. No such pair is known in tzdb, and the
//! design does not rely on memory: `tm/tests/kernel_tz_table.rs` sweeps five zones
//! at minute resolution and checks every chrono-tz zone's transitions at −1 s, 0
//! and +1 s (T4 (c) and (d), `#[ignore]`d, run at B4 and recorded in the README).
//!
//! **This file is the one encoder of zone tables** (AGENTS §5.3): nothing else in
//! the Rust probes a zone for the kernel, and the wire shape is written only by
//! [`ZoneTable::to_wire`]:
//!
//! ```text
//! {"key": "America/Chicago|2025b|1800-2200", "base": "-05:50:36",
//!  "then": [["1883-11-18T18:00:00Z", "-06:00:00"], …]}
//! ```
//!
//! Offsets are `±HH:MM:SS` with `+` at zero, instants `YYYY-MM-DDTHH:MM:SSZ`;
//! the kernel reads both with its own readers (`Boundary.lean`'s `readTz`,
//! `readTzOffset`, `readTzInstant`) and builds the table only through
//! `Cal.mkTz?`. The key names the zone, the tzdb version chrono-tz was built
//! from, and the span, so a table from another tzdb never passes for this one.
//!
//! [`wire_for`] caches the wire value under `.tm/cache/replay/tz.json` (D13),
//! keyed by that key, and since the W-44 repair opening with a digest of its own
//! text ([`cache_text`]). Nothing in the binary calls it yet: W3's `kernel_log.rs`
//! is its first caller. Until then the tests, `examples/tzprobe.rs` and
//! `logbench` (c) include this file by path, so it depends on nothing but chrono,
//! chrono-tz, serde_json and `tm_core`'s one FNV-1a body (`tm_core::fnv`).
//!
//! **A served table is CHECKED against the binary's own zone database first, and a
//! table that disagrees is rebuilt, never served** (the owner's D104, README gaps
//! 4621 and 4711; stage 6 W-46 track H). The digest says a file is the one its
//! writer wrote; it cannot say the writer was this binary, and a hand edit that
//! recomputes the digest — or a binary whose probe read its zone another way under
//! the same key — passed until D104 as "trusted as written". The check
//! ([`agrees`]) covers EVERY second the kernel can read through the table, not
//! only the day it plans: the kernel attributes every log line to a local day
//! through it (genesis replays the whole log, a hand-edited line can carry any
//! instant), so the history, the planned day and the lookahead are all of
//! `[1800, 2200]`. It is cheaper than the probe it saves because a table that
//! agrees with chrono-tz at each of its own transitions and on a one-day grid
//! agrees everywhere, given that every span of every zone outlasts the grid's step
//! ([`CHECK_STEP`]; measured, and held by `cli_tz_cache_digest`'s sweep of every
//! zone).

use std::path::Path;

use chrono::{DateTime, Offset, TimeZone};
use chrono_tz::Tz;
use serde_json::{json, Value};

/// 1800-01-01T00:00:00Z as a Unix second: the table's first instant.
///
/// **Before every zone's first change** (the W-46 audit, README gap 4902): tzdb's earliest
/// transition is Asia/Manila's date-line change of 1844, so `base` is each zone's local mean time
/// and the table reads chrono-tz's offset at EVERY second before [`SPAN_TO`], the kernel's whole
/// calendar from 0001-01-01 included. Until the audit the span began in 1900, where America/Chicago
/// had kept CST since 1883: the table read every earlier second at `-06:00:00` while chrono-tz reads
/// local mean time (`-05:50:36`) before 1883-11-18, so after R3 a `--now` before then planned a
/// day the host decoded in another offset, and `tm plan`, `tm now`, `tm check` and `tm review day`
/// faulted (`plan.hash`), where the fork's planner, which never read the table, planned it.
pub const SPAN_FROM: i64 = -5_364_662_400;
/// 2200-01-01T00:00:00Z as a Unix second: the end of the probed span.
pub const SPAN_TO: i64 = 7_258_118_400;
/// The span as the key spells it.
pub const SPAN: &str = "1800-2200";
/// The sampling step: one UTC hour.
pub const STEP: i64 = 3600;
/// The cache file's name inside the replay cache directory (D13).
pub const CACHE_FILE: &str = "tz.json";
/// **The step of [`agrees`]' grid: one day** (the owner's D104). A table that reads chrono-tz's
/// offset at each of its own transitions (both sides of each) and at every point of this grid reads
/// it at every second of the span, PROVIDED every span of the zone — the time between two of its
/// changes, or between a change and an end of the span — is longer than this step: a change the
/// table lacks then opens a span that holds a grid point, where the two disagree. Measured over
/// every zone of the binary's chrono-tz (0.10.4, tzdb 2025b, 597 zones): the shortest span is
/// 601,200 s (America/Boa_Vista, Noronha and Recife in October 2000; Gaza and Hebron in 2040,
/// 2054 and 2072), so the step has a margin of seven, and `cli_tz_cache_digest`'s sweep of every
/// zone fails the day a chrono-tz upgrade brings a span that does not outlast it.
pub const CHECK_STEP: i64 = 86_400;

/// A zone as the kernel reads it: the offset in force at [`SPAN_FROM`] and every
/// change after it, strictly increasing. Offsets are seconds **east** of UTC
/// (chrono's `local_minus_utc`); instants are Unix seconds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZoneTable {
    /// `<zone>|<tzdb version>|1800-2200`.
    pub key: String,
    /// Seconds east of UTC in force at 1800-01-01T00:00:00Z.
    pub base: i32,
    /// `(Unix second, seconds east)`: the offset in force from that second on.
    pub transitions: Vec<(i64, i32)>,
}

/// chrono-tz's offset at a whole UTC second. The only probe of a zone.
fn offset_at(tz: Tz, unix: i64) -> i32 {
    match DateTime::from_timestamp(unix, 0) {
        Some(dt) => tz.offset_from_utc_datetime(&dt.naive_utc()).fix().local_minus_utc(),
        // Every probed second lies in [1800, 2200], well inside chrono's range.
        None => unreachable!("a probed second is outside chrono's range"),
    }
}

/// The table's key: the zone's IANA name, chrono-tz's tzdb version and the span.
pub fn key_of(tz: Tz) -> String {
    format!("{}|{}|{}", tz.name(), chrono_tz::IANA_TZDB_VERSION, SPAN)
}

/// **Probe `tz`** over `[1800, 2200)`, hourly, each change bisected to the second.
pub fn probe(tz: Tz) -> ZoneTable {
    let base = offset_at(tz, SPAN_FROM);
    let mut transitions = Vec::new();
    let mut cur = base;
    let mut lo = SPAN_FROM;
    let mut t = SPAN_FROM + STEP;
    while t <= SPAN_TO {
        let seen = offset_at(tz, t);
        while seen != cur {
            // offset(lo) == cur and offset(t) != cur: bisect (lo, t].
            let (mut a, mut b) = (lo, t);
            while b - a > 1 {
                let m = a + (b - a) / 2;
                if offset_at(tz, m) == cur {
                    a = m;
                } else {
                    b = m;
                }
            }
            cur = offset_at(tz, b);
            transitions.push((b, cur));
            lo = b;
        }
        lo = t;
        t += STEP;
    }
    ZoneTable { key: key_of(tz), base, transitions }
}

/// `±HH:MM:SS`, `+` at zero: the one spelling `readTzOffset` reads.
pub fn fmt_offset(east: i32) -> String {
    let sign = if east < 0 { '-' } else { '+' };
    let a = east.unsigned_abs();
    format!("{sign}{:02}:{:02}:{:02}", a / 3600, a / 60 % 60, a % 60)
}

/// `YYYY-MM-DDTHH:MM:SSZ` for a Unix second.
pub fn fmt_instant(unix: i64) -> String {
    match DateTime::from_timestamp(unix, 0) {
        Some(dt) => dt.format("%Y-%m-%dT%H:%M:%SZ").to_string(),
        None => unreachable!("a table instant is outside chrono's range"),
    }
}

impl ZoneTable {
    /// **The wire value** (design §10.1's `tz`), keys in the kernel's order.
    pub fn to_wire(&self) -> Value {
        let then: Vec<Value> =
            self.transitions.iter().map(|&(t, o)| json!([fmt_instant(t), fmt_offset(o)])).collect();
        json!({ "key": self.key, "base": fmt_offset(self.base), "then": then })
    }

    /// **The table a wire value holds, when the value is exactly what [`ZoneTable::to_wire`] writes
    /// for one** — else `None` (the owner's D104). The kernel is the zone wire's reader (`readTz`);
    /// this is no second grammar for it (AGENTS §5.3): the table read is accepted only when writing it
    /// back gives the value read — ONE check, which the two field readers do not restate — so nothing
    /// is read that the one encoder could not have written, and a key, an element or a spelling it
    /// would not write is a table that disagrees.
    pub fn from_wire(v: &Value) -> Option<ZoneTable> {
        let o = v.as_object()?;
        let base = offset_of(o.get("base")?.as_str()?)?;
        let mut transitions = Vec::new();
        for p in o.get("then")?.as_array()? {
            match p.as_array()?.as_slice() {
                [t, off] => transitions.push((instant_of(t.as_str()?)?, offset_of(off.as_str()?)?)),
                _ => return None,
            }
        }
        let table = ZoneTable { key: o.get("key")?.as_str()?.to_string(), base, transitions };
        (table.to_wire() == *v).then_some(table)
    }
}

/// [`fmt_offset`] read back: the seconds east `±HH:MM:SS` spells. Whether the text is the encoder's own spelling is
/// [`ZoneTable::from_wire`]'s one check (the table written back must be the value read), not restated here.
fn offset_of(s: &str) -> Option<i32> {
    let (neg, rest) = match s.as_bytes().first()? {
        b'+' => (false, &s[1..]),
        b'-' => (true, &s[1..]),
        _ => return None,
    };
    let mut parts = rest.split(':').map(|p| p.parse::<i32>().ok());
    let (h, m, sec) = (parts.next()??, parts.next()??, parts.next()??);
    let east = h.checked_mul(3600)?.checked_add(m.checked_mul(60)?)?.checked_add(sec)?;
    let east = if neg { east.checked_neg()? } else { east };
    Some(east)
}

/// [`fmt_instant`] read back: the Unix second `YYYY-MM-DDTHH:MM:SSZ` spells — the encoder's spelling is
/// [`ZoneTable::from_wire`]'s check, as for [`offset_of`].
fn instant_of(s: &str) -> Option<i64> {
    Some(chrono::NaiveDateTime::parse_from_str(s, "%Y-%m-%dT%H:%M:%SZ").ok()?.and_utc().timestamp())
}

/// **Whether `table` reads, at every second of `[1800, 2200]`, the offset the binary's own zone
/// database reads for `tz`** — the owner's D104's check, which a served table must pass. The kernel
/// reads the table at every instant a log line carries (its whole history at a genesis, and a
/// hand-edited line can carry any instant), at the day it plans, at every day of the lookahead and
/// at the walls of each, so the check is the whole span, not the planned day. Three things are
/// asked, each of chrono-tz at a Unix second ([`offset_at`], the probe's own question):
///
/// * the key is [`key_of`]`(tz)` and the base is the offset at [`SPAN_FROM`];
/// * every transition is a change of the zone at that very second, inside the span and in order —
///   the second before reads the offset the table had, the second itself reads the new one, and the
///   two differ;
/// * on a grid of [`CHECK_STEP`] from `SPAN_FROM`, and at [`SPAN_TO`], the table reads the zone's
///   offset.
///
/// The first two say every change the table holds is a change of the zone; the third, with every
/// span of the zone longer than the step, says the table lacks none: a change the table lacks opens
/// a span of the zone that holds a grid point, and the table reads its old offset there. So a table
/// this accepts is the probe's table ([`probe`]) — the same transitions, and the same key — and a
/// table it refuses disagrees with the zone at a second the kernel may read. 109,574 grid points
/// and two questions a transition, where the probe asks 2,629,752 and bisects.
pub fn agrees(tz: Tz, table: &ZoneTable) -> bool {
    if table.key != key_of(tz) || table.base != offset_at(tz, SPAN_FROM) {
        return false;
    }
    let (mut before, mut lo) = (table.base, SPAN_FROM);
    for &(t, o) in &table.transitions {
        if t <= lo || t > SPAN_TO || o == before || offset_at(tz, t - 1) != before || offset_at(tz, t) != o {
            return false;
        }
        (before, lo) = (o, t);
    }
    let (mut next, mut reads) = (0, table.base);
    let mut at = SPAN_FROM;
    loop {
        while let Some(&(_, o)) = table.transitions.get(next).filter(|&&(t, _)| t <= at) {
            (reads, next) = (o, next + 1);
        }
        if reads != offset_at(tz, at) {
            return false;
        }
        if at == SPAN_TO {
            return true;
        }
        at = (at + CHECK_STEP).min(SPAN_TO);
    }
}

/// What the cached `tz.json` opens with since the W-44 repair: the digest of the rest of its text.
const DIGEST_HEAD: &str = "{\"digest\":\"";

/// **The text of `tz.json`, opening with the digest of the rest of itself** (the W-44 repair,
/// README gap 4613): `{"digest":"<16 hex>",` and then the wire value's text after its `{`, through a
/// final newline — exactly the bytes the digest is taken over, FNV-1a-64 in the binary's one body
/// (`tm_core::fnv`). The owner's D93 gave every sealed month file of `.tm/cache/replay/` a digest and
/// the campaign's D98 gave the checkpoint one; this is the third file of that directory, and the one
/// a corrupted byte of moved a day's minutes onto another date with nothing said (driven: one
/// offset of the table changed, its key kept — every verb refused `nowDisagrees` at 23:58 and, at
/// 00:10, the evening's twenty minutes were credited to the next day).
pub fn cache_text(wire: &Value) -> String {
    let text = wire.to_string();
    let body = format!("{}\n", text.strip_prefix('{').unwrap_or(&text));
    format!("{DIGEST_HEAD}{}\",{body}", tm_core::fnv::fnv1a64_hex(body.as_bytes()))
}

/// **`tz.json` read back**: its wire value when the digest it opens with is the digest of the rest of
/// it, else `None` — a file written before the digest, a byte changed on disk or by hand, or a text
/// that is not this shape, each probed afresh and overwritten ([`wire_for`]), never served.
pub fn from_cache_text(text: &str) -> Option<Value> {
    let rest = text.strip_prefix(DIGEST_HEAD)?;
    let (hex, body) = (rest.get(..16)?, rest.get(16..)?.strip_prefix("\",")?);
    if tm_core::fnv::fnv1a64_hex(body.as_bytes()) != hex {
        return None;
    }
    serde_json::from_str::<Value>(&format!("{{{body}")).ok()
}

/// **The last `tz.json` text this process found to be its own table, and the value served for it** (the
/// owner's D104). The zone database a binary carries does not change while it runs, so a text the check
/// accepted for a zone is accepted again without being checked again: a verb that reads the zone table
/// three or four times (its load's replay, its capacity or planner request, a reload) and the TUI at every
/// reload pay the check once. Keyed by the zone and the WHOLE text, so a byte changed on disk is a text
/// this has not seen, and is checked.
static SERVED: std::sync::Mutex<Option<(Tz, String, Value)>> = std::sync::Mutex::new(None);

/// **The value `text` serves for `tz`, when it serves one**: its digest matches the rest of it
/// ([`from_cache_text`]), it is exactly what the one encoder writes for a table ([`ZoneTable::from_wire`]),
/// and that table is the binary's ([`agrees`]) — else `None`, and [`wire_for`] probes.
fn served(tz: Tz, text: &str) -> Option<Value> {
    let mut last = SERVED.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some((_, _, v)) = last.as_ref().filter(|(z, t, _)| *z == tz && t == text) {
        return Some(v.clone());
    }
    let table = from_cache_text(text).and_then(|v| ZoneTable::from_wire(&v)).filter(|t| agrees(tz, t))?;
    let wire = table.to_wire();
    *last = Some((tz, text.to_string(), wire.clone()));
    Some(wire)
}

/// **The wire value for `tz`, from the cache when it is this binary's table, else probed.**
///
/// `cache_dir` is `.tm/cache/replay/` (D13); `None` never touches the disk. A
/// cached file whose key is not [`key_of`]`(tz)` — another zone, another tzdb, or
/// a file that does not parse — is probed afresh and overwritten, and since the
/// W-44 repair so is one whose text does not match the digest it opens with
/// ([`from_cache_text`], README gap 4613: D93's rule for the replay cache's
/// other files). **Since the owner's D104 so is one whose table disagrees with the
/// binary's own zone database at any second of the span** ([`agrees`], README gaps
/// 4621 and 4711): a digest says the file is what its writer wrote, never that the
/// writer read the zone as this binary does, so a hand edit with its digest
/// recomputed is rebuilt and not served — and every request reaches its table
/// through this one function (the capacity and planner request, the walls request,
/// every replay, `tm check`'s log sweep), so one check covers them all. The file is
/// written to a temporary name and renamed into place; a write that fails leaves
/// the answer unchanged (the probe is the source, the file only saves it), so an
/// unwritable cache is rebuilt in memory and never served either (D93's path). The
/// value served is the checked table written back ([`ZoneTable::to_wire`]), which
/// is the value read: the kernel still validates every table it is sent (`readTz`,
/// `Cal.mkTz?`).
pub fn wire_for(cache_dir: Option<&Path>, tz: Tz) -> Value {
    if let Some(dir) = cache_dir {
        if let Some(v) = std::fs::read_to_string(dir.join(CACHE_FILE)).ok().and_then(|t| served(tz, &t)) {
            return v;
        }
    }
    let wire = probe(tz).to_wire();
    if let Some(dir) = cache_dir {
        let tmp = dir.join(format!("{CACHE_FILE}.tmp{}", std::process::id()));
        let written = std::fs::create_dir_all(dir)
            .and_then(|()| std::fs::write(&tmp, cache_text(&wire)))
            .and_then(|()| std::fs::rename(&tmp, dir.join(CACHE_FILE)));
        if written.is_err() {
            let _ = std::fs::remove_file(&tmp);
        }
    }
    wire
}
