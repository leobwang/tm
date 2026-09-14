//! **The zone table: Rust probes `cfg.tz`, the kernel reads a table** (stage 5
//! D9 step B4; design `kernel/design/stage5/stage5-D9-D10-design.md` §6.1, §10.1).
//!
//! The kernel carries no time-zone database. It attributes instants to local
//! days through a [`ZoneTable`]: the offset in force at 1900-01-01T00:00:00Z
//! (`base`) and every change after it up to 2200-01-01T00:00:00Z, each at its
//! UTC second (`Cal.lean`'s `TzTable`, `offsetAt`, `localDate`). chrono-tz 0.10.4
//! does not export its spans, so the table is **probed**:
//!
//! * sample `tz.offset_from_utc_datetime(t).fix().local_minus_utc()` at every
//!   UTC hour of `[1900, 2200)` — 2,629,752 samples;
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
//! {"key": "America/Chicago|2025b|1900-2200", "base": "-06:00:00",
//!  "then": [["1918-03-31T08:00:00Z", "-05:00:00"], …]}
//! ```
//!
//! Offsets are `±HH:MM:SS` with `+` at zero, instants `YYYY-MM-DDTHH:MM:SSZ`;
//! the kernel reads both with its own readers (`Boundary.lean`'s `readTz`,
//! `readTzOffset`, `readTzInstant`) and builds the table only through
//! `Cal.mkTz?`. The key names the zone, the tzdb version chrono-tz was built
//! from, and the span, so a table from another tzdb never passes for this one.
//!
//! [`wire_for`] caches the wire value under `.tm/cache/replay/tz.json` (D13),
//! keyed by that key. Nothing in the binary calls it yet: W3's `kernel_log.rs`
//! is its first caller. Until then the tests, `examples/tzprobe.rs` and
//! `logbench` (c) include this file by path, so it depends on nothing but chrono,
//! chrono-tz and serde_json.

use std::path::Path;

use chrono::{DateTime, Offset, TimeZone};
use chrono_tz::Tz;
use serde_json::{json, Value};

/// 1900-01-01T00:00:00Z as a Unix second: the table's first instant.
pub const SPAN_FROM: i64 = -2_208_988_800;
/// 2200-01-01T00:00:00Z as a Unix second: the end of the probed span.
pub const SPAN_TO: i64 = 7_258_118_400;
/// The span as the key spells it.
pub const SPAN: &str = "1900-2200";
/// The sampling step: one UTC hour.
pub const STEP: i64 = 3600;
/// The cache file's name inside the replay cache directory (D13).
pub const CACHE_FILE: &str = "tz.json";

/// A zone as the kernel reads it: the offset in force at [`SPAN_FROM`] and every
/// change after it, strictly increasing. Offsets are seconds **east** of UTC
/// (chrono's `local_minus_utc`); instants are Unix seconds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZoneTable {
    /// `<zone>|<tzdb version>|1900-2200`.
    pub key: String,
    /// Seconds east of UTC in force at 1900-01-01T00:00:00Z.
    pub base: i32,
    /// `(Unix second, seconds east)`: the offset in force from that second on.
    pub transitions: Vec<(i64, i32)>,
}

/// chrono-tz's offset at a whole UTC second. The only probe of a zone.
fn offset_at(tz: Tz, unix: i64) -> i32 {
    match DateTime::from_timestamp(unix, 0) {
        Some(dt) => tz.offset_from_utc_datetime(&dt.naive_utc()).fix().local_minus_utc(),
        // Every probed second lies in [1900, 2200], well inside chrono's range.
        None => unreachable!("a probed second is outside chrono's range"),
    }
}

/// The table's key: the zone's IANA name, chrono-tz's tzdb version and the span.
pub fn key_of(tz: Tz) -> String {
    format!("{}|{}|{}", tz.name(), chrono_tz::IANA_TZDB_VERSION, SPAN)
}

/// **Probe `tz`** over `[1900, 2200)`, hourly, each change bisected to the second.
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
}

/// **The wire value for `tz`, from the cache when its key matches, else probed.**
///
/// `cache_dir` is `.tm/cache/replay/` (D13); `None` never touches the disk. A
/// cached file whose key is not [`key_of`]`(tz)` — another zone, another tzdb, or
/// a file that does not parse — is probed afresh and overwritten. The file is
/// written to a temporary name and renamed into place; a write that fails leaves
/// the answer unchanged (the probe is the source, the file only saves it). The
/// cached value is passed on as read, never decoded: the kernel validates every
/// table it is sent (`readTz`, `Cal.mkTz?`).
pub fn wire_for(cache_dir: Option<&Path>, tz: Tz) -> Value {
    let key = key_of(tz);
    if let Some(dir) = cache_dir {
        let cached = std::fs::read(dir.join(CACHE_FILE))
            .ok()
            .and_then(|b| serde_json::from_slice::<Value>(&b).ok())
            .filter(|v| v.get("key").and_then(Value::as_str) == Some(key.as_str()));
        if let Some(v) = cached {
            return v;
        }
    }
    let wire = probe(tz).to_wire();
    if let Some(dir) = cache_dir {
        let tmp = dir.join(format!("{CACHE_FILE}.tmp{}", std::process::id()));
        let written = std::fs::create_dir_all(dir)
            .and_then(|()| std::fs::write(&tmp, wire.to_string()))
            .and_then(|()| std::fs::rename(&tmp, dir.join(CACHE_FILE)));
        if written.is_err() {
            let _ = std::fs::remove_file(&tmp);
        }
    }
    wire
}
