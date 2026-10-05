//! **T4: chrono and the zone table are two evaluators, tied together** (stage 5
//! D9 step B4; design `kernel/design/stage5/stage5-D9-D10-design.md` §6.1, §6.4,
//! §14.2 row B4; CRIT 11).
//!
//! `tm/src/cli/tz_table.rs` probes a zone hourly and bisects each change to the
//! second; the kernel reads the table (`Boundary.lean`'s `readTz`, built only by
//! `Cal.mkTz?`) and takes the offset of an instant as the last transition at or
//! before its second, else the base (`Cal.offsetAt`, proved to read exactly that:
//! `offsetAt_reads_the_last_transition`). [`table_offset`] is that rule, so each
//! test below compares chrono with the table under the kernel's lookup, and sends
//! the table to the kernel, which must accept it.
//!
//! * (a) 10,000 seeded instants over [1970, 2100) in each of five zones;
//! * (b) every transition of those zones at −1 s, 0 and +1 s;
//! * (c) `#[ignore]`: the five zones at every minute of [1900, 2200) (the span is [1800, 2200) since the W-46 audit; this sweep's range is B4's, recorded);
//! * (d) `#[ignore]`: every chrono-tz zone, its transitions in [1970, 2100) at
//!   ±1 s, the kernel accepting its table, and B1's scan assumption (below).
//!
//! (c) and (d) are run once at B4 and their results recorded in kernel/README.md.

#[allow(dead_code)]
#[path = "support/fnv.rs"]
mod fnv;

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

use chrono::{DateTime, Offset, TimeZone};
use chrono_tz::Tz;
use serde_json::{json, Value};
use tz_table::ZoneTable;

/// Chicago, Berlin, Kolkata (+05:30), Chatham (+12:45) and Lord Howe (a 30-minute
/// DST): design §6.4's five.
const FIVE: [Tz; 5] = [
    chrono_tz::America::Chicago,
    chrono_tz::Europe::Berlin,
    chrono_tz::Asia::Kolkata,
    chrono_tz::Pacific::Chatham,
    chrono_tz::Australia::Lord_Howe,
];

/// 1970-01-01 and 2100-01-01 as Unix seconds.
const Y1970: i64 = 0;
const Y2100: i64 = 4_102_444_800;

fn chrono_offset(tz: Tz, unix: i64) -> i32 {
    let dt = DateTime::from_timestamp(unix, 0).expect("in range").naive_utc();
    tz.offset_from_utc_datetime(&dt).fix().local_minus_utc()
}

/// `Cal.offsetAt`: the last transition at or before `unix`, else the base.
fn table_offset(t: &ZoneTable, unix: i64) -> i32 {
    let i = t.transitions.partition_point(|&(s, _)| s <= unix);
    if i == 0 {
        t.base
    } else {
        t.transitions[i - 1].1
    }
}

/// The kernel reads `table`: a `log` call with no lines must answer `ok`.
fn kernel_accepts(table: &ZoneTable) {
    let req = json!({"docs": [], "tz": table.to_wire(),
                     "log": {"from": 1, "lines": [], "terminated": true}});
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert_eq!(resp["ok"]["log"]["lines"], 0, "{}: {raw}", table.key);
}

fn splitmix(x: &mut u64) -> u64 {
    *x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *x;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// The table's shape: the key, strictly increasing whole seconds inside the
/// span, no transition that does not change the offset, at most 4,096.
fn well_formed(t: &ZoneTable, tz: Tz) {
    assert_eq!(t.key, tz_table::key_of(tz));
    assert!(t.transitions.len() <= 4096, "{}: {}", t.key, t.transitions.len());
    let mut prev = (tz_table::SPAN_FROM, t.base);
    for &(s, o) in &t.transitions {
        assert!(s > prev.0 && s <= tz_table::SPAN_TO, "{}: {s}", t.key);
        assert_ne!(o, prev.1, "{}: a transition at {s} changes nothing", t.key);
        assert!(o.unsigned_abs() < 86_400);
        prev = (s, o);
    }
}

/// **T4 (a).** 10,000 seeded instants over [1970, 2100) in each zone.
#[test]
fn the_table_is_chronos_offset_at_random_instants() {
    let mut seed = 2026;
    for tz in FIVE {
        let t = tz_table::probe(tz);
        well_formed(&t, tz);
        kernel_accepts(&t);
        for _ in 0..10_000 {
            let unix = Y1970 + (splitmix(&mut seed) % (Y2100 - Y1970) as u64) as i64;
            assert_eq!(table_offset(&t, unix), chrono_offset(tz, unix), "{} at {unix}", t.key);
        }
    }
}

/// **T4 (b).** Every transition of the five zones, at −1 s, 0 and +1 s, over the
/// whole span.
#[test]
fn the_table_is_chronos_offset_at_every_transition() {
    let mut n = 0;
    for tz in FIVE {
        let t = tz_table::probe(tz);
        assert_eq!(t.base, chrono_offset(tz, tz_table::SPAN_FROM), "{}", t.key);
        for &(s, _) in &t.transitions {
            for d in [-1, 0, 1] {
                assert_eq!(table_offset(&t, s + d), chrono_offset(tz, s + d), "{} at {s}{d:+}", t.key);
            }
            n += 1;
        }
    }
    assert!(n > 1000, "{n} transitions");
}

/// The wire spelling (design §10.1): Chicago's base is its local mean time,
/// −05:50:36, which it left at 12:09:24 local on 1883-11-18 for −06:00:00 (the span
/// begins in 1800 since the W-46 audit, README gap 4902: before every zone's first
/// change); its next transition is 1918's; offsets are `±HH:MM:SS` with `+` at
/// zero, instants `…Z`.
#[test]
fn the_wire_table_is_spelled_as_the_kernel_reads_it() {
    let w = tz_table::probe(chrono_tz::America::Chicago).to_wire();
    assert_eq!(w["base"], "-05:50:36");
    assert_eq!(w["then"][0], json!(["1883-11-18T18:00:00Z", "-06:00:00"]));
    assert_eq!(w["then"][1], json!(["1918-03-31T08:00:00Z", "-05:00:00"]));
    assert_eq!(tz_table::fmt_offset(0), "+00:00:00");
    assert_eq!(tz_table::fmt_offset(-2670), "-00:44:30");
    assert_eq!(tz_table::fmt_offset(45_900), "+12:45:00");
    let keys: Vec<&String> = w.as_object().expect("object").keys().collect();
    assert_eq!(keys.len(), 3);
    assert!(w["key"].as_str().expect("key").starts_with("America/Chicago|"));
}

/// The cache (D13): a first call probes and writes the wire value — since the W-44 repair as a text
/// opening with the digest of the rest of itself (`cache_text`, README gap 4613); a file whose table is
/// the binary's is read and not re-probed — the file is never rewritten, so it keeps its inode (a probe
/// renames a new file into place); a file with another key, one that does not parse, one written before
/// the digest and one whose digest does not match its text are probed afresh and overwritten; no
/// directory touches no disk. **Since the owner's D104** (stage 6 W-46 track H, README gaps 4621 and
/// 4711) a file with the right key and a matching digest whose table the binary's own zone database
/// does not read — the doctored table below, Kolkata with no transitions — is probed afresh and
/// overwritten too. Until W-46 this test asserted the opposite of that one ("a matching key and digest
/// is read, not re-probed", served as written): the sentence D104 withdraws, and this test's other
/// assertions are unchanged.
#[test]
fn the_cache_keeps_the_wire_value_under_its_key() {
    use std::os::unix::fs::MetadataExt;
    let tz = chrono_tz::Asia::Kolkata;
    let dir = tempfile::tempdir().expect("tempdir");
    let cache = dir.path().join("cache/replay");
    let fresh = tz_table::probe(tz).to_wire();
    assert_eq!(tz_table::wire_for(Some(&cache), tz), fresh);
    let file = cache.join(tz_table::CACHE_FILE);
    let on_disk = std::fs::read_to_string(&file).expect("written");
    assert_eq!(on_disk, tz_table::cache_text(&fresh));
    assert_eq!(tz_table::from_cache_text(&on_disk), Some(fresh.clone()));
    let inode = std::fs::metadata(&file).expect("the file").ino();
    assert_eq!(tz_table::wire_for(Some(&cache), tz), fresh);
    assert_eq!(std::fs::metadata(&file).expect("the file").ino(), inode, "the binary's own table is read, not re-probed");
    let doctored = json!({"key": tz_table::key_of(tz), "base": "+05:30:00", "then": []});
    std::fs::write(&file, tz_table::cache_text(&doctored)).expect("write");
    assert_eq!(
        tz_table::wire_for(Some(&cache), tz),
        fresh,
        "a matching key and digest whose table disagrees with the zone is probed afresh (D104)"
    );
    assert_eq!(std::fs::read_to_string(&file).expect("rewritten"), tz_table::cache_text(&fresh));
    std::fs::write(&file, doctored.to_string()).expect("write");
    assert_eq!(tz_table::wire_for(Some(&cache), tz), fresh, "a file with no digest is probed afresh");
    let flipped = tz_table::cache_text(&doctored).replace("+05:30:00", "+05:31:00");
    std::fs::write(&file, &flipped).expect("write");
    assert_eq!(tz_table::wire_for(Some(&cache), tz), fresh, "a file whose digest does not match is probed afresh");
    std::fs::write(&file, tz_table::cache_text(&json!({"key": "Asia/Kolkata|1999z|1900-2200", "then": []}))).expect("write");
    assert_eq!(tz_table::wire_for(Some(&cache), tz), fresh);
    std::fs::write(&file, "{not json").expect("write");
    assert_eq!(tz_table::wire_for(Some(&cache), tz), fresh);
    assert_eq!(std::fs::read_to_string(&file).expect("rewritten"), tz_table::cache_text(&fresh));
    assert_eq!(tz_table::wire_for(None, tz), fresh);
}

/// **The digest is the harness's FNV-1a-64 of the rest of the text** (README gap 4613), computed by the
/// harness's own body and never borrowed from the binary, and **every one-byte edit of a written table
/// is refused** — the offsets, the instants, the key and the digest itself (`from_cache_text` is
/// `None`), so the edit is probed afresh rather than served.
#[test]
fn every_one_byte_edit_of_the_zone_table_is_refused() {
    let wire = tz_table::probe(chrono_tz::America::Chicago).to_wire();
    let text = tz_table::cache_text(&wire);
    let rest = text.strip_prefix("{\"digest\":\"").expect("the digest first");
    let (hex, body) = rest.split_at(16);
    assert_eq!(hex, fnv::fnv1a64_hex(body.strip_prefix("\",").expect("then the rest").as_bytes()));
    let bytes = text.as_bytes();
    let mut refused = 0usize;
    for (i, b) in bytes.iter().enumerate() {
        let swap = if b.is_ascii_digit() { if *b == b'9' { b'0' } else { b + 1 } } else { continue };
        let mut edit = bytes.to_vec();
        edit[i] = swap;
        let edit = String::from_utf8(edit).expect("ascii");
        assert_eq!(tz_table::from_cache_text(&edit), None, "a digit edited at byte {i} was read");
        refused += 1;
    }
    assert!(refused > 1000, "the sweep reached {refused} digits");
}

/// **T4 (c), `#[ignore]`.** Every minute of [1900, 2200) in the five zones:
/// catches a change and change back inside one hour that lasts a minute or more.
#[test]
#[ignore = "T4 (c): 788 million chrono lookups; run once at B4, recorded in kernel/README.md"]
fn the_table_is_chronos_offset_at_every_minute() {
    let handles: Vec<_> = FIVE
        .into_iter()
        .map(|tz| {
            std::thread::spawn(move || {
                let t = tz_table::probe(tz);
                let (mut k, mut i, mut cur) = (0u64, 0usize, t.base);
                let mut unix = tz_table::SPAN_FROM;
                while unix < tz_table::SPAN_TO {
                    while i < t.transitions.len() && t.transitions[i].0 <= unix {
                        cur = t.transitions[i].1;
                        i += 1;
                    }
                    assert_eq!(cur, chrono_offset(tz, unix), "{} at {unix}", t.key);
                    unix += 60;
                    k += 1;
                }
                (t.key, k)
            })
        })
        .collect();
    for h in handles {
        let (key, k) = h.join().expect("sweep");
        eprintln!("T4 (c): {key}: {k} minutes agree");
    }
}

/// **T4 (d), `#[ignore]`.** Every chrono-tz zone: the table is well formed, the
/// kernel accepts it, and every transition in [1970, 2100) reads chrono's offset
/// at −1 s, 0 and +1 s. Beside it, B1's stated assumption for `Cal.localHits`
/// (a scan where chrono-tz binary-searches the local spans): the local spans are
/// in order and no three overlap, which holds when each span outlasts the offset
/// changes at its two ends.
#[test]
#[ignore = "T4 (d): every chrono-tz zone probed; run once at B4, recorded in kernel/README.md"]
fn every_zone_table_is_chronos_offset_at_its_transitions() {
    let zones: Vec<Tz> = chrono_tz::TZ_VARIANTS.to_vec();
    let workers = 8;
    let chunks: Vec<Vec<Tz>> = zones.chunks(zones.len().div_ceil(workers)).map(<[Tz]>::to_vec).collect();
    let handles: Vec<_> = chunks
        .into_iter()
        .map(|chunk| {
            std::thread::spawn(move || {
                let mut out = Vec::new();
                for tz in chunk {
                    let t = tz_table::probe(tz);
                    well_formed(&t, tz);
                    let mut checked = 0;
                    for &(s, _) in t.transitions.iter().filter(|(s, _)| (Y1970..Y2100).contains(s)) {
                        for d in [-1, 0, 1] {
                            assert_eq!(table_offset(&t, s + d), chrono_offset(tz, s + d), "{} at {s}{d:+}", t.key);
                        }
                        checked += 1;
                    }
                    // Local spans [lo + off, hi + off): in order, and span i
                    // ends before span i + 2 starts.
                    let mut spans = vec![(i64::MIN / 2, t.base)];
                    spans.extend(t.transitions.iter().copied());
                    let mut scan_ok = true;
                    for i in 0..spans.len() {
                        if i + 1 < spans.len() {
                            let (lo, off) = spans[i];
                            let (lo1, off1) = spans[i + 1];
                            scan_ok &= lo + off as i64 <= lo1 + off1 as i64;
                        }
                        if i + 2 < spans.len() {
                            let hi = spans[i + 1].0 + spans[i].1 as i64;
                            let lo2 = spans[i + 2].0 + spans[i + 2].1 as i64;
                            scan_ok &= hi <= lo2;
                        }
                    }
                    out.push((t, checked, scan_ok));
                }
                out
            })
        })
        .collect();
    let (mut zones_n, mut trans, mut checked, mut most, mut bad_scan) = (0, 0, 0, (String::new(), 0), Vec::new());
    for h in handles {
        for (t, c, scan_ok) in h.join().expect("zone worker") {
            kernel_accepts(&t);
            zones_n += 1;
            trans += t.transitions.len();
            checked += c;
            if t.transitions.len() > most.1 {
                most = (t.key.clone(), t.transitions.len());
            }
            if !scan_ok {
                bad_scan.push(t.key.clone());
            }
        }
    }
    eprintln!(
        "T4 (d): {zones_n} zones, {trans} transitions ({checked} in [1970, 2100) checked at ±1 s), most {most:?}, the scan assumption fails in {} zones: {bad_scan:?}",
        bad_scan.len()
    );
    assert!(bad_scan.is_empty(), "B1's scan assumption fails: {bad_scan:?}");
}
