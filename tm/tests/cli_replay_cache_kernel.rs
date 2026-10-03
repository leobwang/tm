//! **A replay cache another kernel wrote is rebuilt, never served** — W-42 track R, step 3 (the
//! owner's **D87**, README gap 4137; D13's cache, design §9.8's integrity rule).
//!
//! D87 changes what the kernel's replay derives for a day whose log holds a break inside a block,
//! so every sealed day record written before it is a record of the OLD reading. D13 lets the
//! kernel read such a record back for an explicitly old date and trusts it as it trusts the
//! checkpoint — nothing re-derives a sealed record once the manifest names it. What keeps an old
//! record from being served after a kernel change is one key: `ckpt.json` carries the identity of
//! the kernel that wrote it (`kernel_log::kernel_id`, FNV-1a-64 of the archive this binary links,
//! `tm-kernel-ffi/build.rs`), and `Snapshot::valid_for` sends a checkpoint written by any other
//! kernel straight to genesis, whose new generation replaces every month file the old manifest
//! named.
//!
//! **This file shows the key working, by value, and shows first that it is needed.** A sealed
//! record is poisoned by hand. Under this binary's own kernel id the poison IS served — the cache
//! really is read, and a stale record would really reach a user — which is the bite. Under another
//! kernel's id the same poison is NOT served: the answer is the one a fresh replay gives, and the
//! cache is rewritten under this binary's id with a new generation. It holds before D87 and after
//! it, which is the point: it is the instrument a change of the replay's reading relies on, not a
//! test of one reading.

mod cli_common;

use std::fs;
use std::path::{Path, PathBuf};

use cli_common::Tm;
use serde_json::Value;

/// Three days after `energy-14d.jsonl`'s last line, so the log's August days are sealed (below
/// the checkpoint's ledger day) — the instant `cli_switch_acceptance.rs` warms its cache at.
const LATER: &str = "2026-09-10T09:00:00-05:00";

/// The log's first day, sealed at [`LATER`]: four blocks done, 260 block minutes.
const SEALED_DATE: &str = "2026-08-25";

/// [`SEALED_DATE`] as the kernel's day number (days since 0001-01-01), the key a month file's
/// `days` object holds it under.
const SEALED_DAY: &str = "739852";

/// Where `blocksDone` sits in a sealed day record: `Seal.DayRecord`'s codec writes the day, then the
/// day's `Replay.DayAcc` as one array (`firstStart`, `starts`, `blockMin`, `blocksDone`, …), then the
/// seam and the day's lists. The test reads the value at this path before it writes one, so a codec
/// that moved the field fails here by name rather than poisoning another fact.
const ACC_AT: usize = 1;
const BLOCKS_DONE_AT: usize = 3;

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../kernel/corpus")
}

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).expect("create dir");
    for entry in fs::read_dir(from).expect("read fixture") {
        let entry = entry.expect("dir entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("file type").is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target).expect("copy file");
        }
    }
}

/// `plan-basic` carrying the corpus's `energy-14d.jsonl` as its `.tm/log.jsonl`.
fn plan_with_the_fortnight() -> Tm {
    let tmp = tempfile::TempDir::new().expect("temp dir");
    let plan = tmp.path().join("plan");
    copy_dir(&corpus().join("plan-basic"), &plan);
    fs::create_dir_all(plan.join(".tm")).expect("mkdir .tm");
    fs::copy(corpus().join("logs/energy-14d.jsonl"), plan.join(".tm/log.jsonl")).expect("copy the log");
    Tm { tmp, plan }
}

fn cache_dir(tm: &Tm) -> PathBuf {
    tm.plan.join(".tm/cache/replay")
}

fn read_json(path: &Path) -> Value {
    let text = fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("{} is not JSON: {e}", path.display()))
}

/// `ckpt.json`'s string field `key`.
fn ckpt_str(tm: &Tm, key: &str) -> String {
    let ckpt = read_json(&cache_dir(tm).join("ckpt.json"));
    ckpt[key].as_str().unwrap_or_else(|| panic!("ckpt.json has no string `{key}`")).to_string()
}

/// The month file `ckpt.json`'s manifest names for August 2026.
fn august_file(tm: &Tm) -> PathBuf {
    let ckpt = read_json(&cache_dir(tm).join("ckpt.json"));
    let name = ckpt["manifest"]["2026-08"]
        .as_str()
        .unwrap_or_else(|| panic!("the manifest names no August file: {}", ckpt["manifest"]));
    cache_dir(tm).join(name)
}

/// The sealed record's `blocksDone`, read from the month file.
fn sealed_blocks_done(path: &Path) -> u64 {
    let month = read_json(path);
    let record = &month["days"][SEALED_DAY];
    assert_eq!(
        record[0].as_u64(),
        Some(SEALED_DAY.parse().expect("a day number")),
        "{}: the record keyed {SEALED_DAY} does not open with its own day — the codec moved",
        path.display()
    );
    record[ACC_AT][BLOCKS_DONE_AT]
        .as_u64()
        .unwrap_or_else(|| panic!("{}: no blocksDone at [{ACC_AT}][{BLOCKS_DONE_AT}]", path.display()))
}

/// Write `blocks_done` into the sealed record, keeping every other byte of meaning.
fn poison(path: &Path, blocks_done: u64) {
    let mut month = read_json(path);
    month["days"][SEALED_DAY][ACC_AT][BLOCKS_DONE_AT] = Value::from(blocks_done);
    fs::write(path, serde_json::to_string(&month).expect("serialise") + "\n").expect("write the month file");
}

/// What `tm review day --date` says about the sealed day.
fn reviewed_blocks_done(tm: &Tm) -> u64 {
    let v = tm.json_at(LATER, &["review", "day", "--date", SEALED_DATE]);
    v["review"]["blocks_done"].as_u64().unwrap_or_else(|| panic!("no blocks_done: {v}"))
}

/// **A sealed record another kernel wrote cannot answer**: `ckpt.json`'s kernel id is the key,
/// and genesis rebuilds every month file under this binary's.
#[test]
fn a_replay_cache_another_kernel_wrote_is_rebuilt_and_never_served() {
    let tm = plan_with_the_fortnight();

    // Warm it: a verb seals the August days into month files.
    tm.ok_at(LATER, &["now"]);
    let this_kernel = ckpt_str(&tm, "kernel");
    let first_gen = ckpt_str(&tm, "gen");
    let august = august_file(&tm);
    let truth = reviewed_blocks_done(&tm);
    assert_eq!(truth, 4, "energy-14d's first day finished four blocks");
    assert_eq!(sealed_blocks_done(&august), truth, "the sealed record is the replay's own reading");

    // THE BITE: under this kernel's id the cache is trusted, so a poisoned record IS served.
    // Without this, the claim below could hold because the sealed record is never read at all.
    poison(&august, truth - 1);
    assert_eq!(
        reviewed_blocks_done(&tm),
        truth - 1,
        "a poisoned record under this kernel's own id was not served — the cache is not read for \
         {SEALED_DATE}, so nothing below would mean anything"
    );

    // THE CLAIM: the same poison under another kernel's id is not served. Flip one hex digit of
    // the id, so the file is byte-for-byte a checkpoint this binary's sibling could have written.
    let other: String = {
        let mut c: Vec<char> = this_kernel.chars().collect();
        c[0] = if c[0] == '0' { '1' } else { '0' };
        c.into_iter().collect()
    };
    assert_ne!(other, this_kernel);
    let ckpt_path = cache_dir(&tm).join("ckpt.json");
    let text = fs::read_to_string(&ckpt_path).expect("read ckpt.json");
    let needle = format!("\"kernel\":\"{this_kernel}\"");
    assert_eq!(text.matches(&needle).count(), 1, "ckpt.json names its kernel once: {text}");
    fs::write(&ckpt_path, text.replace(&needle, &format!("\"kernel\":\"{other}\""))).expect("write ckpt.json");
    assert_eq!(ckpt_str(&tm, "kernel"), other);

    assert_eq!(
        reviewed_blocks_done(&tm),
        truth,
        "a record another kernel wrote was served: a change of the replay's reading (D87) would \
         reach users through every sealed day"
    );
    // And it was rebuilt, not merely bypassed: this binary's id, a new generation, and an August
    // file that is not the poisoned one and holds the replay's own reading.
    assert_eq!(ckpt_str(&tm, "kernel"), this_kernel, "the rebuilt checkpoint is not this kernel's");
    let rebuilt_gen = ckpt_str(&tm, "gen");
    assert_ne!(rebuilt_gen, first_gen, "genesis wrote no new generation");
    let rebuilt = august_file(&tm);
    assert_ne!(rebuilt, august, "the manifest still names the poisoned month file");
    assert_eq!(sealed_blocks_done(&rebuilt), truth, "the rebuilt record is not the replay's reading");

    eprintln!(
        "replay cache: kernel {this_kernel}; a poisoned {SEALED_DATE} record served under it \
         ({} for {truth}); under {other} the answer was {truth} and generation {first_gen} was \
         replaced by {rebuilt_gen}",
        truth - 1
    );
}
