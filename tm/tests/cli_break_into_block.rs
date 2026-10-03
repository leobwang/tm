//! **A break that runs into a block's start is not block time** — the owner's **D92** (README gap 4241,
//! parity P85), driven through the binary, and the cache that must not serve the reading before it.
//!
//! The day: `tm init --example`, woken at 07:00, a break from 09:00 ended at 09:25, and `^m1` started at
//! a `--now` of 09:10 — a clock behind the log, so the `start` lands inside the break the log already
//! holds (`tm start` ends a RUNNING break, and this one had ended), and `tm stop` at 10:00. `tm stop`
//! says thirty-five minutes — the host's idle minutes clip the break to `[09:10, 09:25]` — and since
//! D92 so does every reader of the replay: the review's block minutes, load and mix, the heat grid
//! (the 09:00 hour is thirty-five minutes of block and twenty-five of break, the overlap counted once),
//! and the planner's past row, which starts at the break's end. Fork 4748911's replay started the clock
//! at 09:10, so the review read 50 and the grid's 09:00 cell held 50 + 25 minutes.
//!
//! The second test is step 5 of the track: a sealed day record holding the reading BEFORE D92 — the
//! record the `0984304` kernel (archive id `75dcd6da44741b7a`) wrote for the day, value for value, measured
//! in `scratchpad/w43-k/cache` — is served under this binary's own id (the bite: the cache really is
//! read) and is NOT served under that kernel's id: the answer is the replay's, and the cache is rebuilt.
//!
//! **Since the owner's D93 (W-43 track H, README gap 4246) a sealed month file carries a digest in the
//! manifest**, and a hand edit that leaves the digest behind is refused by the digest alone — so the
//! record is written WITH its digest ([`write_the_reading_before_d92`]): a file a kernel could have
//! written, the case the kernel id is the key for (`cli_replay_cache_kernel.rs`'s poison, the same
//! move). Found at the W-43 land (README gap 4490): track K's test, written beside D93 and not after it,
//! failed its bite on the merged tree — the record was refused by its digest, not served.

mod cli_common;

use std::fs;
use std::path::{Path, PathBuf};

use cli_common::{fnv1a64_hex, Tm};
use serde_json::Value;

const WAKE: &str = "2026-09-07T07:00:00-05:00";
const BREAK_ON: &str = "2026-09-07T09:00:00-05:00";
const BREAK_OFF: &str = "2026-09-07T09:25:00-05:00";
const START: &str = "2026-09-07T09:10:00-05:00";
const STOP: &str = "2026-09-07T10:00:00-05:00";
const AFTER: &str = "2026-09-07T10:01:00-05:00";

fn heat_09(week: &Value) -> Vec<u64> {
    week["review"]["heat"][0]["hours"][9]
        .as_array()
        .unwrap_or_else(|| panic!("no heat cell for 09:00: {week}"))
        .iter()
        .map(|m| m.as_u64().expect("minutes"))
        .collect()
}

#[test]
fn a_block_begun_inside_a_logged_break_counts_its_worked_minutes_everywhere() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm.ok_at(BREAK_ON, &["break", "20m"]);
    tm.ok_at(BREAK_OFF, &["break"]);
    tm.ok_at(START, &["start", "^m1", "--energy", "3"]);
    let said = tm.ok_at(STOP, &["stop"]).stdout;
    assert!(said.contains("after 35m"), "`tm stop` no longer nets the break's tail: {said}");

    // The log holds the break BEFORE the start, lasting into it: gap 4241's shape, written by the binary.
    let log = tm.log();
    let n = log.len();
    let (brk, start) = (&log[n - 3], &log[n - 2]);
    assert_eq!((brk["ev"].as_str(), brk["actual_min"].as_u64()), (Some("break"), Some(25)), "{brk}");
    assert_eq!(brk["t"], BREAK_ON, "the break is stamped at its start: {brk}");
    assert_eq!((start["ev"].as_str(), start["t"].as_str()), (Some("start"), Some(START)), "{start}");

    let day = tm.json_at(AFTER, &["review", "day"]);
    let r = &day["review"];
    assert_eq!(r["block_min"], 35, "review day's block minutes (fork 4748911: 50): {r}");
    assert_eq!(r["load"], 35.0, "review day's load (^m1 is ci 5): {r}");
    assert_eq!(r["load_blocks"], 0.58, "review day's load in blocks: {r}");
    assert_eq!(r["mix"]["total_min"], 35, "review day's energy mix: {r}");

    let week = tm.json_at(AFTER, &["review", "week"]);
    assert_eq!(week["review"]["block_min"], 35, "review week's block minutes");
    assert_eq!(week["review"]["load"], 35.0, "review week's load");
    let cell = heat_09(&week);
    assert_eq!((cell[0], cell[1]), (35, 25), "the 09:00 heat cell: block then break, the overlap counted once: {cell:?}");
    assert_eq!(cell.iter().sum::<u64>(), 60, "the 09:00 cell holds the hour once: {cell:?}");
    let human = tm.ok_at(AFTER, &["review", "week"]).stdout;
    assert!(human.contains("block 35m · break 25m"), "review week's heat line: {human}");

    // The planner's past row starts where the clock did.
    let plan = tm.ok_at(AFTER, &["plan"]).stdout;
    assert!(
        plan.lines().any(|l| l.starts_with("09:25") && l.contains("Finish ch.5")),
        "the past row of ^m1 does not start at the break's end:\n{plan}"
    );
    assert!(!plan.lines().any(|l| l.starts_with("09:10")), "a row still starts at the `start`, across the break:\n{plan}");
}

// ---------------------------------------------------------------------------
// The cache: the reading before D92 is never served from a record another kernel sealed
// ---------------------------------------------------------------------------

/// Three days after the fortnight's last line, so its August days are sealed (W-42 track R's instant).
const LATER: &str = "2026-09-10T09:00:00-05:00";
const SEALED_DATE: &str = "2026-08-25";
/// [`SEALED_DATE`] as the kernel's day number, the key a month file's `days` object holds it under.
const SEALED_DAY: &str = "739852";
/// The kernel `0984304` links — the last before D92: FNV-1a-64 of its `libTmKernel_TmKernel.a`, and
/// the `kernel` its binary writes into `ckpt.json` (both measured, `scratchpad/w43-k/cache`).
const PRE_D92_KERNEL: &str = "75dcd6da44741b7a";

/// Where the three leaves D92 moves sit in a sealed day record: `Seal.DayRecord` is the day, then the
/// day's `Replay.DayAcc` as one array — `blockMin` third, `ciUnknown` (pairs `[id, minutes]`) seventh,
/// `segments` (each `[start, stop, kind]`, a stamp `[sec, ns, west, offSec]`) eleventh. The test reads
/// each before it writes one, so a codec that moved a field fails here by name.
const ACC_AT: usize = 1;
const BLOCK_MIN_AT: usize = 2;
const CI_UNKNOWN_AT: usize = 6;
const SEGMENTS_AT: usize = 10;

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

/// `plan-basic` with the corpus's `energy-14d.jsonl` as its log, edited on its first day so that a
/// twenty-minute break at 11:30 runs into `e02`'s 11:40 `start`, and `e02` is `stop`ped at 12:28 (its
/// `done` replaced): a cut whose credit the overlap moves. The corpus file itself is only read.
fn plan_with_a_break_run_into_a_start() -> Tm {
    let tmp = tempfile::TempDir::new().expect("temp dir");
    let plan = tmp.path().join("plan");
    copy_dir(&corpus().join("plan-basic"), &plan);
    fs::create_dir_all(plan.join(".tm")).expect("mkdir .tm");
    let mut log = fs::read_to_string(corpus().join("logs/energy-14d.jsonl")).expect("read the log");
    let start = r#"{"t":"2026-08-25T11:40:00-05:00","ev":"start","id":"e02""#;
    assert_eq!(log.matches(start).count(), 1, "the fortnight's e02 start moved");
    let brk = r#"{"t":"2026-08-25T11:30:00-05:00","ev":"break","planned_min":20,"actual_min":20,"where":"walk"}"#;
    log = log.replace(start, &format!("{brk}\n{start}"));
    let done = r#"{"t":"2026-08-25T12:28:00-05:00","ev":"done","id":"e02","est_min":60,"actual_min":48,"went":1,"tags":["admin"],"ci":3}"#;
    assert_eq!(log.matches(done).count(), 1, "the fortnight's e02 done moved");
    log = log.replace(done, r#"{"t":"2026-08-25T12:28:00-05:00","ev":"stop","id":"e02","remaining_min":30}"#);
    fs::write(plan.join(".tm/log.jsonl"), log).expect("write the log");
    Tm { tmp, plan }
}

fn cache_dir(tm: &Tm) -> PathBuf {
    tm.plan.join(".tm/cache/replay")
}

fn read_json(path: &Path) -> Value {
    let text = fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("{} is not JSON: {e}", path.display()))
}

fn ckpt_str(tm: &Tm, key: &str) -> String {
    let ckpt = read_json(&cache_dir(tm).join("ckpt.json"));
    ckpt[key].as_str().unwrap_or_else(|| panic!("ckpt.json has no string `{key}`")).to_string()
}

fn august_file(tm: &Tm) -> PathBuf {
    let ckpt = read_json(&cache_dir(tm).join("ckpt.json"));
    let name = ckpt["manifest"]["2026-08"]
        .as_str()
        .unwrap_or_else(|| panic!("the manifest names no August file: {}", ckpt["manifest"]));
    cache_dir(tm).join(name)
}

/// The sealed record's three leaves D92 moves: `blockMin`, `e02`'s ci-unknown minutes, and the second
/// `e02`'s Block segment starts at.
fn sealed_leaves(path: &Path) -> (u64, u64, u64) {
    let month = read_json(path);
    let record = &month["days"][SEALED_DAY];
    assert_eq!(record[0].as_u64(), Some(SEALED_DAY.parse().expect("a day number")), "the codec moved");
    let acc = &record[ACC_AT];
    let unknown = acc[CI_UNKNOWN_AT]
        .as_array()
        .and_then(|ps| ps.iter().find(|p| p[0] == "e02"))
        .and_then(|p| p[1].as_u64())
        .unwrap_or_else(|| panic!("no ci-unknown minutes for e02: {}", acc[CI_UNKNOWN_AT]));
    let seg = acc[SEGMENTS_AT]
        .as_array()
        .and_then(|ss| ss.iter().find(|s| s[2].to_string().contains("e02")))
        .unwrap_or_else(|| panic!("no Block segment of e02: {}", acc[SEGMENTS_AT]));
    (acc[BLOCK_MIN_AT].as_u64().expect("blockMin"), unknown, seg[0][0].as_u64().expect("a start second"))
}

/// Write the reading before D92 into the sealed record — the three leaves `0984304`'s kernel sealed
/// differently, and nothing else, which leaves the record value for value the one that kernel wrote —
/// and the manifest's digest of the file with it (D93), replaced as text because `ckpt.json` carries the
/// kernel's checkpoint verbatim and a parse would reorder its keys.
fn write_the_reading_before_d92(tm: &Tm, path: &Path) {
    let before = fs::read(path).expect("read the month file");
    let mut month = read_json(path);
    let acc = &mut month["days"][SEALED_DAY][ACC_AT];
    acc[BLOCK_MIN_AT] = Value::from(260u64);
    for p in acc[CI_UNKNOWN_AT].as_array_mut().expect("ciUnknown") {
        if p[0] == "e02" {
            p[1] = Value::from(48u64);
        }
    }
    for s in acc[SEGMENTS_AT].as_array_mut().expect("segments") {
        if s[2].to_string().contains("e02") {
            s[0][0] = Value::from(63_923_272_800u64);
        }
    }
    let text = serde_json::to_string(&month).expect("serialise") + "\n";
    fs::write(path, &text).expect("write the month file");
    let ckpt_path = cache_dir(tm).join("ckpt.json");
    let ckpt = fs::read_to_string(&ckpt_path).expect("read ckpt.json");
    let (old, new) = (fnv1a64_hex(&before), fnv1a64_hex(text.as_bytes()));
    assert_eq!(ckpt.matches(&format!("\"{old}\"")).count(), 1, "ckpt.json records the month file's digest once: {ckpt}");
    fs::write(&ckpt_path, ckpt.replace(&format!("\"{old}\""), &format!("\"{new}\""))).expect("write ckpt.json");
}

fn reviewed_block_min(tm: &Tm) -> u64 {
    let v = tm.json_at(LATER, &["review", "day", "--date", SEALED_DATE]);
    v["review"]["block_min"].as_u64().unwrap_or_else(|| panic!("no block_min: {v}"))
}

#[test]
fn a_sealed_record_holding_the_reading_before_d92_is_rebuilt_and_never_served() {
    let tm = plan_with_a_break_run_into_a_start();
    tm.ok_at(LATER, &["now"]);
    let this_kernel = ckpt_str(&tm, "kernel");
    assert_ne!(this_kernel, PRE_D92_KERNEL, "this binary links the kernel before D92");
    let first_gen = ckpt_str(&tm, "gen");
    let august = august_file(&tm);

    // The replay's own reading, sealed: e02 credited 38 (11:50-12:28), its Block drawn from 11:50.
    let truth = reviewed_block_min(&tm);
    assert_eq!(truth, 250, "86 + 61 + 65 done minutes and e02's 38 after the break");
    assert_eq!(sealed_leaves(&august), (250, 38, 63_923_273_400), "the sealed record is not the replay's reading");

    // THE BITE: under this kernel's own id the cache is trusted, so the reading before D92 IS served.
    write_the_reading_before_d92(&tm, &august);
    assert_eq!(sealed_leaves(&august), (260, 48, 63_923_272_800));
    assert_eq!(
        reviewed_block_min(&tm),
        260,
        "the record was not served under this kernel's own id — the cache is not read for {SEALED_DATE}, so \
         nothing below would mean anything"
    );

    // THE CLAIM: the same record under the id of the kernel that wrote that reading is not served.
    let ckpt_path = cache_dir(&tm).join("ckpt.json");
    let text = fs::read_to_string(&ckpt_path).expect("read ckpt.json");
    let needle = format!("\"kernel\":\"{this_kernel}\"");
    assert_eq!(text.matches(&needle).count(), 1, "ckpt.json names its kernel once");
    fs::write(&ckpt_path, text.replace(&needle, &format!("\"kernel\":\"{PRE_D92_KERNEL}\""))).expect("write ckpt.json");
    assert_eq!(
        reviewed_block_min(&tm),
        truth,
        "a record the kernel before D92 sealed was served: its reading of a break run into a start reached the review"
    );
    assert_eq!(ckpt_str(&tm, "kernel"), this_kernel, "the rebuilt checkpoint is not this kernel's");
    let rebuilt_gen = ckpt_str(&tm, "gen");
    assert_ne!(rebuilt_gen, first_gen, "genesis wrote no new generation");
    let rebuilt = august_file(&tm);
    assert_ne!(rebuilt, august, "the manifest still names the month file the old kernel's reading is in");
    assert_eq!(sealed_leaves(&rebuilt), (250, 38, 63_923_273_400), "the rebuilt record is not the replay's reading");
    eprintln!(
        "D92 cache: kernel {this_kernel} seals {SEALED_DATE} at 250; the record {PRE_D92_KERNEL} sealed (260) is served \
         under {this_kernel} and rebuilt under {PRE_D92_KERNEL}: generation {first_gen} -> {rebuilt_gen}"
    );
}
