//! **windowbench: W5's measurement gate, through the replay cache on disk** (stage 5 D9 W5; design
//! `kernel/design/stage5/stage5-D9-D10-design.md` §14.5 row W5, §18.2–§18.7).
//!
//! `logbench` (g) runs it as a child process (as (c) runs `tzprobe`), because it drives
//! `tm/src/cli/kernel_log.rs`'s [`kernel_log::ReplayCache`], whose serde_json and chrono the kernel's FFI crate
//! does not depend on.  It can also be run alone:
//!
//! ```text
//! systemd-run --user --scope -p MemoryMax=16G -p MemorySwapMax=0 --quiet \
//!   cargo run --example windowbench -p tm -- all
//! ```
//!
//! The log is the design pass's 3-year file at 61 events a day (`loggen`, 65,771 lines), in America/Chicago (the
//! probed zone table crosses the wire on every call, as it will at S).  Every call is `ReplayCache::replay` with
//! `want.facts`, as a verb will make it: the snapshot read, the split, the prefix digest, the request, the kernel,
//! the answer's decode and any files written.  Each scenario runs in a child process of its own, `VmHWM` reset to
//! the RSS just before its first measured call, so a peak is the scenario's calls' (and the log text it holds).
//!
//! - **genesis**: the whole log, no cache (the gate's genesis total), then, untimed, the same genesis through
//!   `kernel_log::genesis` for its calls and pops;
//! - **hot**: seven calls on the stored checkpoint of the whole log, the same day; the digest alone beside it;
//! - **reseal**: a checkpoint sealed at day 1,054 and the log through day 1,055 (§9.6's back-off), seven times,
//!   each from a fresh copy of the cache;
//! - **stall**: from that checkpoint, ten days during which a block started on the first evening is never
//!   stopped (every later block event is left out, so the machine's open block holds the ledger day, §9.4), ten
//!   verbs a day; checkpoint writes are counted per day;
//! - **pinned**: from that checkpoint, fourteen days of the log with `maxLine` at day 1,054's last line (an undo
//!   stack pinning fourteen days, §9.6), ten verbs a day;
//! - **far undo**: the whole log's cache, a hand `undo` of a `done` thirty days back, then ten verbs (notes);
//! - **two geneses at once**: two children rebuilding into two caches concurrently.
//!
//! Lines beginning `=` are the gate's figures, which `all` collects into the gate table at the end.

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

#[allow(dead_code)]
#[path = "../tests/support/loggen.rs"]
mod loggen;

#[allow(dead_code)]
#[path = "../src/cli/kernel_log.rs"]
mod kernel_log;

use kernel_log::{Outcome, ReplayCache, Want};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

const REPEATS: usize = 7;
/// The last day of the checkpoint the reseal, stall and pinned scenarios start from.
const EARLY: usize = 1_054;
const VERBS_A_DAY: usize = 10;

fn vm_hwm_kib() -> u64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    s.lines()
        .find_map(|l| l.strip_prefix("VmHWM:"))
        .and_then(|v| v.trim().trim_end_matches("kB").trim().parse().ok())
        .unwrap_or(0)
}

fn reset_hwm() {
    assert!(std::fs::write("/proc/self/clear_refs", "5").is_ok(), "cannot reset VmHWM");
}

fn mib(kib: u64) -> f64 {
    kib as f64 / 1024.0
}

/// The design pass's 3-year, 61-a-day log (generated after its 1mo, 6mo and 1y files from one generator), and
/// each day's first line (one `wake` a day), with the log's length as a sentinel.
fn the_log() -> (Vec<String>, Vec<usize>) {
    let mut g = loggen::LogGen::new(loggen::Rate::SixtyOne, loggen::SEED);
    let mut lines = Vec::new();
    for &(age, days) in loggen::AGES.iter() {
        lines = g.days(days);
        if age == "3y" {
            break;
        }
    }
    let mut starts: Vec<usize> = lines.iter().enumerate().filter(|(_, l)| l.contains(r#""ev":"wake""#)).map(|(i, _)| i).collect();
    assert_eq!(starts.len(), 1_095, "one wake a day");
    starts.push(lines.len());
    (lines, starts)
}

fn now_of(day: usize) -> u64 {
    kernel_log::day_of(chrono::NaiveDate::from_ymd_opt(2026, 1, 1).expect("a date") + chrono::Duration::days(day as i64))
}

fn zone() -> serde_json::Value {
    tz_table::probe(chrono_tz::America::Chicago).to_wire()
}

fn want() -> Want {
    Want { facts: true, headers_from: None, render: vec![] }
}

fn ms_since(s: Instant) -> f64 {
    s.elapsed().as_secs_f64() * 1000.0
}

/// (best, median, max).
fn stats(v: &[f64]) -> (f64, f64, f64) {
    let mut v = v.to_vec();
    v.sort_by(|a, b| a.total_cmp(b));
    (v[0], v[v.len() / 2], v[v.len() - 1])
}

fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).expect("a directory");
    for e in std::fs::read_dir(from).expect("a cache directory").flatten() {
        let p = e.path();
        if p.is_dir() {
            copy_dir(&p, &to.join(e.file_name()));
        } else {
            std::fs::copy(&p, to.join(e.file_name())).expect("a copy");
        }
    }
}

/// The lines of `[from, to)`'s days split into [`VERBS_A_DAY`] appends each.
fn verbs_of(day: &[String]) -> Vec<Vec<String>> {
    let per = day.len().div_ceil(VERBS_A_DAY).max(1);
    day.chunks(per).map(<[String]>::to_vec).collect()
}

/// Child: genesis over days `[0, last]` into `dir`.  With `detail`, also the calls and pops of the same genesis.
fn child_genesis(dir: &Path, last: usize, detail: bool) {
    let (lines, starts) = the_log();
    let text = loggen::text(&lines[..starts[last + 1]]);
    let n = starts[last + 1];
    drop(lines);
    let tz = zone();
    tm_kernel_ffi::init().expect("init");
    let mut cache = ReplayCache::new(Some(dir.to_path_buf()));
    reset_hwm();
    let before = vm_hwm_kib();
    let s = Instant::now();
    let r = cache.replay(text.as_bytes(), now_of(last), &tz, None, &want()).expect("genesis answers");
    let e = ms_since(s);
    let peak = vm_hwm_kib();
    assert_eq!(r.outcome, Outcome::Genesis, "{:?}", r.rebuilt_because);
    println!(
        "genesis through day {last}: {n} lines, {} B; {e:.0} ms (files written); {} day and {} window records in {} month files; ckpt {} B, cut {}, ledger day {}; VmHWM {:.1} -> {:.1} MiB",
        text.len(),
        r.days.len(),
        r.window.len(),
        r.snapshot.manifest.len(),
        r.snapshot.ckpt.len(),
        r.snapshot.meta.cut,
        r.snapshot.meta.ledger_day,
        mib(before),
        mib(peak)
    );
    if detail {
        println!("=genesis_ms\t{e:.1}");
        println!("=rss_genesis\t{:.1}", mib(peak));
        let sp = kernel_log::split(text.as_bytes());
        let g = kernel_log::genesis(
            &kernel_log::date_of(now_of(last)),
            &tz,
            &sp,
            kernel_log::Policy { keep_days: kernel_log::KEEP_DAYS, max_line: None },
            &want(),
        )
        .expect("genesis answers");
        println!("  the same genesis (kernel_log::genesis, not timed): {} calls, {} pops, largest call {} lines", g.calls, g.pops, g.largest_call);
    } else {
        println!("=rss_base_{last}\t{:.1}", mib(peak));
    }
}

/// Child: seven hot calls on the whole log's stored checkpoint, the same day, and the digest alone.
fn child_hot(base: &Path, work: &Path) {
    copy_dir(base, work);
    let (lines, starts) = the_log();
    let last = starts.len() - 2;
    let text = loggen::text(&lines);
    drop(lines);
    let tz = zone();
    tm_kernel_ffi::init().expect("init");
    let mut cache = ReplayCache::new(Some(work.to_path_buf()));
    let snap = cache.read_snapshot().expect("the stored snapshot");
    let s = kernel_log::split(text.as_bytes());
    let cut = snap.meta.cut as usize;
    let req = kernel_log::request(&kernel_log::date_of(now_of(last)), &tz, Some(&snap.ckpt), cut as u64 + 1, &s.lines[cut..], s.terminated, None, &want(), None);
    let tail_lines = s.lines.len() - cut;
    let tail_days = s.lines[cut..].iter().filter(|l| l.as_deref().is_some_and(|l| l.contains(r#""ev":"wake""#))).count();
    drop(s);
    reset_hwm();
    let before = vm_hwm_kib();
    let mut ms = Vec::new();
    for _ in 0..REPEATS {
        let t = Instant::now();
        let r = cache.replay(text.as_bytes(), now_of(last), &tz, None, &want()).expect("a hot call answers");
        ms.push(ms_since(t));
        assert_eq!(r.outcome, Outcome::Hot, "{:?}", r.rebuilt_because);
    }
    let peak = vm_hwm_kib();
    let mut dg = Vec::new();
    for _ in 0..REPEATS {
        let t = Instant::now();
        std::hint::black_box(kernel_log::fnv1a64(std::hint::black_box(&text.as_bytes()[..snap.prefix_bytes as usize])));
        dg.push(ms_since(t));
    }
    let mut kc = Vec::new();
    for _ in 0..REPEATS {
        let t = Instant::now();
        let sp = kernel_log::split(text.as_bytes());
        let req = kernel_log::request(&kernel_log::date_of(now_of(last)), &tz, Some(&snap.ckpt), cut as u64 + 1, &sp.lines[cut..], sp.terminated, None, &want(), None);
        let t2 = Instant::now();
        let a = kernel_log::log_call(&req).expect("the kernel answers").expect("not refused");
        kc.push(ms_since(t2));
        std::hint::black_box((a, t));
    }
    let (b, m, x) = stats(&ms);
    let (db, dm, _) = stats(&dg);
    let (kb, km, _) = stats(&kc);
    println!(
        "hot call (whole log's checkpoint, same day): tail {tail_lines} lines, {} B ({tail_days} wakes), ckpt {} B, request {} B; best {b:.1} / median {m:.1} / max {x:.1} ms; digest of {} B alone best {db:.2} / median {dm:.2} ms; the kernel call alone (request built, FFI, answer decoded) best {kb:.1} / median {km:.1} ms; VmHWM {:.1} -> {:.1} MiB",
        text.len() as u64 - snap.prefix_bytes,
        snap.ckpt.len(),
        req.len(),
        snap.prefix_bytes,
        mib(before),
        mib(peak)
    );
    println!("=hot_max_ms\t{x:.1}");
    println!("=hot_median_ms\t{m:.1}");
    println!("=rss_hot\t{:.1}", mib(peak));
}

/// Child: the day after the early checkpoint's, seven times from a fresh copy (§9.6's back-off reseals).
fn child_reseal(base: &Path, work: &Path) {
    let (lines, starts) = the_log();
    let day = EARLY + 1;
    let text = loggen::text(&lines[..starts[day + 1]]);
    drop(lines);
    let tz = zone();
    tm_kernel_ffi::init().expect("init");
    reset_hwm();
    let before = vm_hwm_kib();
    let mut ms = Vec::new();
    let mut last = None;
    for i in 0..REPEATS {
        let w = work.join(format!("r{i}"));
        copy_dir(base, &w);
        let mut cache = ReplayCache::new(Some(w));
        let t = Instant::now();
        let r = cache.replay(text.as_bytes(), now_of(day), &tz, None, &want()).expect("a reseal answers");
        ms.push(ms_since(t));
        assert_eq!(r.outcome, Outcome::Resealed, "{:?}", r.rebuilt_because);
        last = Some(r);
    }
    let peak = vm_hwm_kib();
    let r = last.expect("a reseal");
    let (b, m, x) = stats(&ms);
    println!(
        "reseal call (checkpoint at day {EARLY}, now day {day}): {} day and {} window records, ckpt {} B, cut {}; best {b:.1} / median {m:.1} / max {x:.1} ms; VmHWM {:.1} -> {:.1} MiB",
        r.days.len(),
        r.window.len(),
        r.snapshot.ckpt.len(),
        r.snapshot.meta.cut,
        mib(before),
        mib(peak)
    );
    println!("=reseal_median_ms\t{m:.1}");
    println!("=rss_reseal\t{:.1}", mib(peak));
}

/// One call's record in a day-by-day scenario.
struct Call {
    day: usize,
    outcome: Outcome,
    ms: f64,
    tail: usize,
    ckpt: usize,
    ledger: u64,
}

/// Runs `days` (each day's lines) from the early checkpoint, ten verbs a day, with `max_line`; prints a row a day.
fn run_days(name: &str, base: &Path, work: &Path, days: Vec<(usize, Vec<String>)>, max_line: Option<u64>) -> Vec<Call> {
    copy_dir(base, work);
    let (lines, starts) = the_log();
    let mut cur: Vec<String> = lines[..starts[EARLY + 1]].to_vec();
    drop(lines);
    let tz = zone();
    tm_kernel_ffi::init().expect("init");
    let mut cache = ReplayCache::new(Some(work.to_path_buf()));
    reset_hwm();
    let before = vm_hwm_kib();
    let mut calls = Vec::new();
    for (day, day_lines) in days {
        for verb in verbs_of(&day_lines) {
            cur.extend(verb);
            let text = loggen::text(&cur);
            let t = Instant::now();
            let r = cache.replay(text.as_bytes(), now_of(day), &tz, max_line, &want()).expect("a call answers");
            let ms = ms_since(t);
            assert_ne!(r.outcome, Outcome::GenesisUnpersisted);
            calls.push(Call {
                day,
                outcome: r.outcome,
                ms,
                tail: cur.len() - r.snapshot.meta.cut as usize,
                ckpt: r.snapshot.ckpt.len(),
                ledger: r.snapshot.meta.ledger_day,
            });
        }
    }
    let peak = vm_hwm_kib();
    let mut by_day: BTreeMap<usize, Vec<&Call>> = BTreeMap::new();
    for c in &calls {
        by_day.entry(c.day).or_default().push(c);
    }
    println!("{name}: {:>4} {:>5} {:>6} {:>22} {:>26} {:>6} {:>8} {:>10}", "day", "calls", "writes", "first call", "hot best/median/max ms", "tail", "ckpt B", "ledger day");
    for (day, cs) in &by_day {
        let writes = cs.iter().filter(|c| c.outcome != Outcome::Hot).count();
        let hot: Vec<f64> = cs.iter().filter(|c| c.outcome == Outcome::Hot).map(|c| c.ms).collect();
        let hs = if hot.is_empty() { "-".to_string() } else { let (b, m, x) = stats(&hot); format!("{b:.1}/{m:.1}/{x:.1}") };
        let last = cs.last().expect("a call");
        println!(
            "{name}: {day:>4} {:>5} {writes:>6} {:>22} {hs:>26} {:>6} {:>8} {:>10}",
            cs.len(),
            format!("{:?} {:.1} ms", cs[0].outcome, cs[0].ms),
            last.tail,
            last.ckpt,
            last.ledger
        );
    }
    println!("{name}: VmHWM {:.1} -> {:.1} MiB over {} calls", mib(before), mib(peak), calls.len());
    println!("=rss_{name}\t{:.1}", mib(peak));
    calls
}

/// Child: a ten-day stall (a block left open).
fn child_stall(base: &Path, work: &Path) {
    let (lines, starts) = the_log();
    let block = [r#""ev":"start""#, r#""ev":"stop""#, r#""ev":"done""#, r#""ev":"pause""#, r#""ev":"unpause""#, r#""ev":"interrupt""#, r#""ev":"resume""#, r#""ev":"extend""#, r#""ev":"undo""#];
    let mut days = Vec::new();
    for day in EARLY + 1..=EARLY + 10 {
        let mut d: Vec<String> = lines[starts[day]..starts[day + 1]].to_vec();
        if day == EARLY + 1 {
            // The first evening: a block started with an energy reading and never stopped.
            let wake = &d[0];
            let t0 = wake.find(r#""t":""#).expect("a stamp") + 5;
            let stamp = &wake[t0..t0 + 25];
            let (date, off) = (&stamp[..10], &stamp[19..]);
            d.push(format!(
                r#"{{"t":"{date}T23:45:00{off}","ev":"start","id":"77","pred":3,"rep":3,"hsw":17.0,"slept_min":480,"loc":"home","blocks_done":0,"since_break_min":0}}"#
            ));
        } else {
            d.retain(|l| !block.iter().any(|b| l.contains(b)));
        }
        days.push((day, d));
    }
    drop(lines);
    let calls = run_days("stall", base, work, days, None);
    let mut per_day: BTreeMap<usize, usize> = BTreeMap::new();
    for c in &calls {
        *per_day.entry(c.day).or_default() += usize::from(c.outcome != Outcome::Hot);
    }
    let hot: Vec<f64> = calls.iter().filter(|c| c.outcome == Outcome::Hot).map(|c| c.ms).collect();
    let (_, m, x) = stats(&hot);
    let first: Vec<f64> = calls.iter().filter(|c| c.outcome != Outcome::Hot).map(|c| c.ms).collect();
    let (_, fm, fx) = stats(&first);
    println!("=stall_writes_max_per_day\t{}", per_day.values().max().expect("a day"));
    println!("=stall_hot_max_ms\t{x:.1}");
    println!("=stall_hot_median_ms\t{m:.1}");
    println!("=stall_write_call_median_ms\t{fm:.1}");
    println!("=stall_write_call_max_ms\t{fx:.1}");
    println!("=stall_ledger_first_last\t{} {}", calls[0].ledger, calls.last().expect("a call").ledger);
}

/// Child: an undo stack pinning fourteen days.
fn child_pinned(base: &Path, work: &Path) {
    let (lines, starts) = the_log();
    let pin = starts[EARLY + 1] as u64;
    let days: Vec<(usize, Vec<String>)> = (EARLY + 1..=EARLY + 14).map(|d| (d, lines[starts[d]..starts[d + 1]].to_vec())).collect();
    drop(lines);
    let calls = run_days("pinned", base, work, days, Some(pin));
    let last_day = EARLY + 14;
    let hot: Vec<f64> = calls.iter().filter(|c| c.outcome == Outcome::Hot).map(|c| c.ms).collect();
    let (_, m, x) = stats(&hot);
    let hot14: Vec<f64> = calls.iter().filter(|c| c.day == last_day && c.outcome == Outcome::Hot).map(|c| c.ms).collect();
    let (_, m14, x14) = stats(&hot14);
    let mut per_day: BTreeMap<usize, usize> = BTreeMap::new();
    for c in &calls {
        *per_day.entry(c.day).or_default() += usize::from(c.outcome != Outcome::Hot);
    }
    println!("=pinned_hot_max_ms\t{x:.1}");
    println!("=pinned_hot_median_ms\t{m:.1}");
    println!("=pinned_day14_hot_median_ms\t{m14:.1}");
    println!("=pinned_day14_hot_max_ms\t{x14:.1}");
    println!("=pinned_day14_tail\t{}", calls.last().expect("a call").tail);
    println!("=pinned_writes_max_per_day\t{}", per_day.values().max().expect("a day"));
}

/// Child: a hand undo thirty days back, then ten verbs.
fn child_farundo(base: &Path, work: &Path) {
    copy_dir(base, work);
    let (mut lines, starts) = the_log();
    let last = starts.len() - 2;
    let id_of = |l: &str| -> Option<String> {
        let v: serde_json::Value = serde_json::from_str(l).ok()?;
        (v["ev"] == "done").then(|| v["id"].as_str().map(str::to_string))?
    };
    let target_day = last - 30;
    let id = lines[starts[target_day]..starts[target_day + 1]]
        .iter()
        .filter_map(|l| id_of(l))
        .find(|id| !lines[starts[target_day + 1]..].iter().any(|l| id_of(l).as_deref() == Some(id.as_str())))
        .expect("a done thirty days back whose id is not done again");
    let last_t = serde_json::from_str::<serde_json::Value>(lines.last().expect("a line")).expect("json")["t"].as_str().expect("t").to_string();
    lines.push(format!(r#"{{"t":"{last_t}","ev":"undo","of":"done","id":"{id}"}}"#));
    let tz = zone();
    tm_kernel_ffi::init().expect("init");
    let mut cache = ReplayCache::new(Some(work.to_path_buf()));
    reset_hwm();
    let before = vm_hwm_kib();
    let mut rows = Vec::new();
    for k in 0..=10 {
        if k > 0 {
            lines.push(format!(r#"{{"t":"{last_t}","ev":"note","text":"verb {k}"}}"#));
        }
        let text = loggen::text(&lines);
        let t = Instant::now();
        let r = cache.replay(text.as_bytes(), now_of(last), &tz, None, &want()).expect("a call answers");
        let ms = ms_since(t);
        let m = &r.snapshot.meta;
        let why = r.rebuilt_because.clone().map_or(String::new(), |w| format!(" ({w})"));
        rows.push((r.outcome, ms, format!("{why}; cut {}, tail {} lines, ledger day {}, reseal day {}", m.cut, lines.len() as u64 - m.cut, m.ledger_day, m.reseal_day)));
    }
    let peak = vm_hwm_kib();
    for (k, (o, ms, why)) in rows.iter().enumerate() {
        println!("far undo: call {k:>2} {o:?} {ms:.1} ms{why}");
    }
    let rebuilds = rows.iter().filter(|r| r.0 != Outcome::Hot).count();
    let first_rebuild = rows[0].0 == Outcome::Genesis;
    let hot: Vec<f64> = rows[1..].iter().map(|r| r.1).collect();
    let (_, m, x) = stats(&hot);
    println!("far undo: undo of {id}'s done on day {target_day}; VmHWM {:.1} -> {:.1} MiB", mib(before), mib(peak));
    println!("=farundo_rebuilds\t{rebuilds}");
    println!("=farundo_first_is_rebuild\t{first_rebuild}");
    println!("=farundo_later_all_hot\t{}", rows[1..].iter().all(|r| r.0 == Outcome::Hot));
    println!("=farundo_rebuild_ms\t{:.1}", rows[0].1);
    println!("=farundo_hot_median_ms\t{m:.1}");
    println!("=farundo_hot_max_ms\t{x:.1}");
    println!("=rss_farundo\t{:.1}", mib(peak));
}

fn child(args: &[&str]) -> Command {
    let mut c = Command::new(std::env::current_exe().expect("this binary"));
    c.args(args);
    c
}

fn run(args: &[&str], gate: &mut BTreeMap<String, String>) {
    let out = child(args).output().expect("spawn");
    assert!(out.status.success(), "child {args:?} failed: {}", String::from_utf8_lossy(&out.stderr));
    collect(&String::from_utf8_lossy(&out.stdout), gate);
}

fn collect(stdout: &str, gate: &mut BTreeMap<String, String>) {
    for l in stdout.lines() {
        match l.strip_prefix('=').and_then(|kv| kv.split_once('\t')) {
            Some((k, v)) => {
                gate.insert(k.to_string(), v.to_string());
            }
            None => println!("{l}"),
        }
    }
}

fn all() {
    let root = tempfile::tempdir().expect("a temp dir");
    let p = |s: &str| -> PathBuf { root.path().join(s) };
    let (full, early) = (p("full"), p("early"));
    let fs = |x: &PathBuf| x.to_str().expect("utf-8").to_string();
    let mut gate = BTreeMap::new();
    println!("windowbench (W5): 3-year log at 61 events a day, America/Chicago; debug_assertions={}", cfg!(debug_assertions));
    run(&["genesis", &fs(&full), "1094", "detail"], &mut gate);
    run(&["genesis", &fs(&early), &EARLY.to_string(), "base"], &mut gate);
    run(&["hot", &fs(&full), &fs(&p("hot"))], &mut gate);
    run(&["reseal", &fs(&early), &fs(&p("reseal"))], &mut gate);
    run(&["stall", &fs(&early), &fs(&p("stall"))], &mut gate);
    run(&["pinned", &fs(&early), &fs(&p("pinned"))], &mut gate);
    run(&["farundo", &fs(&full), &fs(&p("farundo"))], &mut gate);
    // Two processes rebuilding at once (W3's owed figure): each child's own peak.
    let a = child(&["genesis", &fs(&p("c1")), "1094", "base"]).stdout(std::process::Stdio::piped()).spawn().expect("spawn");
    let b = child(&["genesis", &fs(&p("c2")), "1094", "base"]).stdout(std::process::Stdio::piped()).spawn().expect("spawn");
    let (oa, ob) = (a.wait_with_output().expect("a child"), b.wait_with_output().expect("a child"));
    assert!(oa.status.success() && ob.status.success(), "a concurrent genesis failed");
    let mut ga = BTreeMap::new();
    let mut gb = BTreeMap::new();
    println!("two geneses at once:");
    collect(&String::from_utf8_lossy(&oa.stdout), &mut ga);
    collect(&String::from_utf8_lossy(&ob.stdout), &mut gb);
    let pa: f64 = ga["rss_base_1094"].parse().expect("a figure");
    let pb: f64 = gb["rss_base_1094"].parse().expect("a figure");
    gate.insert("rss_two_geneses_sum".into(), format!("{:.1}", pa + pb));

    let f = |k: &str| -> f64 { gate.get(k).unwrap_or_else(|| panic!("no {k}")).parse().unwrap_or_else(|_| panic!("{k}")) };
    println!("\nthe gate's figures:");
    for (k, v) in &gate {
        println!("  {k:<32} {v}");
    }
    let rss_max = gate.iter().filter(|(k, _)| k.starts_with("rss_") && *k != "rss_two_geneses_sum").map(|(_, v)| v.parse::<f64>().expect("a figure")).fold(0.0, f64::max);
    let hot_worst = f("hot_max_ms").max(f("stall_hot_max_ms")).max(f("pinned_hot_max_ms"));
    let checks = [
        ("hot call <= 60 ms incl. digest, worst of the hot, stalled and pinned hot calls", hot_worst <= 60.0, format!("{hot_worst:.1} ms")),
        ("<= 1 checkpoint write per day during the stall", f("stall_writes_max_per_day") <= 1.0, gate["stall_writes_max_per_day"].clone()),
        (
            "far undo: one rebuild, then hot calls",
            gate["farundo_rebuilds"] == "1" && gate["farundo_first_is_rebuild"] == "true" && gate["farundo_later_all_hot"] == "true",
            format!(
                "{} of 11 calls not hot, first a rebuild {}, the ten later calls all hot {} (their median {:.0} ms)",
                gate["farundo_rebuilds"], gate["farundo_first_is_rebuild"], gate["farundo_later_all_hot"], f("farundo_hot_median_ms")
            ),
        ),
        ("genesis <= 1.5 s", f("genesis_ms") <= 1_500.0, format!("{:.0} ms", f("genesis_ms"))),
        ("per-call RSS <= 256 MiB (each scenario's process peak)", rss_max <= 256.0, format!("{rss_max:.1} MiB")),
    ];
    println!("\nGATE (design §14.5 row W5):");
    for (what, ok, fig) in &checks {
        println!("  {:<4} {what}: {fig}", if *ok { "ok" } else { "FAIL" });
    }
    println!("  => {}", if checks.iter().all(|c| c.1) { "PASS" } else { "FAIL" });
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let a: Vec<&str> = args.iter().map(String::as_str).collect();
    match a[..] {
        ["genesis", dir, last, how] => child_genesis(Path::new(dir), last.parse().expect("a day"), how == "detail"),
        ["hot", base, work] => child_hot(Path::new(base), Path::new(work)),
        ["reseal", base, work] => child_reseal(Path::new(base), Path::new(work)),
        ["stall", base, work] => child_stall(Path::new(base), Path::new(work)),
        ["pinned", base, work] => child_pinned(Path::new(base), Path::new(work)),
        ["farundo", base, work] => child_farundo(Path::new(base), Path::new(work)),
        ["all"] | [] => all(),
        _ => panic!("usage: windowbench [all | genesis DIR DAY detail|base | hot|reseal|stall|pinned|farundo BASE WORK]"),
    }
}
