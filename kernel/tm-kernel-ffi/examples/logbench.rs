//! **logbench: the log's costs, measured rather than estimated** (stage 5 step
//! A3; design `kernel/design/stage5/stage5-D9-D10-design.md` §14.1 row A3, §18).
//!
//! Run it capped, from `kernel/tm-kernel-ffi`, under tm's dev profile
//! (`opt-level = 1`, the root `Cargo.toml`; this crate is its own workspace, so
//! the profile is passed in):
//!
//! ```text
//! systemd-run --user --scope -p MemoryMax=16G -p MemorySwapMax=0 --quiet \
//!   env CARGO_PROFILE_DEV_OPT_LEVEL=1 cargo run --example logbench
//! ```
//!
//! It prints wall milliseconds and `VmHWM` for:
//! - **(a)** the kernel's wire parse of the log as a line array,
//!   `{"docs":[],"pad":["<line>",…]}`, at 1 month, 6 months, 1 year and 3 years
//!   at 40 and 61 events a day.  No reader reads `pad`, so the whole request is
//!   parsed and an empty `ok` answers; the response is checked.  (A3 sent the
//!   array under `log`; since B4 that key is the log op's section, and an array
//!   there is refused `tzAbsent`, so the key moved.  The parse is the same.)
//! - **(b)** FNV-1a-64 over 6.9 MiB of log text, in this process.
//! - **(c)** the hourly zone probe for America/Chicago (design §6.1; gap 103,
//!   closed at B4).  The probe is `tm/src/cli/tz_table.rs`, and this crate does
//!   not depend on chrono-tz, so (c) runs tm's `examples/tzprobe.rs` as a child
//!   (`cargo run --example tzprobe -p tm`, the root workspace's dev profile) and
//!   prints its record: best and median of 7 probes, transitions, wire bytes,
//!   `VmHWM`.
//! - **(d)** RSS for a call carrying a 1 MiB and a 4 MiB line array (line
//!   bytes, §9.7's chunk and resend caps).  **Gate:** at 4 MiB, above 256 MiB
//!   means §9.7's resend cap is lowered before W3.
//! - **(e)** the `log` op itself (stage 5 D9 B4): every line read by
//!   `Log.readLine`, a header for each, no rendering, at the 1 MiB cut and at the
//!   per-call bound (8,192 lines since W3).  Since W3 a request asking for headers
//!   resumes from the empty checkpoint, so (e) replays too.
//! - **(f)** (W3, gap 102) **the memory gate for one resend-shaped call**: a
//!   genesis call from the empty checkpoint with a reseal and facts, no headers, at
//!   4,096 and 8,192 lines of the 3-year log (the line bound; 16,384 lines measured
//!   218.9 MiB before the kernel's bound fell to 8,192, and is refused since), and 8,192
//!   lines of long note text at 1,536, 1,792 and 1,920 KiB (the byte bound's worst
//!   shape).  **Gate:** the resend cap is the largest power-of-two line count, and a
//!   byte bound, whose peak `VmHWM` is at most 200 MiB.
//!
//! Every call-bearing measurement runs in a child process of its own (this
//! binary, re-executed with a subcommand), because `VmHWM` only ever rises.
//! The logs are `tm/tests/support/loggen.rs`, the design pass's generator ported
//! byte for byte, generated in its order (`design_logs`), so the sizes are §1.1's.

#[allow(dead_code)]
#[path = "../../../tm/tests/support/loggen.rs"]
mod loggen;

use loggen::{fnv1a64, text, LogGen, Rate, AGES, SEED};
use std::process::Command;
use std::time::Instant;

const MIB: f64 = 1024.0 * 1024.0;

/// Wall-clock repeats per measurement; the best is quoted, the median beside it.
const REPEATS: usize = 7;

fn vm_hwm_kib() -> u64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    s.lines()
        .find_map(|l| l.strip_prefix("VmHWM:"))
        .and_then(|v| v.trim().trim_end_matches("kB").trim().parse().ok())
        .unwrap_or(0)
}

fn mib(kib: u64) -> f64 {
    kib as f64 / 1024.0
}

/// A JSON string literal for a line.  The generator writes only printable
/// ASCII, so `"` and `\` are the only escapes (checked).
fn jstr(out: &mut String, l: &str) {
    out.push('"');
    for c in l.chars() {
        assert!((' '..='~').contains(&c), "loggen wrote a byte this escaper does not handle");
        if c == '"' || c == '\\' {
            out.push('\\');
        }
        out.push(c);
    }
    out.push('"');
}

fn request(lines: &[String]) -> String {
    let mut r = String::with_capacity(lines.iter().map(|l| l.len() + 24).sum::<usize>() + 32);
    r.push_str(r#"{"docs":[],"pad":["#);
    for (i, l) in lines.iter().enumerate() {
        if i > 0 {
            r.push(',');
        }
        jstr(&mut r, l);
    }
    r.push_str("]}");
    r
}

fn rate_of(s: &str) -> Rate {
    match s {
        "40" => Rate::Forty,
        "61" => Rate::SixtyOne,
        _ => panic!("rate is 40 or 61"),
    }
}

/// The design pass's file at `rate` and `age`: the scripts' generator run in
/// their order, stopping at `age` (what `design_logs` returns, without
/// generating the ages after it).
fn lines_of(rate: Rate, age: &str) -> Vec<String> {
    let mut g = LogGen::new(rate, SEED);
    for &(a, days) in AGES.iter() {
        let lines = g.days(days);
        if a == age {
            return lines;
        }
    }
    panic!("age is one of 1mo, 6mo, 1y, 3y")
}

/// Resets `VmHWM` to the current RSS (`clear_refs` value 5, Linux 4.0+), so a
/// child's peak is the call's, not the generator's transient allocations.
/// Returns whether the reset took; if not, the peak includes generation.
fn reset_hwm() -> bool {
    std::fs::write("/proc/self/clear_refs", "5").is_ok()
}

/// Times `REPEATS` calls (or `LOGBENCH_REPEATS`); returns (best ms, median ms).
fn time_calls(req: &str) -> (f64, f64) {
    let repeats = std::env::var("LOGBENCH_REPEATS").ok().and_then(|v| v.parse().ok()).unwrap_or(REPEATS);
    let mut ms: Vec<f64> = (0..repeats)
        .map(|_| {
            let s = Instant::now();
            let out = tm_kernel_ffi::call(req).expect("kernel fault");
            let e = s.elapsed().as_secs_f64() * 1000.0;
            assert!(out.starts_with(r#"{"ok":"#), "unexpected response: {}", &out[..out.len().min(120)]);
            e
        })
        .collect();
    ms.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (ms[0], ms[repeats / 2])
}

/// Child: one parse measurement.  Prints one tab-separated record.
fn child_parse(rate: Rate, age: &str) {
    let lines = lines_of(rate, age);
    let line_bytes = text(&lines).len();
    let req = request(&lines);
    drop(lines);
    tm_kernel_ffi::init().expect("init");
    assert!(reset_hwm(), "cannot reset VmHWM");
    let before = vm_hwm_kib();
    let (best, median) = time_calls(&req);
    let after = vm_hwm_kib();
    println!(
        "{}\t{}\t{}\t{}\t{best:.2}\t{median:.2}\t{before}\t{after}",
        rate.label(),
        age,
        req.len(),
        line_bytes,
    );
}

/// Child: a prefix of the 3-year, 61-a-day log, cut by `how`: `mib N` takes the
/// longest prefix within N MiB of line bytes (each line counted with its
/// newline, as §9.7 counts them); `lines N` takes N lines.
fn child_rss(how: &str, n_arg: usize) {
    let all = lines_of(Rate::SixtyOne, "3y");
    let n = match how {
        "mib" => {
            let mut used = 0;
            all.iter().take_while(|l| { used += l.len() + 1; used <= n_arg << 20 }).count()
        }
        _ => n_arg.min(all.len()),
    };
    let lines: Vec<String> = all.into_iter().take(n).collect();
    let line_bytes = text(&lines).len();
    let req = request(&lines);
    drop(lines);
    tm_kernel_ffi::init().expect("init");
    assert!(reset_hwm(), "cannot reset VmHWM");
    let before = vm_hwm_kib();
    let (best, median) = time_calls(&req);
    let after = vm_hwm_kib();
    println!("{how} {n_arg}\t{n}\t{line_bytes}\t{}\t{best:.2}\t{median:.2}\t{before}\t{after}", req.len());
}

/// Child: the `log` op over a prefix of the 3-year, 61-a-day log, cut as
/// `child_rss` cuts it, with a header for every line.
fn child_logop(how: &str, n_arg: usize) {
    let all = lines_of(Rate::SixtyOne, "3y");
    let n = match how {
        "mib" => {
            let mut used = 0;
            all.iter().take_while(|l| { used += l.len() + 1; used <= n_arg << 20 }).count()
        }
        _ => n_arg.min(all.len()),
    };
    let lines: Vec<String> = all.into_iter().take(n).collect();
    let line_bytes = text(&lines).len();
    let mut req = String::from(r#"{"docs":[],"now":"2029-01-01","tz":{"key":"UTC","base":"+00:00:00","then":[]},"log":{"ckpt":null,"from":1,"lines":["#);
    for (i, l) in lines.iter().enumerate() {
        if i > 0 {
            req.push(',');
        }
        jstr(&mut req, l);
    }
    req.push_str(r#"],"terminated":true,"want":{"headersFrom":1}}}"#);
    drop(lines);
    tm_kernel_ffi::init().expect("init");
    assert!(reset_hwm(), "cannot reset VmHWM");
    let before = vm_hwm_kib();
    let (best, median) = time_calls(&req);
    let after = vm_hwm_kib();
    println!("{how} {n_arg}\t{n}\t{line_bytes}\t{}\t{best:.2}\t{median:.2}\t{before}\t{after}", req.len());
}

/// The prefix of the 3-year, 61-a-day log a cut names: `mib N` / `kib N` the longest prefix within that many
/// bytes of lines (each line counted with its newline, as §9.7 counts them), `lines N` the first N lines.
fn cut_of(how: &str, n_arg: usize) -> Vec<String> {
    let all = lines_of(Rate::SixtyOne, "3y");
    let bytes = match how {
        "mib" => Some(n_arg << 20),
        "kib" => Some(n_arg << 10),
        _ => None,
    };
    let n = match bytes {
        Some(b) => {
            let mut used = 0;
            all.iter().take_while(|l| { used += l.len() + 1; used <= b }).count()
        }
        None => n_arg.min(all.len()),
    };
    all.into_iter().take(n).collect()
}

/// Child (W3, gap 102): **one `log` call with its facts** over a cut of the 3-year, 61-a-day log, the call a
/// genesis resend makes: every line read and replayed, the facts and a header for every line emitted.  Before
/// W3's wire it is a call with `ckpt: null` and `want.facts`; W3 adds `reseal` (the resend's shape).
fn child_logfacts(how: &str, n_arg: usize, reseal: bool) {
    let lines = cut_of(how, n_arg);
    let n = lines.len();
    let line_bytes = text(&lines).len();
    let mut req = String::from(r#"{"docs":[],"now":"2029-01-01","tz":{"key":"UTC","base":"+00:00:00","then":[]},"log":{"ckpt":null,"from":1,"lines":["#);
    for (i, l) in lines.iter().enumerate() {
        if i > 0 {
            req.push(',');
        }
        jstr(&mut req, l);
    }
    req.push_str(r#"],"terminated":true,"#);
    req.push_str(if reseal { r#""reseal":{"keepDays":2,"maxLine":null},"# } else { r#""reseal":null,"# });
    // `LOGBENCH_FACTS=0` / `LOGBENCH_HEADERS=0` drop what a call asks for, to measure the resend's own shape (a genesis
    // call asks facts only at the log's end, and headers never).
    let facts = std::env::var("LOGBENCH_FACTS").map_or(true, |v| v != "0");
    let headers = std::env::var("LOGBENCH_HEADERS").map_or(true, |v| v != "0");
    req.push_str(&format!(r#""want":{{"facts":{facts},"headersFrom":{}}}}}}}"#, if headers { "1" } else { "null" }));
    drop(lines);
    tm_kernel_ffi::init().expect("init");
    assert!(reset_hwm(), "cannot reset VmHWM");
    let before = vm_hwm_kib();
    let (best, median) = time_calls(&req);
    let after = vm_hwm_kib();
    println!("{how} {n_arg}\t{n}\t{line_bytes}\t{}\t{best:.2}\t{median:.2}\t{before}\t{after}", req.len());
}

/// Child (W3, gap 102): **the byte bound's worst shape**: 8,192 `note` lines padded to `kib` KiB of line bytes in all
/// (each counted with its newline), in one resend-shaped call (`ckpt: null`, a reseal, facts, no headers).  A line's text
/// costs the kernel a list cell a character in the request, the line and the entry, so long lines are the heaviest bytes.
fn child_logpad(lines: usize, kib: usize) {
    let head = r#"{"t":"2026-09-07T06:05:00-05:00","ev":"note","text":""#;
    let per = (kib << 10) / lines;
    let pad = per.saturating_sub(head.len() + 3);
    let line = format!(r#"{head}{}"}}"#, "y".repeat(pad));
    let all: Vec<String> = vec![line; lines];
    let line_bytes = text(&all).len();
    let mut req = String::from(r#"{"docs":[],"now":"2029-01-01","tz":{"key":"UTC","base":"+00:00:00","then":[]},"log":{"ckpt":null,"from":1,"lines":["#);
    for (i, l) in all.iter().enumerate() {
        if i > 0 {
            req.push(',');
        }
        jstr(&mut req, l);
    }
    req.push_str(r#"],"terminated":true,"reseal":{"keepDays":2,"maxLine":null},"want":{"facts":true,"headersFrom":null}}}"#);
    drop(all);
    tm_kernel_ffi::init().expect("init");
    assert!(reset_hwm(), "cannot reset VmHWM");
    let before = vm_hwm_kib();
    let (best, median) = time_calls(&req);
    let after = vm_hwm_kib();
    println!("pad {kib}\t{lines}\t{line_bytes}\t{}\t{best:.2}\t{median:.2}\t{before}\t{after}", req.len());
}

/// Child: the process and runtime alone, for the baseline under every figure.
fn child_empty() {
    tm_kernel_ffi::init().expect("init");
    let (best, median) = time_calls(r#"{"docs":[]}"#);
    println!("{best:.3}\t{median:.3}\t{}", vm_hwm_kib());
}

fn spawn(args: &[&str]) -> Vec<String> {
    spawn_env(args, &[])
}

fn spawn_env(args: &[&str], env: &[(&str, &str)]) -> Vec<String> {
    let exe = std::env::current_exe().unwrap();
    let out = Command::new(exe).args(args).envs(env.iter().copied()).output().expect("spawn");
    assert!(out.status.success(), "child {args:?} failed: {}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8(out.stdout).unwrap().trim().split('\t').map(str::to_owned).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.iter().map(String::as_str).collect::<Vec<_>>()[..] {
        ["parse", rate, age] => return child_parse(rate_of(rate), age),
        ["rss", how, n] => return child_rss(how, n.parse().expect("a count")),
        ["logop", how, n] => return child_logop(how, n.parse().expect("a count")),
        ["logfacts", how, n] => return child_logfacts(how, n.parse().expect("a count"), false),
        ["logreseal", how, n] => return child_logfacts(how, n.parse().expect("a count"), true),
        ["only-f"] => return table_f(),
        ["logpad", lines, kib] => return child_logpad(lines.parse().expect("a count"), kib.parse().expect("a count")),
        ["empty"] => return child_empty(),
        [] => {}
        _ => panic!("usage: logbench [parse 40|61 AGE | rss mib|lines N | logop mib|lines N | logfacts|logreseal mib|kib|lines N | only-f | empty]"),
    }

    println!("logbench (stage 5 A3): best of {REPEATS} calls, median beside it; VmHWM of a fresh process, reset to its RSS just before the calls (\"pre\")");
    println!(
        "profile: debug_assertions={}; the kernel archive is lake's, whatever the Rust profile",
        cfg!(debug_assertions)
    );

    let e = spawn(&["empty"]);
    let base_kib: u64 = e[2].parse().unwrap();
    println!("\nbaseline: {{\"docs\":[]}} best {} ms (median {}), VmHWM {:.1} MiB", e[0], e[1], mib(base_kib));

    println!("\n(a) wire parse, the log as a line array {{\"docs\":[],\"pad\":[...]}}");
    println!(
        "{:>7} {:>4} {:>7} {:>10} {:>10} {:>9} {:>9} {:>8} {:>10} {:>10} {:>11}",
        "rate", "age", "lines", "line B", "request B", "best ms", "median", "ms/MiB", "HWM pre", "HWM post", "MiB/MiB req"
    );
    for rate in ["40", "61"] {
        for (age, _) in AGES {
            let r = spawn(&["parse", rate, age]);
            let req_b: f64 = r[2].parse().unwrap();
            let best: f64 = r[4].parse().unwrap();
            let pre: u64 = r[6].parse().unwrap();
            let post: u64 = r[7].parse().unwrap();
            let lines = lines_of(rate_of(rate), age).len();
            println!(
                "{:>7} {:>4} {:>7} {:>10} {:>10} {:>9} {:>9} {:>8.1} {:>7.1} MiB {:>6.1} MiB {:>11.1}",
                r[0],
                r[1],
                lines,
                r[3],
                r[2],
                r[4],
                r[5],
                best / (req_b / MIB),
                mib(pre),
                mib(post),
                mib(post.saturating_sub(pre)) / (req_b / MIB)
            );
        }
    }

    println!("\n(b) FNV-1a-64 over 6.9 MiB of log text, in this process");
    let log = text(&lines_of(Rate::SixtyOne, "3y"));
    let want = (6.9 * MIB) as usize;
    let buf: Vec<u8> = log.as_bytes().iter().copied().cycle().take(want).collect();
    let mut ms: Vec<(f64, u64)> = (0..REPEATS)
        .map(|_| {
            let s = Instant::now();
            let h = std::hint::black_box(fnv1a64(std::hint::black_box(&buf)));
            (s.elapsed().as_secs_f64() * 1000.0, h)
        })
        .collect();
    ms.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
    println!(
        "{} B: best {:.2} ms (median {:.2}), {:.3} ns/B; digest {:016x}",
        buf.len(),
        ms[0].0,
        ms[REPEATS / 2].0,
        ms[0].0 * 1e6 / buf.len() as f64,
        ms[0].1
    );

    println!("\n(c) hourly zone probe, America/Chicago (tm/src/cli/tz_table.rs via tm's examples/tzprobe.rs)");
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../Cargo.toml");
    let out = Command::new("cargo")
        .args(["run", "--quiet", "--example", "tzprobe", "-p", "tm", "--manifest-path", root, "--", "America/Chicago"])
        .output()
        .expect("spawn cargo");
    assert!(out.status.success(), "tzprobe failed: {}", String::from_utf8_lossy(&out.stderr));
    let r: Vec<String> = String::from_utf8(out.stdout).unwrap().trim().split('\t').map(str::to_owned).collect();
    println!(
        "{}: best {} ms (median {}), {} transitions ({} .. {}), {} B on the wire, VmHWM {:.1} MiB",
        r[0], r[1], r[2], r[3], r[4], r[5], r[6], mib(r[7].parse().unwrap())
    );

    println!("\n(d) RSS for one call carrying a line array (3y @61/day prefix)");
    println!(
        "{:>11} {:>7} {:>10} {:>10} {:>9} {:>9} {:>10} {:>10} {:>9}",
        "cut", "lines", "line B", "request B", "best ms", "median", "HWM pre", "HWM post", "gate"
    );
    // The two rows the design names, then the resend cap's line bound and the
    // sizes between, so the owner can see where 256 MiB falls.
    for (how, n) in [("mib", "1"), ("mib", "4"), ("lines", "32768"), ("mib", "2"), ("mib", "3")] {
        let r = spawn(&["rss", how, n]);
        let post: u64 = r[7].parse().unwrap();
        let gate = match (how, n) {
            ("mib", "4") if mib(post) <= 256.0 => "ok <=256",
            ("mib", "4") => "BREACH",
            _ => "-",
        };
        println!(
            "{:>11} {:>7} {:>10} {:>10} {:>9} {:>9} {:>6.1} MiB {:>6.1} MiB {:>9}",
            r[0],
            r[1],
            r[2],
            r[3],
            r[4],
            r[5],
            mib(r[6].parse().unwrap()),
            mib(post),
            gate
        );
    }

    println!("\n(e) the log op (grammar only: every line read, a header each), 3y @61/day prefix");
    println!(
        "{:>11} {:>7} {:>10} {:>10} {:>9} {:>9} {:>10} {:>10}",
        "cut", "lines", "line B", "request B", "best ms", "median", "HWM pre", "HWM post"
    );
    // W3 (gap 102): the per-call bound is the memory gate's 8,192 lines; a larger cut is refused `tooManyLines`.
    for (how, n) in [("mib", "1"), ("lines", "8192")] {
        let r = spawn(&["logop", how, n]);
        println!(
            "{:>11} {:>7} {:>10} {:>10} {:>9} {:>9} {:>6.1} MiB {:>6.1} MiB",
            r[0],
            r[1],
            r[2],
            r[3],
            r[4],
            r[5],
            mib(r[6].parse().unwrap()),
            mib(r[7].parse().unwrap())
        );
    }

    table_f();
}

/// **(f) the memory gate for one resend-shaped call (W3, gap 102).**  A genesis resend is one call carrying every line
/// from a popped checkpoint through the refusing chunk, with a reseal, and facts when it reaches the log's end: read,
/// replayed, resealed, its facts and records emitted.  The cap is chosen by this table: the largest power-of-two line count,
/// and a byte bound, whose peak `VmHWM` is at most 200 MiB (22% under design §14.1's 256 MiB gate).  Rows at and around the
/// cap are measured, and one past it each way.  `LOGBENCH_F=how:n,…` measures other rows (`lines`, `kib` or `pad`).
fn table_f() {
    println!("\n(f) one resend-shaped call (ckpt null, reseal {{keepDays 2}}, facts, no headers); gate: peak <= 200 MiB");
    println!(
        "{:>11} {:>7} {:>10} {:>10} {:>9} {:>9} {:>10} {:>10} {:>9}",
        "cut", "lines", "line B", "request B", "best ms", "median", "HWM pre", "HWM post", "gate"
    );
    let rows: Vec<(String, String)> = match std::env::var("LOGBENCH_F") {
        Ok(v) => v.split(',').map(|c| { let (h, n) = c.split_once(':').expect("how:n"); (h.to_string(), n.to_string()) }).collect(),
        // 16,384 lines was measured before the kernel's bound fell to 8,192 (218.9 MiB, README "Stage 5 D9 W3"); the
        // kernel now refuses it `tooManyLines`, so the table stops at the cap.
        Err(_) => [("lines", "4096"), ("lines", "8192"), ("pad", "1536"), ("pad", "1792"), ("pad", "1920")]
            .iter()
            .map(|(h, n)| (h.to_string(), n.to_string()))
            .collect(),
    };
    for (how, n) in rows {
        let r = if how == "pad" {
            spawn_env(&["logpad", "8192", &n], &[])
        } else {
            spawn_env(&["logreseal", &how, &n], &[("LOGBENCH_HEADERS", "0")])
        };
        let post: u64 = r[7].parse().unwrap();
        let gate = if mib(post) <= 200.0 { "ok <=200" } else { "OVER" };
        println!(
            "{:>11} {:>7} {:>10} {:>10} {:>9} {:>9} {:>6.1} MiB {:>6.1} MiB {:>9}",
            r[0], r[1], r[2], r[3], r[4], r[5], mib(r[6].parse().unwrap()), mib(post), gate
        );
    }
}
