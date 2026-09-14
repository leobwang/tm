//! **tzprobe: the wall time of one zone probe** (stage 5 D9 step B4; design §6.1;
//! kernel/README.md gap 103). `logbench` (c) runs it as a child process, because
//! the probe is `tm/src/cli/tz_table.rs`, whose chrono-tz the kernel's FFI crate
//! does not depend on.
//!
//! ```text
//! systemd-run --user --scope -p MemoryMax=16G -p MemorySwapMax=0 --quiet \
//!   cargo run --example tzprobe -p tm -- America/Chicago
//! ```
//!
//! Prints one tab-separated record: zone, best ms, median ms (of 7 probes),
//! transitions, first and last transition, wire bytes, and `VmHWM` in KiB.

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

use std::time::Instant;

const REPEATS: usize = 7;

fn vm_hwm_kib() -> u64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    s.lines()
        .find_map(|l| l.strip_prefix("VmHWM:"))
        .and_then(|v| v.trim().trim_end_matches("kB").trim().parse().ok())
        .unwrap_or(0)
}

fn main() {
    let name = std::env::args().nth(1).unwrap_or_else(|| "America/Chicago".to_string());
    let tz: chrono_tz::Tz = match name.parse() {
        Ok(tz) => tz,
        Err(e) => {
            eprintln!("tzprobe: {name}: {e}");
            std::process::exit(2);
        }
    };
    let mut ms = Vec::with_capacity(REPEATS);
    let mut table = None;
    for _ in 0..REPEATS {
        let s = Instant::now();
        let t = std::hint::black_box(tz_table::probe(tz));
        ms.push(s.elapsed().as_secs_f64() * 1000.0);
        table = Some(t);
    }
    ms.sort_by(|a, b| a.total_cmp(b));
    let Some(table) = table else { return };
    let wire = table.to_wire().to_string();
    let first = table.transitions.first().map_or("-".to_string(), |&(t, _)| tz_table::fmt_instant(t));
    let last = table.transitions.last().map_or("-".to_string(), |&(t, _)| tz_table::fmt_instant(t));
    println!(
        "{name}\t{:.1}\t{:.1}\t{}\t{first}\t{last}\t{}\t{}",
        ms[0],
        ms[REPEATS / 2],
        table.transitions.len(),
        wire.len(),
        vm_hwm_kib()
    );
}
