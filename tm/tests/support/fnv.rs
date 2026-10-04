//! **FNV-1a-64, the test harness's ONE definition** (stage 6 W-44 track C; README gaps 4504 and 4581).
//!
//! The harness computes the 64-bit FNV-1a digest for three readers — design §9.8's `prefixFnv` over a
//! generated log (`loggen`), each sealed month file's digest in the replay cache's manifest
//! (`cli_common::fnv1a64_hex`, the owner's D93) and fork 4748911's `DayPlan::hash` over a serialised day
//! (`forkplan::day_hash`) — and until W-44 it computed it in three places, the W-43 repair having made
//! three copies one in `cli_common` while the class still had three members.  Each reader includes this
//! file by `#[path]`, so there is one body.
//!
//! It is the harness's own and never the binary's (`kernel_log::fnv1a64`) or the fork's: a test's reading
//! of the rule stays independent of the code under test.  Dependency-free on purpose, like `loggen.rs`,
//! which `kernel/tm-kernel-ffi/examples/logbench.rs` includes from another crate.

/// FNV-1a, 64-bit: the offset basis, then for each byte an XOR and a multiply by the prime.
pub fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in bytes {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// [`fnv1a64`] as sixteen lowercase hex digits — how the replay cache's manifest and a frozen day's
/// `hash` spell it.
pub fn fnv1a64_hex(bytes: &[u8]) -> String {
    format!("{:016x}", fnv1a64(bytes))
}
