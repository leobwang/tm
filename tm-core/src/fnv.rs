//! **FNV-1a-64, the binary's ONE definition** (stage 6 W-44 repair, README gap 4612).
//!
//! The shipped binary computes the 64-bit FNV-1a hash for four readers — design §9.8's prefix digest
//! of `.tm/log.jsonl` and each sealed month file's digest (the owner's D93) and the checkpoint's own
//! (the campaign's D98) in `tm/src/cli/kernel_log.rs`, the zone table's digest
//! (`tm/src/cli/tz_table.rs`, the same repair), fork 4748911's `DayPlan::hash` (`dayplan.rs`) and an
//! imported event's id (`ics.rs`) — and until the repair it computed it in four bodies, three of them
//! in this crate's and the CLI's sources: W-44 track C made the test harness's copies one
//! (`tm/tests/support/fnv.rs`, gap 4581) and left the binary's as a list.  Every one of them reads
//! this file now; `tm/tests/harness_one_fnv.rs` fails by name on a second body in the shipped
//! sources.
//!
//! Two bodies stay apart, each for a stated reason: the test harness's (a test's reading of the rule
//! is independent of the code under test) and `kernel/tm-kernel-ffi/build.rs`'s (a build script of a
//! crate outside this workspace, hashing the kernel archive at build time — it links nothing of this
//! crate and may take no new dependency, R7).  The kernel's own `Planner.fnv1a` is Lean, the other
//! side of the wire.

/// FNV-1a, 64-bit: the offset basis, then for each byte an XOR and a multiply by the prime.
pub fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in bytes {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// [`fnv1a64`] as sixteen lowercase hex digits — how a digest is spelled in a cache file and a day's
/// `hash`.
pub fn fnv1a64_hex(bytes: &[u8]) -> String {
    format!("{:016x}", fnv1a64(bytes))
}
