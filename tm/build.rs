//! Runtime search path for the Lean toolchain's shared libraries.
//!
//! `tm-kernel-ffi`'s own build script links the Lean archives into every
//! dependent binary (`cargo:rustc-link-lib`/`-search` propagate across
//! crates), but `cargo:rustc-link-arg` does **not** — it applies only to the
//! emitting package's own targets. On Linux the `tm` binary and this crate's
//! test harnesses therefore need their own `-Wl,-rpath` to the toolchain's
//! `lib/`, where libc++/libc++abi/libunwind ship, or they fail at startup
//! with `libc++.so.1: cannot open shared object file`. The prefix is
//! resolved exactly the way tm-kernel-ffi's build.rs resolves it: `lean
//! --print-prefix` run inside the kernel package, so `lean-toolchain` is
//! honoured (R8).

use std::path::PathBuf;
use std::process::Command;

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let pkg = manifest.parent().unwrap().join("kernel/TmKernel");
    let out = Command::new(which("lean"))
        .arg("--print-prefix")
        .current_dir(&pkg)
        .output()
        .expect("lean --print-prefix failed (is elan on PATH?)");
    let prefix = PathBuf::from(String::from_utf8(out.stdout).unwrap().trim().to_string());
    // `rustc-link-arg` covers binaries and test harnesses alike.
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", prefix.join("lib").display());
    println!("cargo:rerun-if-changed={}", pkg.join("lean-toolchain").display());
}

fn which(bin: &str) -> PathBuf {
    let elan = PathBuf::from(std::env::var("HOME").unwrap())
        .join(".elan/bin")
        .join(bin);
    if elan.exists() {
        elan
    } else {
        PathBuf::from(bin)
    }
}
