use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let pkg = manifest.parent().unwrap().join("TmKernel");

    // `lean --print-prefix` run INSIDE the package, so it honours lean-toolchain.
    let prefix = {
        let out = Command::new(which("lean"))
            .arg("--print-prefix")
            .current_dir(&pkg)
            .output()
            .expect("lean --print-prefix failed (is elan on PATH?)");
        PathBuf::from(String::from_utf8(out.stdout).unwrap().trim())
    };

    // `lake build` alone produces only .olean + .c IR.  The linkable archive is
    // the `:static` LIBRARY facet.
    let status = Command::new(which("lake"))
        .args(["build", "TmKernel:static"])
        .current_dir(&pkg)
        .status()
        .expect("failed to run lake");
    assert!(status.success(), "lake build TmKernel:static failed");

    for f in ["TmKernel.lean", "lakefile.toml", "lean-toolchain"] {
        println!("cargo:rerun-if-changed={}", pkg.join(f).display());
    }
    rerun_dir(&pkg.join("TmKernel"));

    cc::Build::new()
        .file("shim.c")
        .include(prefix.join("include"))
        .compile("tmshim");
    println!("cargo:rerun-if-changed=shim.c");

    // Stage 5 D9 W3 (design §9.8, CRIT 26): the kernel's identity is FNV-1a-64 of the archive this crate links, so a
    // replay cache written by another kernel goes to genesis once.
    let archive = pkg.join(".lake/build/lib/libTmKernel_TmKernel.a");
    let bytes = std::fs::read(&archive).expect("the kernel archive lake just built");
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    println!("cargo:rustc-env=TM_KERNEL_ID={h:016x}");
    println!("cargo:rerun-if-changed={}", archive.display());
    println!("cargo:rustc-link-search=native={}", pkg.join(".lake/build/lib").display());
    // TWO search paths: gmp/uv/ssl/crypto live in lib/, not lib/lean/.
    println!("cargo:rustc-link-search=native={}", prefix.join("lib/lean").display());
    println!("cargo:rustc-link-search=native={}", prefix.join("lib").display());

    println!("cargo:rustc-link-lib=static=TmKernel_TmKernel");
    for l in ["leancpp", "Init", "Std", "Lean", "leanrt", "Lake", "gmp", "uv", "ssl", "crypto"] {
        println!("cargo:rustc-link-lib=static={l}");
    }
    println!("cargo:rustc-link-lib=dylib=c++");

    // Linux needs a runtime search path: libc++/libc++abi/libunwind ship in the
    // toolchain's lib/ and the test binaries load them at run time (macOS
    // embeds an install_name instead).  -arg-tests covers the test binaries.
    let rpath = format!("-Wl,-rpath,{}", prefix.join("lib").display());
    println!("cargo:rustc-link-arg={rpath}");
    println!("cargo:rustc-link-arg-tests={rpath}");
}

fn which(bin: &str) -> PathBuf {
    let elan = PathBuf::from(std::env::var("HOME").unwrap()).join(".elan/bin").join(bin);
    if elan.exists() { elan } else { PathBuf::from(bin) }
}

fn rerun_dir(d: &Path) {
    if let Ok(rd) = std::fs::read_dir(d) {
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() { rerun_dir(&p); } else { println!("cargo:rerun-if-changed={}", p.display()); }
        }
    }
}
