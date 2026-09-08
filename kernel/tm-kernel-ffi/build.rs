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

    println!("cargo:rustc-link-search=native={}", pkg.join(".lake/build/lib").display());
    // TWO search paths: gmp/uv/ssl/crypto live in lib/, not lib/lean/.
    println!("cargo:rustc-link-search=native={}", prefix.join("lib/lean").display());
    println!("cargo:rustc-link-search=native={}", prefix.join("lib").display());

    println!("cargo:rustc-link-lib=static=TmKernel_TmKernel");
    for l in ["leancpp", "Init", "Std", "Lean", "leanrt", "Lake", "gmp", "uv", "ssl", "crypto"] {
        println!("cargo:rustc-link-lib=static={l}");
    }
    println!("cargo:rustc-link-lib=dylib=c++");
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
