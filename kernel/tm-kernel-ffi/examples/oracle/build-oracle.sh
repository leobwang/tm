#!/usr/bin/env bash
# Stand up the `main`-side half of the differential oracle.
#
# `main` still has the Rust kernel; this branch deliberately does not, and the
# Rust must not be built inside this worktree.  So: extract `main` into a
# scratch directory, drop `tm-oracle` into it, build, and print the path of the
# binary.  Nothing is written inside the repository.
#
#   ./build-oracle.sh [scratch-dir]        default: $TMPDIR/tm-oracle
#
# Then:
#   <binary> gen 512 1                     512 lines from the shipped generator
#   <binary> parse < lines.jsonstrings     one JSON string per line
#
# and feed either to `cargo run --example oracle-compare` in tm-kernel-ffi.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && git rev-parse --show-toplevel)
out=${1:-${TMPDIR:-/tmp}/tm-oracle}

mkdir -p "$out"
if [ ! -d "$out/tm-core" ]; then
  echo "extracting main into $out" >&2
  git -C "$repo" archive --format=tar main | tar -x -C "$out"
fi

mkdir -p "$out/tm-oracle"
cp -R "$here/Cargo.toml" "$here/src" "$out/tm-oracle/"

# add it to main's workspace if it is not a member yet
if ! grep -q '"tm-oracle"' "$out/Cargo.toml"; then
  /usr/bin/sed -i.bak 's/members = \["tm-core", "tm"\]/members = ["tm-core", "tm", "tm-oracle"]/' "$out/Cargo.toml"
fi

( cd "$out" && cargo build --quiet -p tm-oracle )
echo "$out/target/debug/tm-oracle"
