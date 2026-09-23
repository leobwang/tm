#!/usr/bin/env bash
# Stand up the fork-point half of the differential oracle.
#
# The fork point `4748911` is the last commit that still carries the Rust
# implementation this kernel is a port of; `main` was DISCARDED on 2026-09-12
# (README "`main` DISCARDED", AGENTS §2.2), so this script used to fail before
# it built anything (AGENTS §7.3, "Broken in this clone, and owed").  Every
# "no disagreement" it prints from here on is against the fork-point grammar
# and the fork-point replay, whose delta to `main@557a3d2` is stage 0's fix.
#
# The Rust must not be built inside this worktree, so: extract the fork point
# into a scratch directory, drop `tm-oracle` into it, build, and print the path
# of the binary.  Nothing is written inside the repository.
#
#   ./build-oracle.sh [scratch-dir]        default: $TMPDIR/tm-oracle
#   TM_FORK=<ref> ./build-oracle.sh        build against another ref
#
# Then:
#   <binary> gen 512 1                     512 lines from the shipped generator
#   <binary> parse < lines.jsonstrings     one JSON string per line
#   <binary> replay <tz> < log.jsonstrings the fork's `log::replay`, as JSON
#
# and feed either to `cargo run --example oracle-compare` in tm-kernel-ffi.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && git rev-parse --show-toplevel)
out=${1:-${TMPDIR:-/tmp}/tm-oracle}
fork=${TM_FORK:-4748911}

# The scratch tree is stamped with the ref it holds, so a changed TM_FORK (or a
# tree left by the old `main`-targeted script) is re-extracted rather than
# silently reused.
stamp="$out/.oracle-ref"
want=$(git -C "$repo" rev-parse "$fork")
if [ ! -d "$out/tm-core" ] || [ ! -f "$stamp" ] || [ "$(cat "$stamp")" != "$want" ]; then
  echo "extracting $fork ($want) into $out" >&2
  rm -rf "$out/tm-core" "$out/tm" "$out/Cargo.toml" "$out/Cargo.lock"
  mkdir -p "$out"
  git -C "$repo" archive --format=tar "$want" | tar -x -C "$out"
  printf '%s\n' "$want" > "$stamp"
fi

mkdir -p "$out/tm-oracle"
cp -R "$here/Cargo.toml" "$here/src" "$out/tm-oracle/"

# THE GENERATOR IS ONE DEFINITION, and this is the line that makes it one.
#
# `src/main.rs` held 186 lines copied out of the fork's own proptest, with two
# comments naming the file they came from; W-25 moved those strategies to
# `tm-core/tests/grammar_common/mod.rs` so that `tm/tests/kernel_item_grammar.rs`
# and `tm-core/tests/grammar_proptest.rs` would draw the SAME lines, and left
# this third copy behind pointing at a file that no longer held one.  The
# fork-point checkout extracted above predates that module, so the oracle cannot
# reach it from there: it is copied in, and a missing one is a HARD ERROR rather
# than a build that quietly samples something else.
common="$repo/tm-core/tests/grammar_common/mod.rs"
if [ ! -f "$common" ]; then
  echo "build-oracle.sh: $common is missing -- the oracle's generator lives there" >&2
  exit 1
fi
cp "$common" "$out/tm-oracle/src/grammar_common.rs"

# add it to the fork's workspace if it is not a member yet.  Written through a
# temp file: `sed -i` spells its backup suffix differently on GNU and BSD.
if ! grep -q '"tm-oracle"' "$out/Cargo.toml"; then
  sed 's/members = \["tm-core", "tm"\]/members = ["tm-core", "tm", "tm-oracle"]/' \
    "$out/Cargo.toml" > "$out/Cargo.toml.new"
  grep -q '"tm-oracle"' "$out/Cargo.toml.new" || {
    echo "build-oracle.sh: could not add tm-oracle to $out/Cargo.toml's members" >&2
    exit 1
  }
  mv "$out/Cargo.toml.new" "$out/Cargo.toml"
fi

( cd "$out" && cargo build --quiet -p tm-oracle )
echo "$out/target/debug/tm-oracle"
