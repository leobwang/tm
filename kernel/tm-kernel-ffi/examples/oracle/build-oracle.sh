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
#   <binary> plan < requests.jsonl         the fork's planner, ranked as the
#                                          shipped binary ranks it (owner D72)
#   <binary> review < requests.jsonl       the fork's week grid, review::week_review's
#                                          heat over a world (README gap 3718)
#   <binary> capacity < requests.jsonl     the fork's lookahead, day-0 slots, slot cut,
#                                          section 7 pass and batches, the class R3
#                                          deletes from tm-core (README gap 4752, W-46
#                                          track C; tm/tests/support/forkcap.rs asks it)
#
# and feed either to `cargo run --example oracle-compare` in tm-kernel-ffi.
#
# THE PLANNER IS GRAFTED (stage 6 W-39, README gap 3533): fork 4748911's
# `planner::plan` takes no priorities, and the shipped binary has handed it the
# kernel's since `09d38fa`.  `plan-seam.patch` is exactly that commit's two edits
# to what the fork's day planning reads -- its header says which -- and it is
# applied to the extracted fork below; a patch that does not apply FAILS the
# build, and the stamp carries the patch's own hash, so a changed patch
# re-extracts the tree rather than grafting twice.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && git rev-parse --show-toplevel)
out=${1:-${TMPDIR:-/tmp}/tm-oracle}
fork=${TM_FORK:-4748911}

# The scratch tree is stamped with the ref it holds, so a changed TM_FORK (or a
# tree left by the old `main`-targeted script) is re-extracted rather than
# silently reused.
stamp="$out/.oracle-ref"
seam="$here/plan-seam.patch"
# D74's runs (parity P64, W-40 land): applied after the seam, behind an opt-in.
runs="$here/p64-runs.patch"
# The worked seam (W-44 track C, README gap 4507): fork `active_run`'s own reading of the
# running block's worked minutes, MOVED into a method the oracle's `worked` op calls --
# the oracle used to re-type it.  Applied last; its header says what it moves.
worked="$here/worked-seam.patch"
want="$(git -C "$repo" rev-parse "$fork") $(git hash-object "$seam") $(git hash-object "$runs") $(git hash-object "$worked")"
if [ ! -d "$out/tm-core" ] || [ ! -f "$stamp" ] || [ "$(cat "$stamp")" != "$want" ]; then
  echo "extracting $fork (${want%% *}) into $out" >&2
  rm -rf "$out/tm-core" "$out/tm" "$out/Cargo.toml" "$out/Cargo.lock"
  mkdir -p "$out"
  git -C "$repo" archive --format=tar "${want%% *}" | tar -x -C "$out"
  # The ceiling keeps `git apply` from finding a repository above the scratch
  # tree, where it would read the patch's paths from that repository's root.
  ( cd "$out" && export GIT_CEILING_DIRECTORIES="$(dirname "$out")" \
      && git apply --check "$seam" && git apply "$seam" \
      && git apply --check "$runs" && git apply "$runs" \
      && git apply --check "$worked" && git apply "$worked" ) || {
    echo "build-oracle.sh: $seam, $runs or $worked does not apply to $fork -- the oracle's planner would not be the one it describes" >&2
    exit 1
  }
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
