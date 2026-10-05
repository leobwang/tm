#!/usr/bin/env bash
# **The class R3 orphans, by the binary's own symbol table** (stage 6 W-46 track C;
# kernel/README.md gap 4752, restated as a class there).
#
# Builds the `tm` binary of two trees at OPT-LEVEL 0 — the dev profile is opt-level 1,
# which inlines a small function into its caller and so hides it from `nm` (the W-45
# critic's three: `EnergyCtx::with_allow_home`, `Candidate::cap_left_min`,
# `Item::is_travel_day`) — each twice: as the linker keeps it (`--gc-sections`, the
# default: a function no reachable code references is dropped) and with
# `-C link-dead-code` (every compiled function kept).  Per tree, UNREACHED = compiled
# minus kept; the class R3 orphans = unreached in the switched tree minus unreached in
# the tree before it, `tm_core::planner::` (the file R3 deletes), closures and trait
# impls set aside.  Prints that list, one `tm_core::…` path a line.
#
#   class.sh <tree before R3> <tree after R3> <out dir>
#
# Each tree needs `kernel/TmKernel/.lake` (copy the main checkout's: `lake build` is
# then a no-op).  Run it capped, as everything here is (AGENTS §5.10a).  What it cannot
# see: a function that is reached only through a function pointer or a vtable kept by
# reachable code (it counts as reached, the safe side), and a generic function never
# instantiated in either tree (in neither list).  rsgraph.py and reach_grep.py are
# the second instrument, by the sources.
set -euo pipefail
before=$1; after=$2; out=$3
mkdir -p "$out"
for side in before after; do
  tree=${!side}
  for mode in kept compiled; do
    flags=""; [ "$mode" = compiled ] && flags="-C link-dead-code"
    ( cd "$tree" && CARGO_PROFILE_DEV_OPT_LEVEL=0 RUSTFLAGS="$flags" CARGO_TARGET_DIR="$tree/target-r3class-$mode" \
        cargo build -q -p tm )
    nm -C --defined-only "$tree/target-r3class-$mode/debug/tm" | sed -E 's/^[0-9a-f]+ [A-Za-z] //' \
      | grep -E '^(<)?tm_core::' | sed -E 's/::h[0-9a-f]{16}$//' | sort -u > "$out/$side-$mode.txt"
  done
  comm -23 "$out/$side-compiled.txt" "$out/$side-kept.txt" | grep -v '{{closure}}' | grep -v '^<' > "$out/$side-unreached.txt"
done
comm -23 "$out/after-unreached.txt" "$out/before-unreached.txt" | grep -v 'tm_core::planner::' | tee "$out/r3-orphans.txt"
echo "$(wc -l < "$out/r3-orphans.txt") functions R3 orphans; $(comm -12 "$out/after-unreached.txt" "$out/before-unreached.txt" | wc -l) unreached on both sides" >&2
