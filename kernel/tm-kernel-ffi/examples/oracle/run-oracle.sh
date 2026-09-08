#!/usr/bin/env bash
# The whole differential sweep in one command: build the `main`-side oracle in a
# scratch directory, run both input sets through it, and compare with the Lean
# kernel through the FFI.
#
#   ./run-oracle.sh [scratch-dir] [cases-per-seed] [seeds]
#
# Two input sets, and they answer different questions:
#
#   1. the corpus's own item lines — real tm syntax, every one with an id, so
#      the id and `est`-edit comparisons actually run on them;
#   2. `main`'s own `grammar_proptest` generator, the 512-case strategy that
#      ships, over several seeds — wide, adversarial, and mostly id-less, so it
#      is where the tokenizer differences show up.
#
# Nothing is written inside the repository and no Rust is built in this
# worktree.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
ffi=$(cd "$here/../.." && pwd)
scratch=${1:-${TMPDIR:-/tmp}/tm-oracle}
cases=${2:-512}
seeds=${3:-4}

oracle=$("$here/build-oracle.sh" "$scratch")
echo "oracle: $oracle" >&2

cd "$ffi"

echo
echo "############ input set 1: the fixture corpus's own item lines"
cargo run --quiet --example oracle-compare -- --emit-corpus-lines \
  | "$oracle" parse > "$scratch/corpus.jsonl"
cargo run --quiet --example oracle-compare -- "$scratch/corpus.jsonl"

echo
echo "############ input set 2: ${cases} cases x ${seeds} seeds from main's grammar_proptest"
: > "$scratch/gen.jsonl"
for s in $(seq 1 "$seeds"); do
  "$oracle" gen "$cases" "$s" >> "$scratch/gen.jsonl"
done
cargo run --quiet --example oracle-compare -- "$scratch/gen.jsonl"
