#!/usr/bin/env bash
# The whole differential sweep in one command: build the fork-point oracle in a
# scratch directory, run both input sets through it, and compare with the Lean
# kernel through the FFI.
#
#   ./run-oracle.sh [scratch-dir] [cases-per-seed] [seeds]
#
# Two input sets, and they answer different questions:
#
#   1. the corpus's own item lines — real tm syntax, every one with an id, so
#      the id and `est`-edit comparisons actually run on them;
#   2. the fork point's own `grammar_proptest` generator, the 512-case strategy
#      that ships, over several seeds — wide, adversarial, and mostly id-less,
#      so it is where the tokenizer differences show up.
#
#   3. the log corpus, through the `replay` and `fit` modes: the whole
#      `Replay` the fork derives from each log, key for key against the
#      kernel's own facts, and the `Model` `tm model --fit` writes from them.
#      That set is driven from `tm/tests/kernel_replay_parity.rs`, which holds
#      the decoder; this script points it at the oracle binary and runs it.
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
echo "############ input set 2: ${cases} cases x ${seeds} seeds from the fork point's grammar_proptest"
: > "$scratch/gen.jsonl"
for s in $(seq 1 "$seeds"); do
  "$oracle" gen "$cases" "$s" >> "$scratch/gen.jsonl"
done
cargo run --quiet --example oracle-compare -- "$scratch/gen.jsonl"

echo
echo "############ input set 3: the log corpus, replayed and fitted by the fork point"
# The kernel's half of this one is `tm/tests/kernel_replay_parity.rs` (it holds
# the facts decoder), so it runs from the repository root, against the oracle
# binary this script just built.  Without TM_ORACLE the test is inert, which is
# why it is `#[ignore]`d and not part of `cargo test --workspace`.
repo=$(cd "$ffi/../.." && git rev-parse --show-toplevel)
( cd "$repo" && TM_ORACLE="$oracle" cargo test --quiet --test kernel_replay_parity \
    -- --ignored --exact --nocapture \
    stage5_parity_the_kernel_replays_and_fits_as_the_fork_point_does )
