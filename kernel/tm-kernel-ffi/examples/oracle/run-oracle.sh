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
#   4. every log LINE the grammar tests feed, through the `parse-entry` mode:
#      the fork's per-line acceptance — is this an entry, a warning or blank,
#      and what entry is it — against the kernel's `log` op.  That is T1-T3's
#      oracle after design §12 deletes the in-tree parser (owner decision D23,
#      README gap 148).  It is driven from `tm/tests/kernel_log_grammar.rs`,
#      which holds the input sets; this script points it at the oracle and runs
#      the two arms that need it: the re-bless of the frozen verdicts, and the
#      round trip the frozen file cannot make (the fork reading back every
#      rendering the kernel writes).
#
#   5. the week grid, through the `review` mode: fork 4748911's heat grid of
#      every frozen world and of fresh generated weeks, cell for cell against
#      the shipped binary's `tm review week` with parity P63's cells moved by
#      its rule (README gap 3718).  Driven from `tm/tests/fork_week_grid.rs`.
#
#   6. the planner, through the `plan` mode (owner D72): every frozen class,
#      batch and driven line, and every frozen P56 day (README gap 3719), still
#      fork 4748911's answer, and fresh draws -- the class draw's and the
#      seeded P56 days' --
#      against the kernel with every registered departure applied by its
#      property.  Driven from `tm/tests/planner_classes.rs`,
#      `tm/tests/planner_invariants.rs` and `tm/tests/planner_p56_cut.rs`; these
#      are the arms that outlive R3, so this set is the fork's last word on the
#      planner once `tm-core/src/planner.rs` is gone.
#
#   7. every other arm, by the class and not by a list (the W-46 audit, README
#      gap 4896): the whole workspace under TM_ORACLE — the capacity arms of
#      track C's targets ask `tm-oracle capacity` live — and every `#[ignore]`d
#      arm `arms.py` reads off the test sources that sets 3-6 do not name.
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

echo
echo "############ input set 4: every log line the grammar tests feed, per-line"
# The kernel's half is `tm/tests/kernel_log_grammar.rs` (it holds the input
# sets).  The round trip runs against the oracle; the re-bless does NOT run
# here, because rewriting a committed fixture is a decision and never part of a
# sweep (AGENTS §7.2) — it needs TM_FORK_BLESS as well, and its command is in
# that file's GAP 148 banner.
( cd "$repo" && TM_ORACLE="$oracle" cargo test --quiet --test kernel_log_grammar \
    -- --ignored --exact --nocapture \
    the_fork_reads_back_every_rendering_the_kernel_writes )

echo
echo "############ input set 5: the week grid, through the review mode"
# The kernel's half is `tm/tests/fork_week_grid.rs` (it holds the worlds and the
# shipped binary's review of each): every frozen grid still fork 4748911's answer,
# and fresh weeks drawn and compared cell by cell with P63's cells applied by its
# rule (README gap 3718).  The bless does NOT run here (AGENTS §7.2): it needs
# TM_GRID_BLESS as well, and its command is in that file.
( cd "$repo" && TM_ORACLE="$oracle" cargo test --quiet -p tm --test fork_week_grid \
    -- --ignored --exact --nocapture \
    the_frozen_week_grids_are_the_forks_oracle_answer_today \
    the_binary_draws_every_fresh_week_as_the_forks_oracle_draws_it )

echo
echo "############ input set 6: the planner, through the plan mode"
# The frozen lines against the oracle, then the two fresh-draw arms; each reads
# the oracle's banner and refuses a binary without the `plan` mode by name.
( cd "$repo" && TM_ORACLE="$oracle" cargo test --quiet -p tm --test planner_classes \
    -- --ignored --exact --nocapture \
    the_frozen_lines_are_the_forks_oracle_answer_today )
( cd "$repo" && TM_ORACLE="$oracle" cargo test --quiet -p tm --test planner_invariants \
    -- --ignored --exact --nocapture \
    the_kernel_plans_every_fresh_draw_as_the_forks_oracle_plans_it )
( cd "$repo" && TM_ORACLE="$oracle" cargo test --quiet -p tm --test planner_p56_cut \
    -- --ignored --exact --nocapture \
    the_frozen_p56_days_are_the_forks_oracle_answer_today \
    the_kernel_plans_every_fresh_p56_day_as_the_forks_oracle_plans_it )
# The TUI's worlds and the two start worlds (W-41 track H, README gaps 3963 and 3964): every
# frozen TUI day and every frozen start day still fork 4748911's answer.
( cd "$repo" && TM_ORACLE="$oracle" cargo test --quiet -p tm --test tui_kernel_answers \
    -- --ignored --exact --nocapture \
    the_frozen_tui_days_are_the_forks_oracle_answer_today )
( cd "$repo" && TM_ORACLE="$oracle" cargo test --quiet -p tm --test planner_w41_starts \
    -- --ignored --exact --nocapture \
    the_frozen_start_days_are_the_forks_oracle_answer_today )

echo
echo "############ input set 7: every other arm that asks the oracle, read off the sources"
# Sets 3-6 are lists, and the W-46 audit found them short of the class (README gap 4896):
# track C moved eleven test targets' comparands to `tm-oracle capacity` and `tm-oracle plan`
# (`kernel_lookahead_parity`, the `priority_*` files, the `tui_queue_*` binaries, tm-core's
# `priority_edf` and `capacity_slots`, `planner_w40_runs`, ...), each asking live under
# TM_ORACLE, and no set ran them.  So the whole workspace runs here with TM_ORACLE set — every
# arm that is not `#[ignore]`d asks the oracle live — and then every `#[ignore]`d arm the
# sets above do not name, as `arms.py` reads them off the test sources (no list: a new arm is
# run by being written).  Blesses do not run (AGENTS §7.2).
( cd "$repo" && TM_ORACLE="$oracle" cargo test --quiet --workspace --no-fail-fast )
self="$ffi/examples/oracle/run-oracle.sh"
python3 "$ffi/examples/oracle/arms.py" | while read -r package target name; do
  if grep -q "^    ${name}\( \|$\)" "$self"; then
    continue  # run above, by its set
  fi
  echo "-- ${package} ${target} ${name}"
  ( cd "$repo" && TM_ORACLE="$oracle" cargo test --quiet -p "$package" --test "$target" \
      -- --ignored --exact --nocapture "$name" ) || echo "FAILED: ${package} ${target} ${name}"
done
