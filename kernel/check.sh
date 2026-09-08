#!/usr/bin/env bash
# Stage-one acceptance.  Everything the README claims is checked here.
set -uo pipefail
cd "$(dirname "$0")"
LEAN=~/.elan/bin/lean
LAKE=~/.elan/bin/lake
fail=0
say() { printf '%-46s %s\n' "$1" "$2"; }

# 1. The kernel builds, including the linkable archive.
( cd TmKernel && "$LAKE" build TmKernel:static >/dev/null 2>&1 ) \
  && say "lake build TmKernel:static" "ok" || { say "lake build TmKernel:static" "FAILED"; fail=1; }

# 2. Totality and boundary discipline.  A Lean panic returns Inhabited.default
#    with exit code 0 -- a silent wrong answer -- so the kernel must be total.
if python3 totality.py TmKernel/TmKernel; then
  say "totality check" "ok"
else
  say "totality check" "FAILED"; fail=1
fi

# 3. The axiom audit: no theorem may depend on sorryAx.
out=$( cd TmKernel && LEAN_PATH=.lake/build/lib/lean "$LEAN" Check.lean 2>&1 )
n=$( printf '%s' "$out" | grep -c 'axioms' )
if printf '%s' "$out" | grep -q sorryAx; then
  say "axiom audit ($n theorems)" "FAILED (sorryAx)"; fail=1
else
  say "axiom audit ($n theorems)" "ok"
fi

# 4. The negative test MUST fail to compile.  It is the only test that checks
#    the type system is still doing its job.
if ( cd TmKernel && LEAN_PATH=.lake/build/lib/lean "$LEAN" Negative.lean >/dev/null 2>&1 ); then
  say "Negative.lean compiles (must not)" "FAILED"; fail=1
else
  say "Negative.lean rejected" "ok"
fi

# 5. Rust calls the kernel and gets the right answers.
( cd tm-kernel-ffi && cargo test --quiet >/dev/null 2>&1 ) \
  && say "cargo test (Rust -> C shim -> Lean)" "ok" || { say "cargo test" "FAILED"; fail=1; }

exit $fail
