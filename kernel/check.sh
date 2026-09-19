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
#    Both directories: the library, and the package root, which holds Check.lean,
#    Negative.lean and Goals.lean.  Goals.lean is the one exemption and
#    totality.py names it explicitly; see the comment there.
if python3 totality.py TmKernel/TmKernel TmKernel; then
  say "totality check" "ok"
else
  say "totality check" "FAILED"; fail=1
fi

# 3. The axiom audit: no theorem may depend on sorryAx.
#
#    An ERROR in Check.lean is also a failure, and used not to be.  A
#    `#print axioms` naming a constant that has been renamed elaborates to
#    `unknown constant`, prints no `axioms` line, and this check still said ok --
#    the theorem silently stopped being audited and only the count moved.  Stage
#    6 W-13 hit exactly that (three W4 twin rows renamed by D24's seam), so the
#    check now fails on any error Lean reports for this file.
#
#    And the OTHER direction, which this check could not see until W-13's repair:
#    a theorem DECLARED in a module and never given an audit line.  The count
#    alone cannot show it -- step L9 added 35 declarations and 26 audit lines,
#    both numbers rose, and the check said ok at 3984 while nine theorems went
#    unaudited (gap 260: the audit had a count, not a roster).  So the check now
#    runs AGENTS 6.3's own reconciliation: the multiset of declared short names
#    against the multiset of audited last segments, `comm -23`, which must be
#    EMPTY.  It is one-directional on purpose -- `Tm.WfPlan` is a `def` that is
#    deliberately audited (6.3), and auditing more than the theorems is not a
#    defect.  A `sort -u` count cannot replace this: 23 short names are declared
#    in more than one namespace.
out=$( cd TmKernel && LEAN_PATH=.lake/build/lib/lean "$LEAN" Check.lean 2>&1 )
n=$( printf '%s' "$out" | grep -c 'axioms' )
unaudited=$( cd TmKernel && comm -23 \
  <( grep -hoE '^(@\[[^]]*\][[:space:]]*)?theorem [^ (){}:]+' TmKernel/*.lean \
       | sed 's/.*theorem //' | sed 's/.*\.//' | sort ) \
  <( grep '^#print axioms' Check.lean | awk '{print $3}' | sed 's/.*\.//' | sort ) )
if printf '%s' "$out" | grep -q sorryAx; then
  say "axiom audit ($n theorems)" "FAILED (sorryAx)"; fail=1
elif bad=$( printf '%s\n' "$out" | grep -E '^Check\.lean:[0-9]+:[0-9]+: error' | head -3 ); [ -n "$bad" ]; then
  say "axiom audit ($n theorems)" "FAILED (Check.lean errors)"; fail=1
  printf '%s\n' "$bad"
elif [ -n "$unaudited" ]; then
  m=$( printf '%s\n' "$unaudited" | wc -l )
  say "axiom audit ($n theorems)" "FAILED ($m declared, never audited)"; fail=1
  printf '%s\n' "$unaudited" | head -5 | sed 's/^/  no #print axioms for: /'
else
  say "axiom audit ($n theorems)" "ok"
fi

# 4. The negative test MUST fail to compile.  It is the only test that checks
#    the type system is still doing its job.
#
#    Failing to compile is not enough: Lean stops elaborating a file after
#    `maxErrors` (default 100) errors, so once the file held more than 100
#    cheats the last ones were never looked at and the file still "failed".
#    Stage 5 step 3's cheats 86-90 were in that state (README "Stage 5 repair").
#    So the cap is lifted, hitting it anyway is a failure, and every `/- CHEAT`
#    block must carry an error at a line of its own.  A block whose header
#    says `withdrawn` holds no claim and is exempt.
neg=$( cd TmKernel && LEAN_PATH=.lake/build/lib/lean "$LEAN" -DmaxErrors=1000000 Negative.lean 2>&1 )
rc=$?
if [ $rc -eq 0 ]; then
  say "Negative.lean compiles (must not)" "FAILED"; fail=1
elif printf '%s\n' "$neg" | grep -q 'maximum number of errors'; then
  say "Negative.lean rejected" "FAILED (maxErrors reached)"; fail=1
elif silent=$( printf '%s\n' "$neg" | python3 -c '
import re, sys
src = open("TmKernel/Negative.lean").read().split("\n")
starts = [i + 1 for i, l in enumerate(src) if l.startswith("/- CHEAT")]
errs = {int(m.group(1)) for m in re.finditer(r"^Negative\.lean:(\d+):\d+: error", sys.stdin.read(), re.M)}
ends = starts[1:] + [len(src) + 1]
bad = [src[s - 1][3:14].strip() for s, e in zip(starts, ends)
       if "withdrawn" not in src[s - 1] and not any(s <= x < e for x in errs)]
print(", ".join(bad)); sys.exit(1 if bad else 0)
' ); then
  say "Negative.lean rejected" "ok"
else
  say "Negative.lean rejected" "FAILED (no error in: $silent)"; fail=1
fi

# 5. Rust calls the kernel and gets the right answers.
#
#    BOTH test binaries since the owner's D36 (README gap 686).  This check ran
#    `--test kernel` only, and the root Cargo.toml's `members` excludes
#    tm-kernel-ffi, so `cargo test --workspace` did not run the crate either:
#    ALL SEVEN tests of tests/stack.rs were run by nothing automatic.  Not only
#    T17, the D30(Q8) replan instrument gap 600 depends on -- also the four
#    2 MiB-thread stack probes (T0 (a), the log op, T0 (c)) and the two
#    3,660-day lookahead rows.  They ran and passed; that was a procedure, not
#    a gate, and a regression in any of them waited on somebody remembering.
#
#    THE COST IS DECLARED, NOT HIDDEN.  stack.rs sends megabyte requests and
#    takes ~2.2 s against this script's ~3.8 s built-tree wall -- +59%, against
#    design 14.0 item 4's 10%-per-step rule.  D36 spends the rule on this, once,
#    deliberately: the measured before/after is in README "Stage 6 W-18, track
#    A".  Do not read that +59% as a licence for the next step.
#
#    The count is SAID, the way checks 3, 6 and 7 say theirs, so a test that
#    stops running is visible instead of silent: `--test kernel --test stack`
#    is 86 + 7 = 93 today, and an #[ignore] added later moves the number without
#    changing the verdict.  A binary that vanished would fail cargo outright.
out=$( cd tm-kernel-ffi && cargo test --quiet --test kernel --test stack 2>&1 )
rc=$?
n=$( printf '%s\n' "$out" | awk '/^test result:/ { p += $4; i += $8 }
                                 END { printf "%d tests%s", p, (i ? ", " i " ignored" : "") }' )
if [ $rc -eq 0 ]; then
  say "cargo test (Rust -> C shim -> Lean)" "ok  (${n:-no count reported})"
else
  say "cargo test (Rust -> C shim -> Lean)" "FAILED"; fail=1
  printf '%s\n' "$out" | grep -E '^(test |error|thread |---- )' | head -20
fi

# 6. Stage two's acceptance evidence: every Markdown file of the fixture corpus
#    goes through the String -> String boundary with NO COMMANDS and comes back
#    byte-identical -- inside its plan's WHOLE-TREE load, the only request the
#    harness makes since the owner's D6 (a parent is read off its line, so a week
#    file naming month outcomes cannot load alone; README "Stage 4 final", step
#    3).  A file of a refused plan scores `reject`.  This is the only check that covers the split of bytes into
#    lines and back, which happens outside the kernel (README gap 6), and the
#    JSON escaping on both sides of the FFI.
#
#    Two assertions, and they are different in kind.  `no_file_is_silently_
#    rewritten` is absolute: a document the kernel ACCEPTS and hands back with
#    different bytes is data loss and there is no baseline for it.
#    `corpus_round_trip` is a ratchet against corpus/round-trip.expected: a file
#    recorded as round-tripping that stops doing so fails; a file that starts
#    doing so does not, because the grammar is still being extended.  Rebless
#    with `TM_CORPUS_BLESS=1 cargo test --test corpus`.
out=$( cd tm-kernel-ffi && cargo test --quiet --test corpus -- --nocapture 2>&1 )
rc=$?
score=$( printf '%s' "$out" | grep -m1 '^CORPUS:' | sed 's/^CORPUS: //' )
if [ $rc -eq 0 ]; then
  say "corpus round trip" "ok  (${score:-no score reported})"
else
  say "corpus round trip" "FAILED"; fail=1
  printf '%s\n' "$out" | tail -40
fi

# 7. The outstanding goals of stages 3-6 elaborate.  TmKernel/Goals.lean states
#    every remaining obligation as a theorem with a `sorry` proof: a statement
#    that typechecks is guaranteed to be well-formed and to name real
#    definitions, so a goal nobody can state is visible now rather than in
#    stage 6.  `sorry` warnings are the point here; ERRORS are not, and that is
#    what this checks.
#
#    The count is a BURN-DOWN, not a score.  A stage that discharges a goal
#    moves the theorem into its real module and deletes it from Goals.lean, and
#    the number drops.  It rises only when a new debt is admitted.
#
#    Nothing imports Goals.lean, so its `sorry`s cannot reach a proved theorem;
#    check 3 above is what enforces that -- a sorryAx there means it leaked.
out=$( cd TmKernel && LEAN_PATH=.lake/build/lib/lean "$LEAN" Goals.lean 2>&1 )
rc=$?
goals=$( grep -c '^theorem ' TmKernel/Goals.lean )
# The stage mix is MEASURED, not spelled.  This line used to print a literal
# "stages 3-6" beside a counted $goals, and by W-11 all thirteen outstanding
# goals were stage 6's -- a number quoted from a stale measurement, which is
# AGENTS 9.2's own disguised-gap list.  Each goal belongs to the `# STAGE n`
# header above it; a goal above every header is counted and SAID, never
# silently attributed.
stages=$( awk '
  /^# STAGE/ { s = ""; for (i = 1; i <= NF; i++) if ($i ~ /^[0-9]+$/) { s = $i; break }; next }
  /^theorem / { if (s == "") loose++; else { seen[s] = 1; n++ } }
  END {
    m = 0; for (k in seen) out[m++] = k + 0
    for (i = 0; i < m; i++) for (j = i + 1; j < m; j++) if (out[j] < out[i]) { t = out[i]; out[i] = out[j]; out[j] = t }
    if (m == 0) line = "no stage header"
    else if (m == 1) line = "all stage " out[0]
    else { line = "stages " out[0]; for (i = 1; i < m; i++) line = line ", " out[i] }
    if (loose) line = line ", " loose " above every header"
    print line
  }' TmKernel/Goals.lean )
if [ $rc -eq 0 ] && ! printf '%s\n' "$out" | grep -q 'error'; then
  say "stage goals" "ok  ($goals outstanding, $stages)"
else
  say "stage goals" "FAILED"; fail=1
  printf '%s\n' "$out" | grep -v 'declaration uses' | head -40
fi

# 8. The prose resolves.  The owner's D39 (README gap 779).
#
#    FIVE CONSECUTIVE RUNS shipped a stale prose citation -- a doc comment or a
#    README line naming a theorem that had been deleted or renamed -- and every
#    one was found by hand by an independent auditor, because no check above
#    reads a sentence.  Check 3 reads `#print axioms` lines and says so in its
#    own comment; check 4 reads `/- CHEAT` headers.  Nothing read the prose, so
#    the single largest recurring defect class in this campaign's ledger was
#    invisible to the gate by construction.
#
#    So: every backticked snake_case identifier in TmKernel/**.lean AND in
#    README.md is resolved against five DECLARATION sets -- Lean declarations,
#    fields and constructors; Lean string literals (a wire key is declared by
#    the literal that spells it); Rust declarations and fields; Rust string
#    literals; and file stems (`cargo test --test cli_latency` names a file).
#    None of the five is prose, so one stale sentence cannot launder another.
#    citations.py's header is the specification and names its own blind spots.
#
#    THE ALLOW-LIST IS THE WORK, and it is exact names, never patterns: a regex
#    that silenced a class is how this check would get quietly useless, because
#    the next stale citation would land inside the silenced class.  Its four
#    sections say which exemptions were adjudicated and which were merely
#    grandfathered, so a reader can tell an intention from an oversight.
#
#    It found four LIVE stale citations on its first run, in files W-19 did not
#    own; they are carried in the allow-list's section 2 declared as defects
#    (README gap 832), not laundered as exemptions.  Four more it found in files
#    W-19 did own were repaired in the commit before this one.
#
#    The cost is declared, not hidden: 0.21-0.23 s against a 6.7-8.8 s
#    built-tree wall, about 3%.  Gap 703's measurement is re-taken with it in
#    README "Stage 6 W-19, track A".
out=$( python3 citations.py 2>&1 )
if [ $? -eq 0 ]; then
  say "prose citations" "ok  (${out:-no count reported})"
else
  say "prose citations" "FAILED"; fail=1
  printf '%s\n' "$out" | head -20
fi

exit $fail
