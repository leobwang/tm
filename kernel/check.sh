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
#
#    AND THE ROSTER GREP WAS THE FOURTH ENUMERATION, repaired at the W-22 repair
#    step.  W-21 made `totality.py`, `citations.py` and `mutate.py` recursive and
#    left THIS one at `TmKernel/*.lean`, because none of the three named it: a
#    theorem in a SUBDIRECTORY was never required to have a `#print axioms` line,
#    which is exactly the class the paragraph above says this check exists to
#    catch.  DRIVEN before the repair, in a scratch copy: the same theorem gave
#    `unaudited` EMPTY at `TmKernel/TmKernel/Sub/Probe.lean` and named it at
#    `TmKernel/Probe2.lean`.  The walk is now `leanfiles.lean_files`, the one
#    enumeration all four checkers share.
#
#    AND SHARING THE WALK WAS NOT ENOUGH: TWO OF THE FOUR CALLED IT ON THE
#    MODULE DIRECTORY AND NOT ON THE LIBRARY (README gap 1314, the W-23 repair
#    step).  A Lake library is `TmKernel/TmKernel/**.lean` PLUS the root module
#    `TmKernel/TmKernel.lean` beside it; this roster and mutate.py's asked for
#    the directory, so a theorem in the ROOT module was never required to carry
#    a `#print axioms` line and a def there was never constant-folded, while
#    lake compiled both.  DRIVEN with these very lines: the probe theorem in
#    TmKernel/TmKernel.lean left `unaudited: []` and the same theorem in
#    Emit.lean named itself.  `leanfiles.py --library TmKernel` names the root,
#    once, so a fifth disagreement needs someone to write a second walk OR a
#    second root.
out=$( cd TmKernel && LEAN_PATH=.lake/build/lib/lean "$LEAN" Check.lean 2>&1 )
n=$( printf '%s' "$out" | grep -c 'axioms' )
unaudited=$( comm -23 \
  <( python3 leanfiles.py --library TmKernel \
       | xargs -r grep -hoE '^(@\[[^]]*\][[:space:]]*)?theorem [^ (){}:]+' \
       | sed 's/.*theorem //' | sed 's/.*\.//' | sort ) \
  <( grep '^#print axioms' TmKernel/Check.lean | awk '{print $3}' | sed 's/.*\.//' | sort ) )
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

# 8. The prose resolves.  The owner's D39 (README gap 779), WIDENED by D41 (W-20).
#
#    FIVE CONSECUTIVE RUNS shipped a stale prose citation -- a doc comment or a
#    README line naming a theorem that had been deleted or renamed -- and every
#    one was found by hand by an independent auditor, because no check above
#    reads a sentence.  Check 3 reads `#print axioms` lines and says so in its
#    own comment; check 4 reads `/- CHEAT` headers.  Nothing read the prose, so
#    the single largest recurring defect class in this campaign's ledger was
#    invisible to the gate by construction.
#
#    So: every backticked identifier in TmKernel/**.lean -- RECURSIVELY since
#    the W-21 repair step, which is where this line stopped overstating the
#    sweep: three checkers enumerated the library one level deep while this
#    sentence claimed a recursion none of them did, and a module in a
#    SUBDIRECTORY was invisible to checks 2, 8 and 9 at once -- in README.md, in
#    AGENTS.md (D41) and -- since the W-20 repair step -- in this file, in
#    kernel/*.py and in mutations.txt, on one line OR wrapped across two, is
#    resolved against SEVEN DECLARATION sets: Lean
#    declarations, fields, constructors and namespaces; Lean string literals (a
#    wire key is declared by the literal that spells it); Rust declarations,
#    fields and parameters; Rust string literals; file stems (`cargo test --test cli_latency`
#    names a file); the checkers' own Python in kernel/*.py; and the PINNED Lean
#    toolchain's own sources.  citations.py's header is the specification and
#    names its own blind spots.
#
#    "NONE OF THE SEVEN IS PROSE, SO ONE STALE SENTENCE CANNOT LAUNDER ANOTHER"
#    IS WHAT THIS LINE USED TO SAY, AND IT WAS FALSE (README gap 1312).
#    RUST_DECL ran over whole Rust file text with no anchor, and LEAN_DECL
#    allows leading whitespace, so `// The old fn foo is gone.` and an indented
#    `def foo` inside a `/-! ... -/` block each DECLARED foo.  Driven at the
#    W-23 repair step: a citation planted in README.md was caught alone, and
#    laundered green by either of those two comments.  Two names in the tree
#    were resolving that way -- seg_title, deleted at W-23, from a needle STRING
#    in one_renderer.rs, and fit_cell, a plant removed before its commit, from
#    one_padder.rs's prose about it.  citations.py's rust_code() and lean_code()
#    strip comments (and Rust string CONTENTS) before the declaration scan; the
#    two citations lost their backticks.  What is still deliberately prose-free
#    is the STRING LITERAL set: a string that is exactly an identifier declares
#    it, because that is how a wire key is spelled, and `"fn foo"` is not one.
#
#    D41 WIDENED THE SPAN TEST from snake_case to snake_case OR camelCase,
#    because snake_case-only reported green on a live stale emitRefused and
#    hid a name gap 809 declares nonexistent at, as re-measured at W-20, 64
#    sites.  camelCase is a CASE TRANSITION and nothing else: `decide`,
#    `rfl`, `Nat`, `sorry`, `lake`, hypothesis names and commit shas have none,
#    which is why the noise gap 880 measured (812 distinct names) does not
#    arrive with the widening.  D41 also DECLINED `kernel/design/**`: 144
#    unresolved names there are a prospective specification's work to do, not
#    stale citations.
#
#    THE W-21 REPAIR STEP WIDENED IT TWICE MORE, and the second is the bigger
#    one.  A DIGIT in front of the capital counts as the transition, because
#    gap22Parent -- renamed childFoldB3 at stage 4 final step 3 and declared
#    nowhere since -- was backticked at six live sites with this check green.
#    And a QUALIFIED span (two dotted segments, capitalised head) is swept
#    whether or not it has a transition at all: `Arith.ramp`, `Cap.edf`,
#    `Look.bucket` and `Ckpt.wf` have neither, and 4,848 citations / 600
#    distinct dotted spans were unswept.  Driven: renaming the live `def ramp`
#    left eleven `Arith.ramp` citations and this check exited 0 with
#    byte-identical counts; it now names it.  Three adjudications in all.
#
#    A COUNTED ALLOW-LIST CAP IS EXACT, also the W-21 repair step's: FEWER
#    citations than the cap fails too, naming the number to tighten to.  Slack
#    opened by a falling count is a free exemption nobody adjudicated, and it
#    opens without anyone editing the allow-list -- 3 of 348 entries carried 6
#    citations of it when it was found.
#
#    W-24 ADDED THE RUST COMMENTS AS A SWEPT SOURCE, closing README gap 1313
#    item 3 -- the last unswept prose in the repository, and the half of the
#    partition the W-23 repair left open: rust_code() has blanked comments since
#    that repair so prose cannot DECLARE, and rust_prose(), its exact
#    complement, is what makes prose CITED.  Every byte of a .rs file is now
#    read by exactly one of the two.  Source 3 gained function PARAMETERS in the
#    same step, because a doc comment naming its own fn's argument is correct
#    prose and eleven names were exactly that; `let` bindings were measured and
#    DECLINED (+896 short names for two resolutions).  Driven: the same plant --
#    a backticked w24_module_comment_plant in a //! at tm-core/src/emit.rs:1 --
#    leaves the PREVIOUS citations.py's output byte-identical and is named by
#    this one, and so are plants in ///, // and a nested /* */; a plant inside a
#    STRING literal is correctly seen by neither half.  It cost 30 adjudications
#    (not the 162 W-23 predicted from a wider span test) and found SIX live
#    stale citations plus a seventh written while building it.
#
#    THE ALLOW-LIST IS THE WORK, and it is exact names, never patterns: a regex
#    that silenced a class is how this check would get quietly useless, because
#    the next stale citation would land inside the silenced class.  Its nine
#    sections say which exemptions were adjudicated and which were merely
#    grandfathered, so a reader can tell an intention from an oversight.
#
#    It found eight LIVE stale citations on its first run (README gap 832 keeps
#    the four W-19 did not own) and, widened, 51 more that W-20 repaired with
#    the un-backtick convention.  The last 19 -- all of one dead name, left
#    behind two counted allow-list entries because they sat in files track A did
#    not own -- were repaired at the W-20 repair step, and gap 932 is closed:
#    64 of 64.  The line-wrap widening found two more, in the paragraph claiming
#    this check had caught the step's stale citations.
#
#    The cost is declared, not hidden: 0.52 s (three runs, this machine)
#    against a 7.91-8.01 s built-tree wall, 6.5%, of which source 6 is 0.21 s.
#    It was 0.22-0.23 s before D41.  RE-MEASURE; do not quote.
out=$( python3 citations.py 2>&1 )
if [ $? -eq 0 ]; then
  say "prose citations" "ok  (${out:-no count reported})"
else
  say "prose citations" "FAILED"; fail=1
  printf '%s\n' "$out" | head -20
fi

# 9. Every definition a step ADDS is constant-folded.  The owner's D40
#    (README gap 930).
#
#    THREE TIMES this campaign a definition shipped whose body nothing in the
#    package could tell from a constant, and a human found all three:
#    W-17's P4 sort key (halves swapped, 1,342 tests green), W-18's nine
#    candidate facts (invert one, the suite green, `tm plan` visibly re-ranks),
#    and W-19's `Planner.Ranked.gatherable` -- `:= true`, and 168 build targets,
#    every theorem, all nineteen witnesses and check.sh 8/8 still green.  No
#    check above can see it: check 3 reads axiom sets, check 4 reads a file that
#    must fail, check 8 reads sentences.  A definition nothing distinguishes
#    passes all eight.
#
#    So: every `def` and `abbrev` in the library that is NEW OR CHANGED since
#    the baseline commit in `mutations.txt` has its body replaced by a constant
#    of its type -- `true` AND `false` for `Bool`, `True`/`False` for `Prop`,
#    `0`/`1` for `Nat`, `default` otherwise -- one at a time, and the build must
#    FAIL for each.  A build that SUCCEEDS is the defect.  A build that fails
#    with an error INSIDE the mutated declaration is also a failure, not a pass:
#    that is the constant not typechecking, which would otherwise hand out a
#    free PINNED verdict.
#
#    A CONSTANT OF THE TYPE IS NOT ONLY `default`, and the W-21 repair step
#    added the two that exist where `default` does not: a nullary `T.empty`
#    this kernel declares in the SAME FILE, and a structure literal
#    `⟨c1, …, cn⟩` built when EVERY field of the type has a constant.  README
#    gap 1035 said of `PlanReq.deferFold`, `PlanReq.finalAssign` and
#    `dayDiagnostics` -- the whole of what was left of step 6's algorithm --
#    that nothing below the gate said any theorem read them.  Re-audited: all
#    three PINNED, at PlannerWit.lean:3704, Planner.lean:5348 and
#    Planner.lean:5340, and two `PlannerWit` fixtures with them, so the rows
#    pinned by NOTHING fell from 23 of 77 to 18 of 77.  A synthesised constant
#    that does not elaborate is UNAVAILABLE, not INVALID: the guess failed, not
#    the definition, and it is counted on the "pinned by nothing" line.
#
#    ONE EXCEPTION, AND IT IS NAMED, COUNTED AND EXACT.  If that in-declaration
#    error is exactly `failed to synthesize ... Inhabited T`, the type has no
#    constant to fold to and D40's constant DOES NOT EXIST for that definition.
#    The verdict is UNFOLDABLE: the definition is rostered in mutations.txt with
#    `unfoldable` in its constants column and the type in its reason column, the
#    count is printed on every run, and the gate does not fail.  This is check
#    8's allow-list discipline applied to check 9 -- exact names, never a
#    pattern -- and it is NOT a claim that anything reads the definition.
#
#    A SIXTH label, FIXTURE, re-labels an already-exempt row declared in a
#    `WITNESS_MODULES` leaf -- exact paths, the leaf property checked on every
#    run and fatal if it fails.  It subtracts nothing from the audit: a
#    witness-module definition a constant pins stays PINNED.  README gap 1086.
#
#    THE FIRST REAL RUN, at the W-20 land step, was 46 definitions from tracks P
#    and G: 23 PINNED, 23 UNFOLDABLE, **0 SURVIVED**.  The 23 are `Bool` +
#    `Subtype` types (AGENTS 5.1) that deliberately have no default, so the gate
#    and the kernel's own discipline are in tension; README gap 980 puts that to
#    the owner, and reversing it is one line in `mutate.py`.
#
#    A CONSTANT IS NOT THE ONLY DEGENERATE BODY, and W-21 track A added the
#    other one: the IDENTITY ON THE ACCUMULATOR (README gap 985).  When a
#    definition's result type appears among its own argument types, its
#    degenerate body is that argument -- `PlanReq.rePlaceWalk` folded to
#    `fun a0 _ => a0`, `PlanReq.deferWalk` to `fun a0 a1 _ => (a0, a1)`,
#    `placeAt` to `q` -- which is the shape a walk that forgets to walk actually
#    takes, and which EXISTS for an uninhabited type.  It is tried BESIDE the
#    type's own constants, never instead of them.  Measured when it landed:
#    5 of the 23 UNFOLDABLE rows are reached and all five are PINNED, so the
#    exemption fell from 23 of 46 to **18 of 46**; the gate's summary now prints
#    both numbers, because "no constant of this type exists" and "nothing
#    mutates this definition at all" are two different claims and only the
#    second is an exemption.  DRIVEN, the way W-20's own repair was: before the
#    widening, `def w21AccumWalk : Assign -> List Nat -> Assign` with a body
#    nothing in the package distinguishes from the identity was reported
#    UNFOLDABLE and `mutate.py --only` EXITED 0 -- green on an instance of the
#    class check 9 exists to catch.
#
#    SCOPED TO NEW DEFINITIONS because D40 scoped it there: a full sweep of the
#    existing 2,810 library definitions was declined as producing a backlog
#    rather than preventing new instances.  The baseline is the decline, written
#    down.
#
#    THE COST IS THE STEP'S OWN, AND IT IS ~0 AT A SETTLED TREE.  Nothing is
#    new, two git calls say so, and this check is 0.09-0.10 s on this machine --
#    about 1.1% of the wall.  It was 0.05 s with one git call; the second is
#    `git ls-files --others`, which is what makes an UNTRACKED new module
#    visible, and acceptance runs before the commit.  (This comment said 0.03 s
#    and "under half a percent" while `mutate.py`'s own header and the land
#    block's table beside it both said 0.05 -- README gap 871's class, a
#    checker's prose misquoting the measurement printed next to it, for the
#    fourth time this campaign and inside the file the campaign had just added.
#    Repaired at the W-20 repair step; RE-MEASURE, do not quote.)
#    It is ~0 here only because the 46 rows are IN: the
#    W-20 land step paid 69 kernel builds, about 75 minutes, to put them there.  A step that ADDS definitions pays one kernel build
#    per constant, measured in README "Stage 6 W-20, track A" at 53 s
#    (Planner.lean), 54 s (PlannerWit.lean) and 205 s (Boundary.lean); that is
#    the step's cost, not this script's steady state, and it is why the roster
#    is trusted on a matching body sha1 rather than re-run.  `mutate.py
#    --verify` re-runs every row and is what an auditor uses.  The whole script
#    went 7.37-7.48 s at eight checks to 7.83-7.87 s at nine on the machine that
#    measured it -- min to min +6.2%, max to max +5.2%; the "+5.1%" that stood
#    here followed from neither pair.  This machine's quiet wall is 7.91-8.01 s
#    at nine.
out=$( python3 mutate.py --gate 2>&1 )
if [ $? -eq 0 ]; then
  say "new definitions mutated" "ok  (${out:-no count reported})"
else
  say "new definitions mutated" "FAILED"; fail=1
  printf '%s\n' "$out" | head -20
fi

exit $fail
