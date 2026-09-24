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
#
#    THIS CHECK DID NOT CATCH ITS OWN CLASS UNTIL W-27, and both halves of the
#    hole were in AGENTS R4's own "checked by" column, in plain sight.
#
#    The FIRST half was a NAME LIST.  R4 bans `!`-ACCESSORS and gives `.get!`
#    and `xs[i]!` as EXAMPLES; `totality.py`'s `BANNED` held exactly those two
#    examples, so every other member of the class passed.  DRIVEN in a
#    `git archive HEAD` clone: `.head!`, `.getLast!`, `.back!`, `.tail!`,
#    `.set!` and `.toNat!`, each planted alone in `Emit.lean`, each ELABORATING
#    against the pinned toolchain, gave rc=0.  It is a class now -- a `!` that
#    ends a name -- and the two examples are caught by it rather than beside it.
#
#    The SECOND half was DECLARED, not hidden, which is why it lasted longer:
#    R4's row said `unsafe`, `opaque` and `@[implemented_by]` were "audit
#    items", and the audit appears nowhere in this script.  It was never
#    performed.  All three are mechanised now and R4's row says `totality.py`
#    for the whole rule.  Nine plants in all, every one rc=0 before and named
#    after; three false-positive controls -- `'!'`, `s!"..."` and `a != b`, 58
#    live lines between them -- stay green, which is what makes the class rule
#    a rule and not a wider net.
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
#
#    AND THE THIRD PLACE THE ENUMERATION WAS WRONG WAS THE DECLARATION SHAPE
#    (the W-27 repair step).  The walk was right and the root was right, and the
#    grep still asked for `theorem` at COLUMN ZERO with at most ONE attribute in
#    front of it, so `private theorem`, `protected theorem`, `nonrec theorem`, a
#    second attribute block and any theorem INDENTED inside a `section` were all
#    outside the roster -- declared, compiled, cited, and never required to
#    carry a `#print axioms` line.  This was live, not hypothetical: FOUR
#    private theorems (`Arith.cancelR`, `Look.scaled_le`, `Look.convex_between`,
#    `Look.dayLeft_scale`) and one indented one
#    (`Planner.plan_reserves_one_block_at_a_time`, which had an audit line only
#    because somebody wrote one by hand) were unaudited while this check said
#    ok.  DRIVEN in a scratch copy: a probe theorem at column zero was named, the
#    identical theorem indented inside `section .. end` left `unaudited: []`.
#    The four are no longer `private` -- `#print axioms` cannot name a private
#    constant from another file, so the choice was to expose them or to exempt
#    them, and exempting is how a roster becomes a list again.
#
#    AND THE ROSTER IS NO LONGER A GREP, because widening the grep is wrong in
#    the OTHER direction: `Planner.lean` 6333 writes an indented `theorem
#    plan_reserves_one_block_at_a_time ..` inside a ```lean fence inside a
#    module DOCSTRING, quoting the §8.3 goal it goes on to refute.  Column zero
#    missed that by luck; any indented grep demands an audit line for a theorem
#    that does not exist.  So `leanfiles.py --theorems` comment-strips first,
#    with the same scanner `totality.py`'s ban uses -- one walk, one stripper,
#    one roster, which is the shape the last three repairs of this class each
#    reached for one layer at a time.
#
#    AND W-27'S FIX WAS A LONGER LIST OF PREFIXES, which is the FIFTH place this
#    enumeration was wrong and the W-28 repair step.  The pattern was anchored at
#    the LINE HEAD -- attributes, then `private|protected|nonrec`, then
#    indentation, each a spelling somebody thought of -- so a `theorem` that does
#    not START its line was outside the roster.  Lean's `in` combinators put one
#    there, and this library writes three of them (`set_option maxRecDepth 20000
#    in` twice in EmitWire.lean, `set_option linter.unusedSimpArgs false in` in
#    Json.lean), each on its own line TODAY and each one newline from being
#    invisible.  DRIVEN in a `git archive HEAD` clone with a warm .lake:
#    `set_option maxRecDepth 400 in theorem .. := trivial` and `open Nat in
#    theorem .. := trivial` appended to the library ROOT module both ELABORATE
#    (lake build rc=0) and this check said `ok (5104 theorems)` with both
#    unaudited; the same two theorems written on TWO lines were named at once,
#    and with `leanfiles.py`'s W-28 pattern the one-line pair is named too.
#    The roster is now the KEYWORD TOKEN -- `theorem` is reserved in Lean 4, so
#    in comment- and string-stripped source every occurrence of it declares one,
#    wherever on the line it falls.  Nothing has to be added for a fourth
#    attribute block, a modifier a later toolchain adds, or an `in` combinator
#    nobody has written yet.  Measured: the two patterns agree EXACTLY on this
#    library, 5,102 names each, and `leanfiles.py` states what the token cannot
#    see.
out=$( cd TmKernel && LEAN_PATH=.lake/build/lib/lean "$LEAN" Check.lean 2>&1 )
n=$( printf '%s' "$out" | grep -c 'axioms' )
# **RECONCILED BY THE FULL NAME** (W-29 repair step, README gap 2008).  Both
# sides used to be put through `sed 's/.*\.//'`, which made this a multiset over
# SHORT names: it saw a name that had been LOST and could NOT see one that had
# been SWAPPED for another namespace's same-short-name theorem.  DRIVEN before
# the repair: a second copy of `Tm.EmitWire.the_refusals_spell_themselves`
# standing in for `Tm.PlanWire.the_refusals_spell_themselves` left this check
# saying `ok` with the PlanWire theorem audited zero times.  `leanfiles.py
# --theorems` now prints the name `lean` itself prints, so the two sides are
# compared on the key the audit is actually about.
unaudited=$( comm -23 \
  <( python3 leanfiles.py --theorems TmKernel | sort ) \
  <( grep '^#print axioms' TmKernel/Check.lean | awk '{print $3}' | sort ) )
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
#
#    AND UNTIL W-27 THIS CHECK COULD NOT TELL A DISCHARGED GOAL FROM A DELETED
#    ONE.  "The number drops" was a count and nothing else: `sed -i /theorem
#    plan_tail_drop/d` lowers the burn-down, keeps this check green, and AGENTS
#    3.2's discipline -- prove it in a real module, append `#print axioms
#    Tm.<name>` to Check.lean, THEN delete from Goals.lean -- was enforced by
#    nobody at all.  So the deletion is reconciled against git, the way check 8
#    reconciles its residue: every goal name in HEAD's Goals.lean that this
#    tree no longer states must be NAMED IN Check.lean.
#
#    The comparison is against HEAD and not against a campaign base on purpose.
#    A goal is often discharged under a DIFFERENT name -- restated over the
#    real definitions, or refuted with a witness -- and 14 of the 42 goals
#    discharged since `d61fece` are in that class, so a fixed base would make
#    this red for work that was done correctly years of steps ago.  Against
#    HEAD it is exactly "did THIS step delete a goal", which is the moment the
#    discipline applies, and acceptance runs before every commit.  The escape
#    The escape for a restatement is deliberate: the old name has to appear on a
#    `#print axioms` LINE of Check.lean, which is where a refutation names it
#    (`plan_tail_drop` -> `PlannerWit.plan_tail_drop_as_stage_6_wrote_it_is_
#    refuted_by_the_run_it_does_not_pin`).  PROSE does not count -- the first
#    cut of this rule grepped the whole file and a deletion of any goal two
#    comments mention would have gone green.
#
#    WHAT IT CANNOT SEE, measured here rather than guessed: 5 of the 9 goals
#    outstanding today (`plan_does_not_overbook`, `plan_is_monotone_in_rank`,
#    `plan_puts_hot_before_the_queue`, `plan_tail_drop`,
#    `plan_is_stable_across_a_replan`) ALREADY have an audit line whose name
#    contains theirs -- a partial restatement or a refutation of the form
#    stage 6 wrote -- so deleting one of those five outright still passes.  The
#    other four are caught.  Closing the remaining half needs the burn-down to
#    record, goal by goal, WHICH theorem discharged it; this check has a roster
#    and not a ledger, and that is README gap 1770.
out=$( cd TmKernel && LEAN_PATH=.lake/build/lib/lean "$LEAN" Goals.lean 2>&1 )
rc=$?
goals=$( grep -c '^theorem ' TmKernel/Goals.lean )
gone=""
if git rev-parse --verify -q HEAD >/dev/null; then
  for name in $( comm -23 \
      <( git show HEAD:kernel/TmKernel/Goals.lean 2>/dev/null \
           | grep -oE '^theorem [^ (){}:]+' | sed 's/^theorem //' | sort -u ) \
      <( grep -oE '^theorem [^ (){}:]+' TmKernel/Goals.lean | sed 's/^theorem //' | sort -u ) ); do
    grep '^#print axioms' TmKernel/Check.lean | grep -q "$name" || gone="$gone $name"
  done
fi
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
if [ -n "$gone" ]; then
  say "stage goals ($goals outstanding)" "FAILED (goal deleted, never audited)"; fail=1
  for name in $gone; do echo "  gone from Goals.lean and not named in Check.lean: $name"; done
elif [ $rc -eq 0 ] && ! printf '%s\n' "$out" | grep -q 'error'; then
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
#    THE FILE POPULATION IS INVERTED SINCE W-27 (README gap 1525).  The list
#    below is the history of what this check grew to read, one hole at a time:
#    the Lean recursion (W-21), the prune list and check 3's roster (W-22), the
#    library ROOT module (W-23), `tm/examples` (W-24), `kernel/parity.txt`
#    (W-25).  Every one of those is a file that had to be ADDED to a list to be
#    covered, which is why each was found only after it had gone wrong.  The
#    enumeration is now `git ls-files` (plus `--others`), `EXCLUDED` is the only
#    list, and the residue must be EMPTY -- so the NEXT one fails this check
#    instead of being silent.  It cost one adjudication and brought in the
#    repository ROOT README.md, `tm/DORMANT.md`, the FFI shim's C, six manifests
#    and two shell scripts.  And `::`-SPELLED SPANS ARE SWEPT, which is gap 989
#    closed and ten live stale citations found; `citations.py`'s header has the
#    numbers and the blind spot that is left.
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
#    W-28 GAVE THE OWNER TEST BOTH SEPARATORS (README gap 933).  W-27 turned the
#    `::` spans on and checked that a path's OWNER exists; the test was written
#    `"::" in name`, which is a rule about a SPELLING and not about a path, so
#    the same hole stayed open on `.` -- 9,127 citations over 1,983 dotted names
#    with a capitalised head and 824 more over 192 with a lowercase one, every
#    one of them resolved on its LAST segment alone.  It was at its worst on
#    FILENAMES: `rs`, `md`, `lean`, `snap`, `a`, `toml` and `sh` are all declared
#    names of this repository, so every filename citation in the tree resolved on
#    its EXTENSION.  DRIVEN in a git-initialised clone, one line in
#    `mutations.txt`: check 8 at W-27 NAMED the `::`-spelled stale path and was
#    SILENT on the dotted one beside it.  It costs ten adjudications, EIGHT of
#    them files that do not exist, and one of those eight is a live find -- the
#    README's test arithmetic still counts a 292-line file deleted at 2b26be3.
#    Two sets were widened with it, because an owner is not a leaf: source 5's
#    file stems are now `tracked()`, the repository's own account of its files
#    (it was a walk of THREE DIRECTORY NAMES and the repository ROOT was not on
#    it), and `core_namespaces` reads the pinned toolchain's `namespace` lines
#    OWNER-ONLY, so `Classical.choice` resolves through a real owner.
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
#
#    AND A KILLED RUN IS A FINDING HERE, NOT A SILENT REPAIR (README gap 1788,
#    the W-28 repair step).  `mutate.py` writes the original bytes to
#    `.mutate-in-flight` BEFORE it mutates and puts them back in a `finally`,
#    and `restore_in_flight` puts back whatever it finds AT THE START OF THE
#    NEXT RUN.  That left a window nothing watched: between a killed run and the
#    next `mutate.py`, the tree holds a CONSTANT-FOLDED library file that looks
#    like a commit, and every other check here would pass over it.  DRIVEN by an
#    independent auditor at W-28, in a clone: a `--gate` run killed mid-build
#    left `Emit.lean`'s probe definition with the body `0`.  So the sidecar is
#    tested BEFORE the gate runs and its presence FAILS -- `mutate.py` restores
#    it, and a gate that quietly repaired the tree and then reported ok is the
#    shape this campaign has already paid for.  `mutate.py` also handles SIGINT,
#    SIGTERM and SIGHUP now, so only a SIGKILL or a power cut reaches this.
if [ -e .mutate-in-flight ]; then
  say "new definitions mutated" "FAILED"; fail=1
  echo "  a killed mutate.py left .mutate-in-flight: the library holds a"
  echo "  constant-folded definition.  Run \`python3 mutate.py --gate\` to"
  echo "  restore it, then re-run this script."
else
out=$( python3 mutate.py --gate 2>&1 )
if [ $? -eq 0 ]; then
  say "new definitions mutated" "ok  (${out:-no count reported})"
else
  say "new definitions mutated" "FAILED"; fail=1
  printf '%s\n' "$out" | head -20
fi
fi

# 10. The PARITY register has one home, and no number is issued twice.
#
#     A parity entry is a recorded divergence from the fork point 4748911
#     (owner D21/D22), and the list is stage 5's own acceptance artifact:
#     "every disagreement must be on the list with the decision behind it".
#     It had no single home and no check, and it cost a DUPLICATE TWICE --
#     P32 (README gap 226) and P38 (README gap 1417), five months apart, for
#     the same reason both times: there was no way to read the next free
#     number except off whichever sentence a step happened to find.
#
#     AGENTS 6.5 item 7 gave the MERGE a command after the second one, and
#     said in the same breath why it could not be a gate: a `P<n>` here is
#     also a stage-6 STEP name (P0-P8, and track P), so no regex over `P<n>`
#     tells an issuance from a reference.  That argument is right and it is
#     an argument for an INDEX, not for nothing.  `parity.txt` is the index --
#     one row per number naming the file and LINE where the entry lives --
#     and `parity.py` re-resolves every anchor with no build, the way
#     mutate.py's `stale_sites` re-resolves a pin site.
#
#     WHAT THE COMMAND IN 6.5 COULD NOT SEE, measured before this existed:
#     it required the row to be BOLD and the first twelve are not, so 12 of
#     the 39 numbers in use were invisible to the reconciliation written to
#     find them; it counted the P38 issuance QUOTED INSIDE BACKTICKS in the
#     repair block that fixed P38, so it reported the duplicate on the
#     repaired tree; and it read README.md alone, while P13, P22, P28, P29
#     and P31 live only in design 17's table and P36 lives only in a comment
#     in Replay.lean.  Gap 1417 concluded 17 numbers were "not locatable
#     mechanically".  All 39 are located and anchored now; what was missing
#     was a list of where to look.
#
#     FIVE PLANTS, in a scratch copy, each reverted: a second canonical
#     issuance line for P38 (caught), an unregistered one for `P41` (caught),
#     two index rows for P20 (caught), P20 deleted from the index (caught by
#     the CONTIGUITY rule, which is what stops an index going quietly short),
#     and an anchor moved by one line (caught).  A sixth -- the same issuance
#     line QUOTED in backticks -- stays green, which is the false positive
#     6.5's command had.  A SEVENTH WENT GREEN and is why the row half of the
#     check exists: a bold register row for `P41` appended with no issuance line
#     and no index row passed until it was added.
#
#     SIX MORE WENT GREEN AND WERE REPAIRED AT THE W-25 REPAIR STEP, all six
#     driven in a scratch copy and all six now rc=1.  They are recorded in
#     `parity.py`'s own docstring at length; in one line each:
#
#       * the file set was a NAME LIST of three (README gap 1470, and filed
#         narrower than the hole: the canonical ISSUANCE line went green in a
#         fourth file too, not only a row).  It is a property-based walk of
#         every file in the repository now -- and a THREE-SUFFIX draft of that
#         repair was itself a name list, with plants in design/stage6/notes.txt,
#         notes.org, mutations.txt and this file walking through it;
#       * the THIRD IDIOM was declared and not swept: `parity entry P40` left
#         the gate green and still printing "next free P40";
#       * every anchor was COLUMN ZERO, so an indented row, a row with no
#         spaces round its pipes, and an indented issuance all passed -- and an
#         indented numbered list is this ledger's own gap-block shape;
#       * P0 was read as a parity number, which is what made §14.2's step table
#         need an exclusion at all;
#       * a declared hole ABOVE the top row was left out of "next free", so the
#         gate would have handed out a number the index retires.
#
#     WHAT STILL GOES GREEN, recorded and not claimed away: a register ROW in
#     one of the five files carrying a `not-row` line (their draft numberings
#     mean different things), and an issuance quoted inside backticks.  A
#     backtick span that WRAPS A LINE is the false positive in the other
#     direction -- inline code cannot cross a newline, so half a quoted
#     issuance reads as a citation -- which is why this comment names the
#     idioms in prose instead of quoting them.
#
#     THE COST WAS 0.06-0.07 s at W-25 track A, reading three files; it is
#     0.29 s here, reading 591.  Measured on its own with `/usr/bin/time
#     python3 parity.py`; it still builds nothing.  §5.11: re-measure, do not
#     quote.
out=$( python3 parity.py 2>&1 )
if [ $? -eq 0 ]; then
  say "parity register" "ok  (${out:-no count reported})"
else
  say "parity register" "FAILED"; fail=1
  printf '%s\n' "$out" | head -20
fi

# 11. TWO NAMES FOR ONE DEFINITION.  AGENTS §5.3 -- two definitions of one
#     concept is the bug -- is the rule this kernel is named after, and until
#     W-30 NOTHING BELOW THE GATE READ IT.  It was swept by hand at several
#     steps, and W-29's audit measured what hand-sweeping is worth: that run
#     reported "seventeen groups, all seventeen accounted for", and FIVE
#     character-identical `def` pairs were in none of them.
#
#     W-29 wrote `twins.py` so the number could be re-measured instead of
#     believed, and left it a SWEEP -- it printed thirty groups, exited 0, and
#     argued that a GATE would need an exemption LIST, which is the shape this
#     campaign keeps finding wrong.  README gap 2017 carried that.  It needs no
#     list: it needs a sharper KEY and two PROPERTIES, and the file's header is
#     the specification.  The key is the SIGNATURE and the BODY WITH ITS STRING
#     LITERALS (W-29's key blanked the strings, which made three emitters that
#     differ only in the wire key they spell one body), and a group under one
#     key survives only if neither of these answers it:
#
#       * the definition is NULLARY -- a named value, and two names for one
#         value are two fixture roles or two bounds, not two concepts;
#       * the compiler EMITS DIFFERENT CODE for the two.  That is the exemption
#         the five `@[csimp]` pairs needed and that nobody had ever checked: a
#         `@[csimp]` lemma rewrites the callees of every definition compiled
#         AFTER it, so `edfFast` -- character-identical to `edf` -- compiles to
#         a call to `edfCapsFast` while `edf` keeps `edfCaps`, and deleting the
#         copy would silently deoptimise the original.  Read out of `lake`'s own
#         `.lake/build/ir`, which is why this check runs after check 1.
#
#     It found ONE group that nothing answers, and it was a live duplicate
#     README gap 1956 had already named and not taken: Tm.isDemotedRecord
#     (Close.lean, the name that is now gone) and `Tm.demotedRecordPlacement`
#     (Plan.lean), D8's rule written twice in two modules.  The Close copy is deleted and its three
#     sites read the Plan definition.
#
#     THE COST IS DECLARED AND MEASURED, NOT QUOTED.  0.75-0.76 s (three runs,
#     this machine) inside a 13.26-15.03 s eleven-check wall (FOUR runs, warm
#     tree, same session; the 15.03 followed a python run and the other three
#     were back to back) -- 5.3-6.1% of the ten-check wall it is added to,
#     inside design 14.0 item 4's 10%-per-step rule.  (A first draft of this comment
#     said "about 12%", computed against the 7.91-8.01 s wall check 9's comment
#     records for an older machine.  That is README gap 871's class -- a
#     checker's prose misquoting the measurement beside it -- and §5.11 says
#     re-measure, do not quote.)
out=$( python3 twins.py 2>&1 )
if [ $? -eq 0 ]; then
  say "no two names for one definition" "ok  ($( printf '%s\n' "$out" | tail -1 ))"
else
  say "no two names for one definition" "FAILED"; fail=1
  printf '%s\n' "$out" | head -20
fi

exit $fail
