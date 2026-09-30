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
#
#    RE-DRIVEN BY AN AUDITOR WHO DID NOT WRITE IT (W-32).  `e89a2c0` landed
#    after its auditor had finished, so its class was planted again in a `cp -a`
#    clone with its OWN build tree, three ways, each alone: `#eval show
#    Lean.Elab.Command.CommandElabM Unit from .. addDecl (Declaration.axiomDecl
#    ..)` at column zero (named, "`#eval` stands where a command begins");
#    the same `#eval` INDENTED inside `section W32Critic .. end` (named,
#    "a COMMAND keyword .. at an indented command position"); and `run_cmd`
#    indented inside a section, W-30's own escape (named the same way).  All
#    three rc=1, and a fourth -- `theorem .. := by native_decide` -- is named
#    too, which is what puts check 3's arm below on a plant this one cannot see
#    only by DISABLING this one.  Control: rc=0 before each plant and after each
#    revert.
#
#    AND THE WORD AFTER `in` KEPT THE SHORT CLASS until the W-33 repair (README
#    gap 2561): `open Lean Elab Command in #eval .. addDecl (.axiomDecl ..)` on
#    ONE line passed at rc=0 while check 3 named the axiom.  Driven in a clone
#    with HEAD's and the repaired script over the same plant: rc=0 silent, then
#    rc=1 naming both `#eval`s.  Both position readers share one class now.
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
# **AND THE CHECK NAMED "THE AXIOM AUDIT" NEVER LOOKED AT THE AXIOM SET**
# (W-31 repair step, README gap 2256).  This chain's first arm was `grep -q
# sorryAx`: ONE NAME, where the hard rule is a CLASS -- *no new axiom*.  A
# planted axiom is not `sorryAx`, so `lean` printed `'Tm.w31_one_is_two'
# depends on axioms: [w31Planted]` and the gate read that line and said `ok`.
# DRIVEN in a `cp -a` clone with its own build tree: `lake build
# TmKernel:static` rc=0, this fragment "axiom audit (5290 theorems)  ok", and
# the planted name in `$out` at line 5762.  `grep -rn 'propext|Classical.choice
# |Quot.sound' check.sh *.py` returned only prose -- NOTHING in the tree
# compared the printed set to the allowed one.  The twelfth counted instance of
# a NAME LIST where the rule is a CLASS, inside the gate the rule is named
# after.
#
# SO THE ARM IS A SUBSET TEST, and it is W-27's shape: an axiom joins the three
# Lean ships to be EXEMPT.  `sorryAx` keeps its own arm above because its
# message is the one a reader wants; it would fail here too.
#
# RE-DRIVEN BY AN AUDITOR WHO DID NOT WRITE IT (W-32), and with a plant check 2
# could not have caught on its own reading of the SOURCE: `theorem
# w32_critic_native : (1000 : Nat) < 2000 := by native_decide` appended to
# `SealInStep.lean` in a `cp -a` clone with its own build tree, plus its
# `#print axioms` line.  `lake build TmKernel:static` rc=0, Check.lean reported
# ZERO errors, `grep -c sorryAx` was **0** -- so the arm this one replaced would
# have said `ok` -- and `lean` printed `'w32_critic_native' depends on axioms:
# [w32_critic_native._native.native_decide.ax_1_1]`.  The subset arm named it at
# rc=1: "A NEW AXIOM: w32_critic_native._native.native_decide.ax_1_1, 1 use(s)".
# Reverted and rebuilt, the census is the line this check prints.
#
# AND THE PARSER CARRIES ITS OWN FLOOR.  `lean` WRAPS a long axiom list over
# several lines (16 of them in this library), so a line-at-a-time reader sees
# fewer records than were printed -- and a parser that reads nothing gates
# nothing, which is what the campaign keeps finding.  The record count must
# equal the `axioms`-line count or this fails by name.
axcensus=$( printf '%s\n' "$out" | python3 -c '
import re, sys
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
t = sys.stdin.read()
# The name is GREEDY to its last apostrophe and the list is a character class:
# `Tm.Field.map_map\x27` and 23 more carry a prime, and `[^\x27\n]+` read 5,266
# of 5,290 records on the first drive -- the floor below caught this parser
# before it gated anything, which is what the floor is for.
dep = re.findall(r"(?m)^\x27(.+)\x27 depends on axioms: \[([^]]*)\]", t)
none = re.findall(r"(?m)^\x27(.+)\x27 does not depend on any axioms", t)
printed = sum(1 for line in t.splitlines() if "axioms" in line)
if len(dep) + len(none) != printed:
    print("PARSED %d of %d printed audit lines -- this arm would gate nothing"
          % (len(dep) + len(none), printed))
    raise SystemExit(1)
seen = {}
for name, lst in dep:
    for a in lst.replace("\n", " ").split(","):
        a = a.strip()
        if a:
            seen.setdefault(a, []).append(name)
extra = sorted(set(seen) - ALLOWED)
if extra:
    for a in extra:
        print("A NEW AXIOM: %s, %d use(s), first `%s`" % (a, len(seen[a]), seen[a][0]))
    raise SystemExit(1)
print(", ".join("%s %d" % (a, len(seen.get(a, []))) for a in sorted(ALLOWED)) +
      "; %d of %d depend on none" % (len(none), printed))
' ); arc=$?
if printf '%s' "$out" | grep -q sorryAx; then
  say "axiom audit ($n theorems)" "FAILED (sorryAx)"; fail=1
elif bad=$( printf '%s\n' "$out" | grep -E '^Check\.lean:[0-9]+:[0-9]+: error' | head -3 ); [ -n "$bad" ]; then
  say "axiom audit ($n theorems)" "FAILED (Check.lean errors)"; fail=1
  printf '%s\n' "$bad"
elif [ $arc -ne 0 ]; then
  say "axiom audit ($n theorems)" "FAILED (an axiom outside Lean's three)"; fail=1
  printf '%s\n' "$axcensus" | head -5 | sed 's/^/  /'
elif [ -n "$unaudited" ]; then
  m=$( printf '%s\n' "$unaudited" | wc -l )
  say "axiom audit ($n theorems)" "FAILED ($m declared, never audited)"; fail=1
  printf '%s\n' "$unaudited" | head -5 | sed 's/^/  no #print axioms for: /'
else
  say "axiom audit ($n theorems)" "ok  ($axcensus)"
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
#    outstanding today (plan_does_not_overbook, `plan_is_monotone_in_rank`,
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
    # NOT `grep -q` (W-39 track K, README gap 3551): under `pipefail`, `-q`
    # exits at its first match while the first grep is still writing ~6,000
    # audit lines, which then dies of SIGPIPE, and the pipeline's 141 read as
    # "never audited".  Measured on the W-39 tree: every goal whose name is
    # first matched early in Check.lean reported gone with its audit line
    # standing (`plan_is_monotone_in_rank` rc=141); the one matched in the
    # file's last buffer passed.  A false alarm, never a false pass -- but a
    # gate that fails correct work teaches the next step to route around it.
    # EXACT, NOT A SUBSTRING (the W-39 repair, README gap 3716): a goal leaves this file
    # only as a theorem OF ITS OWN NAME (discharged, or restated under its short name in
    # its real module) or as a REFUTATION of it (AGENTS 3.1 item 3's refute-and-rename:
    # a last segment `<name>_..._is_refuted`).  `grep "$name"` let any longer-named
    # theorem answer for it -- `plan_tail_drop_with_the_active_item_erased` for
    # `plan_tail_drop`, a `<name>_bound` lemma for a goal deleted with no proof.
    grep '^#print axioms' TmKernel/Check.lean | awk '{print $3}' | sed 's/.*\.//' \
      | grep -xE "${name}(_(.*_)?is_refuted)?" >/dev/null || gone="$gone $name"
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
    # At a burn-down of 0 there is no goal to attribute, and "no stage header"
    # was false of a file with four (W-39 track K, README gap 3551).
    if (m == 0) line = (loose ? "no stage header" : "no goal under any stage header")
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
#
#    AND A PIN WAS THE FIRST ERROR, WHICH CANNOT SAY WHAT KIND OF ERROR IT IS
#    (W-34 track A, README gap 2578).  A theorem that breaks under the constant
#    either states something the constant FALSIFIES -- the pin -- or only had a
#    PROOF that unfolded the body, while its statement stays true of the
#    constant and pins nothing: `PlanReq.dayHot_capped` pinned `dayHot := []`
#    that way until the W-33 repair reordered four laws by hand (gap 2567).
#    `mutate.py`'s SECOND PASS first reads the one error that SAYS the
#    statement is false -- Lean's `decide`, the theorem's whole proof, "proved
#    that the proposition .. is false" (`its statement, decided false`) --
#    and otherwise asks whether anything ELSE fails: another declaration in
#    the same build (`also`), one that fails once the first theorem's proof is
#    `sorry` and the package is rebuilt (`then`), or the theorem's own
#    STATEMENT with its proof gone (`its statement`).  A rebuild that SUCCEEDS
#    is ALONE and FATAL, like SURVIVED.  The decided rule was found by the
#    pass's first real run: `PlannerWit.witCandsSwapped`, whose one reader is a
#    `by decide` witness the constant falsifies, came back ALONE without it.  Driven in a clone
#    with its own `.lake`, the W-33 script beside it: a filter with one law
#    whose statement `[]` satisfies was PINNED three times, rc=0, and is ALONE
#    three times, rc=1; with a `decide` witness a module downstream it is
#    PINNED `then` that witness; in the same module, `also`; a width a
#    statement's type reads is `(its statement)`.  A kill mid-pass left the
#    two-file sidecar this check fails on, and the next run restored both.
#    ITS COST IS THE STEP'S, NOT THIS SCRIPT'S: a PINNED constant costs one
#    more build when the first build shows no second failing declaration.
#    Settled, this check does no build either way -- 0.39-0.40 s before, 0.39-
#    0.41 s after, three runs each -- and prints the rows the pass predates.
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

#    THE BUILD THE LATER CHECKS READ IS THE SOURCE'S (W-34 repair, README gap
#    2736).  `mutate.py` builds each constant-folded mutant and restores the
#    SOURCE in a `finally`; it does not rebuild.  So after a pass that built
#    anything, `.lake/build/ir` held the LAST MUTANT's C, and checks 11 and 12
#    read that call graph.  Driven by W-34's reuse critic on a red run: checks
#    11 and 12 failed with "`tm_kernel_call` is not an emitted function" because
#    `PlanWire.c` was missing; had the last mutant SURVIVED, they would have
#    read a mutant's graph and said nothing.  One rebuild here makes every
#    check after this line read what check 1 built.  On a settled tree it is
#    Lake's no-op.
( cd TmKernel && "$LAKE" build TmKernel:static >/dev/null 2>&1 ) \
  || { say "rebuild after check 9" "FAILED"; fail=1; }

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
#       * the definition is NULLARY *and not a function* -- a named value, and
#         two names for one value are two fixture roles or two bounds, not two
#         concepts.  "Nullary" was the SPELLING `sig.startswith(":")` until the
#         W-30 repair, under which `def f : A -> B := fun ..` was a named value;
#         it is now the type and the body (gap 2128);
#       * the compiler EMITS DIFFERENT CODE for the two AND THE EXPORT REACHES
#         ONE OF THEM.  That is the exemption the `@[csimp]` pairs needed, and
#         **only its first half had ever been checked** (gap 2126): this comment
#         said "deleting the copy would silently deoptimise the original" and
#         named `edf` and its twin, and rooted at the export NEITHER is among
#         the 2,092 reachable of 11,949 emitted C functions -- there was no call
#         to deoptimise.  `twins.py` now walks the emitted call graph, the three
#         pairs where the fast twin IS reached keep the exemption, and edfFast
#         and edfGrantsFast were DELETED with their two `rfl` lemmas rather
#         than exempted.  Read out of `lake`'s own `.lake/build/ir`, which is
#         why this check runs after check 1.
#
#     AND THE POPULATION IS EVERY `def`, not every `def` spelled with a `:=`
#     (gap 2127).  `bodies()` dropped the 400 declarations written with match
#     arms -- 13% of the library's 3,044 -- on a silent `continue`, and printed
#     "2644 def bodies" with no residue beside it.  A declaration this key
#     cannot split is now COUNTED and FAILS the check.
#
#     It found ONE group that nothing answers, and it was a live duplicate
#     README gap 1956 had already named and not taken: Tm.isDemotedRecord
#     (Close.lean, the name that is now gone) and `Tm.demotedRecordPlacement`
#     (Plan.lean), D8's rule written twice in two modules.  The Close copy is deleted and its three
#     sites read the Plan definition.
#
#     AND THE KEY IS TWO KEYS SINCE W-33 (track A, README gap 2418).  The exact
#     key above cannot see a GENERALISATION -- a definition that is another's
#     body with a literal turned into a parameter -- and W-32's repair found
#     four in one module (`PlannerWit.pCand`, `pCandDue`, `pCandSmall`,
#     `bCand`) with this check green at 14 groups: a LIST where the rule is a
#     CLASS, the thirteenth counted instance, inside the gate named after §5.3.
#     The SECOND key puts two `def`s in one group when their result types and
#     bodies are identical once every parameter and every literal is a hole
#     (a constructor over holes is a literal; constructors are what the
#     library and `Init/Prelude.lean` DECLARE, read by `leanfiles.constructors`,
#     the one scanner check 8 also reads).  A group that is one exact-key group
#     is the exact key's; every other climbs a ladder of properties -- E3 a
#     fixture value, ALPHA two names for one body (fails unless E2), E5 a
#     wrapper, E4 wire-named -- and what no rung answers must have a SENTENCE
#     in `twins-exempt.txt`: ONE CONCEPT, naming the carrier and an EXIT, or
#     NOT ONE CONCEPT, saying why; dated either way.  W-27's shape.  Measured
#     at `8702132`: 60 generalisation groups beyond the exact ones, 35 fixture
#     values, 2 wrappers, 7 wire-named, 16 adjudged (9 owed, 7 not one), and
#     the ALPHA rung's first catch was `closeTo`/`targetContaining`, one body
#     under two parameter names that E2 had been answering for because the
#     generator's C locals carry the parameter's NAME (repaired: `CVAR`
#     erases it).  DRIVEN in a clone, four plants, each rc=0 before and rc=1
#     named after: a surrogate test with its lower bound made a parameter,
#     `pairScalar` with its base made a parameter, a `WfSeg` fixture with its
#     `SegKind` made a parameter, and `natLt` again under other names.
#     WHAT IT CANNOT SEE is the file's header: a generalisation across a delta
#     step or a structure eta (gap 2417's family is two groups here and one
#     definition), a closed term that is not a literal, a renamed body-local
#     binder.  The cost: 1.57/1.59/1.56 s before against 2.07/2.08 s after,
#     interleaved under the same load (one 3.15 s outlier as the load rose to
#     8), about +0.5 s.  THE W-33 REPAIR (README gaps 2550, 2562, 2563): E4
#     read EVERY nullary constructor as a wire name, so a `SegKind` sibling
#     (`.rest` for `.windDown`) was answered WIRE-NAMED -- driven, and named
#     now, by `WIRE_KEY_TYPES`; the header declares four more blind spots it
#     had not (a one-hole body, a `Fin` literal, a fixture's literal made a
#     parameter, a shared constructor short name); a NEW NOT ONE CONCEPT line
#     FAILS as RATCHET (driven: spanPer plus a dated NOT ONE line was green);
#     and a ONE CONCEPT line that says CARRIED BY `X` is counted carried, after
#     the gate checks every member is headed by `X`.
#
#     W-34 TRACK A CLOSES THE FOUR (README gaps 2577, 2601, 2604, 2605), each by
#     a PROPERTY and each driven in a `git clone --no-hardlinks` with the W-33
#     script beside this one over the same plant -- rc=0 then rc=1, the control
#     rc=0 before and after, the shared tree's porcelain unchanged: a body that
#     is ONE HOLE is keyed by the constructor it applies (a `⟨n, d⟩` plant beside
#     `Arith.util` fails ALPHA); a TACTIC PROOF is a hole (`⟨l % 86400 / 60, h⟩`
#     beside `Emit.clockOfLocal`'s `by omega` is unanswered); a VALUE that
#     re-spells its group's rule at closed arguments FAILS as FIXTURE
#     (a `⟨43200 % 86400 / 60, by omega⟩` fixture); and a field-key
#     constructor is a WIRE NAME only where Lean's own expected-type rule
#     resolves it to `Tm.Field.Key` -- the tuple read the short name `Key`,
#     which is TWO types, and `.floor`/`.cap`/`.est` are `EditVal`'s
#     constructors too, so a `.floor` sibling over a planted type and a
#     `.machine` one over the replay's `Key` were each answered WIRE-NAMED
#     before and are unanswered now.  E5 was made SPELLING-INVARIANT with it: `⟨n, 1⟩` IS
#     `Q.mk n 1`, and the rung answered only the second.  Two precision defects
#     the widening exposed are closed on the way: members were NAMED by their
#     written name, first occurrence winning, so `Tm.Field.setEst` was reported
#     as `Tm.setEst` (six such pairs; positional now, a scanner disagreement
#     fatal); and a structure field sharing a parameter's spelling was holed.
#     Measured at `9551d66` plus this step: 88 generalisation groups (61 before
#     it), 0 UNANSWERED -- every group the widening formed is answered by E3
#     or E5 -- and 2.33-2.34 s against 2.08-2.10 s, three runs each
#     interleaved in one clone at load ~8: +0.24 s, about 1% of the wall.
#
#     THE COST IS DECLARED AND MEASURED, NOT QUOTED, AND IT WENT UP.  It was
#     0.75-0.76 s; the reachability walk reads the whole of `.lake/build/ir`
#     once and cached, and three runs at the W-30 repair measure **1.45, 1.46
#     and 1.50 s** -- about +0.7 s on a 13.26-15.03 s eleven-check wall (FOUR
#     runs, warm tree, same session; the 15.03 followed a python run and the
#     other three were back to back), so ~5% more wall for the half of E2 that
#     had never been checked.  Re-measure it, do not quote it (5.11).
#     The older figure was 5.3-6.1% of the ten-check wall it was added to,
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

# 12. A DEFINITION THE COMPILER EMITS MUST BE REACHED.  The owner's D51, README
#     gap 2130, and the layer every other check in this file is blind to.
#
#     Checks 3, 8, 9 and 11 read the SOURCE or the THEOREM SET.  Reachability is
#     a property of the emitted CALL GRAPH, so none of them could see it, and
#     the auditor who built the first walk put it in one sentence: a definition
#     can be pinned by a theorem (check 9), unique (check 11), audited (check 3)
#     and cited (check 8) and still be called by nothing -- `Tm.remainingMin` is
#     all five.  THREE OF THIS CAMPAIGN'S FINDINGS LIVE THERE AND EVERY ONE WAS
#     FOUND BY HAND: D50's `assignFold` (eight audit runs), gap 501's
#     `Recur.lean` (many runs), and `Tree.lean` -- ten definitions and
#     thirty-seven theorems -- which nobody had found at all.
#
#     THE PROPERTY, NOT A COUNT.  *A definition not used solely within proofs
#     must be reachable from `tm_kernel_call`.*  The antecedent is the
#     COMPILER'S: a `def` it emits no code for is one nothing can call, and a
#     `def` it does emit is code the program runs or carries dead.  The
#     source-side reading of "solely within proofs" was measured and REFUSED
#     (`reach.py`'s header): it exempts 260 definitions, and among them are
#     `Tm.edf` and `Tm.edfGrants` -- §7's EDF grant machine, whose fast twins the
#     W-30 repair deleted as dead (gap 2126) and whose originals nothing has
#     called since.  A rule about who MENTIONS a name is a rule the blind spot
#     is defined by; `Tm.remainingMin` is mentioned nine times inside its own
#     module, exactly as `assignFold` was.
#
#     AND THE ROOT OF THAT PROPERTY WAS ASSUMED UNTIL W-32 (README gap 2229).
#     "Reachable from `tm_kernel_call`" is answerable and it is not the
#     question: `tm_kernel_call` is a DOOR, not a caller.  What comes through it
#     is a REQUEST, whose top-level keys choose which of the kernel's sections
#     runs, and a section nothing sends is a door into a room nobody enters.
#     W-31's track P found the consequence BY HAND, while pricing R3 -- the same
#     way `assignFold`, `Recur.lean` and `Tree.lean` were all found -- and it is
#     the fourth of them: `Planner.dayPlan`, §8.2's whole day planner, is
#     reached from this root and from NO shipped caller, because `grep -rn
#     '"planner"' tm/src` is EMPTY.  So the root is MEASURED now, on both sides,
#     by `sections.py`: the kernel's own top-level sections, walked from the
#     `@[export]` definition by following the request value (so `readTz` on the
#     `tz` object is never mistaken for a reader of the request), and the
#     requests `tm/src` builds, read as the keys at brace depth 1 of every
#     `json!` block and string literal that is request-shaped.  Measured
#     2026-09-25: the kernel dispatches TEN top-level sections and `tm/src`
#     sends EIGHT.  `planner` and `plan` -- W-24's rows -- are sent by
#     `tm/tests/planner_invariants.rs` and `tm/tests/kernel_planner_wire.rs` and
#     by nothing a user can run, and `tm/src`'s three `"plan":` occurrences are
#     all a CANDIDATE's nested field inside `kernel_capacity.rs`'s `plan_json`.
#     **1,467 reachable became 1,178** -- 228 behind `planner`, 53 behind
#     `plan`, 8 behind the two together.
#
#     THE CUT IS AN ARM AND NOT A ROOT, and the difference was measured.
#     Rooting the walk at the section readers loses the plumbing every request
#     runs -- `jparse`, `jemit`, the loader -- and reports it dead, so the root
#     stays `tm_kernel_call` and a dispatcher for an unsent section contributes
#     only the callees of its ABSENT arms: `Tm.PlanWire.runPlanner` gives
#     `Tm.jsonErr` and `Tm.EmitWire.runRows`, and its `.ok (some sec)` arm --
#     `Tm.PlanWire.readPlannerSection`, `Tm.PlanWire.planReqOf`,
#     `Tm.PlanWire.planJson`, `Tm.Planner.dayPlan` -- gives nothing.  The cut is
#     taken where the PROGRAM branches and not where the PROOF does: the first
#     attempt used the right-hand side of the kernel's own absence law, and
#     `runRows_without_a_plan_section_is_runCap` is EXTENSIONAL -- it says the
#     two compute the same value while `Tm.EmitWire.runRowsP` and `Tm.runCapP`
#     both still RUN -- so cutting there would have written three false reasons
#     into the exemption file.  The cut is at `Tm.EmitWire.runRowsP`.
#
#     THE EXEMPTIONS ARE W-27'S SHAPE -- an enumeration you join to be EXEMPT,
#     not to be COVERED.  `reach-exempt.txt` grandfathers the definitions that
#     were unreachable on 2026-09-25 -- 952 when the gate landed, 1,459 after
#     the same day's repair widened the population by the globals (gap 2257),
#     1,748 after W-32 rooted the walk where the binary enters, and 1,756 after
#     W-32 track G's eight witness entries arrived at the merge -- each under
#     a section that carries a reason, and it declares its own size.  It MAY
#     ONLY SHRINK: an entry that becomes reachable, stops being emitted or stops
#     existing FAILS by name and must be deleted.  A bare threshold would have
#     been the list-shaped answer this campaign has now got wrong eleven counted
#     times, and gap 2130 says so itself.  Sixteen of the sections name their
#     EXIT; fourteen of the sixteen name R3, and when the shipped binary sends
#     `planner` the cut goes, every entry under them becomes REACHED and this
#     check fails on each as STALE until it is deleted -- the ratchet doing R3's
#     bookkeeping instead of R3 having to remember it.
#
#     AND TWO CLASSES LEFT THE FILE AS NAMES (W-33 repair, README gap 2560).
#     It grew 1,756 -> 1,772 in W-33 by D51's letter, and 509 of the 1,772 were
#     two classes this gate already measures, listed one name at a time: the
#     definitions reached ONLY through a request section `tm/src` never sends
#     (296, eighteen sections all saying so) and `PlannerWit.lean`'s witness
#     fixtures (213).  They are answered by PROPERTY now -- a `CLASS unsent
#     <key>` line per DECLARED unsent section, measured by walking the graph
#     with those cuts lifted, and check 9's own `mutate.WITNESS_MODULES` under
#     its own leaf test -- and the file shrank to 1,263.  A section that stops
#     being sent is not declared, so its definitions arrive NOT EXEMPT by name;
#     a declared key that is sent FAILS as STALE; a name listed for a definition
#     a class answers FAILS as ANSWERED BY PROPERTY.  DRIVEN in a clone, seven
#     plants, control rc=0 before and after: a witness name re-listed, a
#     cut-class name re-listed, the `planner` class line deleted (235 NOT
#     EXEMPT), a class for the SENT `docs` section, a class for no section, an
#     undated class line, and a library module importing `PlannerWit` (213 NOT
#     EXEMPT and the WITNESS line) all rc=1; and a dead `def` appended to
#     `Emit.lean`, a module wholly inside the `plan` class, BUILT and was named
#     NOT EXEMPT -- the class answers what the cut section reaches, never what
#     nothing reaches.
#
#     AND A THIRD CLASS, PROOF (W-35 repair, README gap 2923).  W-35 track K
#     grew the file 1,262 -> 1,263 for one predicate of `PlanCheck.lean`, L26's
#     checker battery, whose 61 definitions were listed by name in three
#     sections although the module is unreachable BY CONSTRUCTION: only the
#     witness module and the manifest import it.  `CLASS proof <Module>` answers
#     a declared module's unreached definitions while `reach.proof_violations`
#     finds no other importer, and the file shrank to 1,202.  DRIVEN in a clone,
#     control rc=0 before and after, four plants rc=1: `Boundary.lean`
#     importing `PlanCheck` (61 NOT EXEMPT and the PROOF line), the class line
#     deleted (61 NOT EXEMPT), a PlanCheck name re-listed beside it (ANSWERED BY
#     PROPERTY), and the class line undated (RATCHET).
#
#     AND THE REASON IS GATED ON THREE HALVES NOW (W-32 repair, gaps
#     2410-2412), because the reason is what 1,756 grandfathered entries are
#     auditable BY and it was pinned by nothing.  (i) A reason that states its
#     module's census -- "N of its M emitted definitions are reached" -- is held
#     against `reach.py`'s own per-module measurement; TWENTY-THREE of the
#     twenty-seven that carried one were FALSE at `9d7fad2`, `## Planner.lean`
#     worst at "178 of its 221" where the measurement is 0 of 236, because W-32
#     rewrote the file under the new root and re-derived none of the headings it
#     moved.  (ii) A reason that is REWRITTEN must carry an ISO date, the same
#     price growth pays: the ratchet compared entry KEYS, so an existing
#     section's reason could be replaced wholesale -- driven, `## Recur.lean`'s
#     gap-501 citation, date and exit swapped for an invented sentence, summary
#     unchanged, rc=0 -- and the same plant is 61 named complaints at rc=1 now.
#     (iii) A NEW section must name an EXIT beside its date, which is what the
#     two W-32 track-G sections did not.
#
#     AND THE ROOT IS MEASURED BEFORE ANY VERDICT IS TAKEN FROM IT (W-32 repair,
#     gaps 2413 and 2414).  `sections.py` DISCARDED a request region carrying a
#     key it did not recognise, so the next dispatch arm would not fall out
#     loudly -- it would fall out invisibly.  DRIVEN in the clone, one sibling
#     key `"w32critic": 1` added to a shipped `json!`: at `kernel_bridge.rs:797`
#     this check stayed GREEN with a byte-identical summary; at
#     `kernel_log.rs:2084`, the only shipped send of `emit`, it failed with a
#     FALSE diagnosis over D16's whole log WRITER and printed a remedy that
#     would have grandfathered it.  Both are one named `UNREADABLE` complaint
#     now, and `reach.py` prints NO per-definition verdict at all while the root
#     is unmeasured.  The `#[cfg(test)]` floor is a gate too: six of the eight
#     sent sections have a test-only site and every one still has a shipped
#     site, so a section only a harness sends FAILS by name -- driven by making
#     `log`'s one shipped send unreadable, which leaves its fixture alone.
#
#     DRIVEN, W-32, in a `git clone --local` whose `.lake` is a SYMLINK to the
#     shared build (reach.py reads that tree and never writes it, and no `lake`
#     was run in the clone).  The gate has to be able to fail on the thing it
#     was built for, so a section string was deleted from the RUST.  `"emit"`
#     renamed to `"items"` at `kernel_log.rs:2084`, its only send: 8 sections
#     became 7, 1,178 reachable became 1,172, rc=1, and the six named are
#     exactly what that arm alone reached -- `Tm.emitStep`, `Tm.readEmitAt`,
#     `Tm.readEmitItem`, `Tm.EmitRefusal.json`, `Tm.Log.emitEvent` and
#     `Tm.Log.emitLine`, which is the whole of D16's log WRITER.  Reverted, rc=0.
#     `"capacity"` renamed to `"cap"` at `kernel_capacity.rs:886`, its only send
#     in a request-shaped region (the refusal fixtures in `kernel_bridge.rs` open
#     their own object and carry no `docs`, so they are not read as requests):
#     1,178 became 893 and 285 were named, across Lookahead.lean 123,
#     Boundary.lean 94, Capacity.lean 17, Arith.lean 17, Priority.lean 15,
#     Cal.lean 10, Line.lean 6, Plan.lean 2, State.lean 1 -- D10's whole
#     capacity machine.  Reverted, rc=0.
#
#     AND THE GLOBAL HALF RE-DRIVEN (W-32), because `5d9aba5` also landed after
#     its auditor had finished.  In a second clone with its OWN build tree,
#     `def w32CriticOrphanGlobal : List Nat := [2, 7, 1, 8, 2, 8, 1, 8]`
#     appended to `SealInStep.lean`: `lake build TmKernel:static` rc=0, the
#     generator wrote it as `LEAN_EXPORT const lean_object*
#     lp_TmKernel_w32CriticOrphanGlobal = (const lean_object*)&..` at
#     `SealInStep.c:94` -- the SECOND of the two global spellings, the one a
#     pattern anchored on `;` misses -- the population went 2,926 -> 2,927, and
#     this check printed `NOT EXEMPT: w32CriticOrphanGlobal (SealInStep.lean)`
#     at rc=1.  Reverted and rebuilt, rc=0.
#
#     WHAT THIS CHECK STILL CANNOT ASK, one layer further out and measured
#     rather than left to be found: a definition can be reached by a real
#     request and still have its result carried by NO response key.  Measured
#     2026-09-25 at the KEY layer -- every key the kernel emits under the
#     measured root (`docs`, `report`, `log`, `emit`, `lookahead`, and their
#     entries) is read by `tm/src`, `report.closes[].min` included
#     (`kernel_bridge.rs:521`, spent at `closing.rs:396`) -- so there is no dead
#     answer key today.  The DEFINITION-level form of the question is open and
#     is README gap 2282.
#
#     DRIVEN, in a `cp -a` clone with its own build tree, never the shared one.
#     `Tm.PlanWire.hashHex` has exactly one caller in the emitted C; its call
#     site in `planJson` was replaced by a literal (and the `rfl` theorem that
#     pins `planJson` with it), `lake build TmKernel.PlanWire` rebuilt the one
#     module, and the symbol went from FOUR occurrences in the IR to three --
#     prototype, body, boxed wrapper, no call.  Check 12 then printed
#     `NOT EXEMPT: Tm.PlanWire.hashHex (PlanWire.lean) is emitted and nothing
#     reaches it from tm_kernel_call` at rc=1, and 1,413 reachable became 1,412.
#     Reverted and rebuilt in the same clone it was rc=0 again.  Five more
#     drives, no build needed: an entry deleted names its definition; a REACHED
#     name added names itself STALE; a section with an empty reason takes its
#     ten entries down with it; an entry above the first section is named; a
#     name listed twice is named.  All six at rc=1.
#
#     THE THREE KNOWN INSTANCES, CONFIRMED HERE RATHER THAN QUOTED: `Tree.lean`'s
#     ten are one section with D52's reason, due to leave when D27 lands;
#     `Recur.lean`'s 58 are one section with gap 501's; and `assignFold`,
#     `dayRows`, `dayPlan`, `dayAssigned` and `keptBreaksToday` are all REACHED,
#     which is D50's P9 composition seen in the emitted C and not in the source.
#
#     THE COST IS MEASURED, NOT QUOTED (5.11): three runs at 2.67, 2.67 and
#     2.69 s, at load average 3.3-7.5 with another session's `lake` on the
#     machine (gap 1333).  Where it goes, timed INSIDE one run so the parts sum
#     to the whole: 1.32 s to take 3,142 qualified `def`/`abbrev` names out of
#     the source, 0.66 to read the emitted function bodies out of
#     `.lake/build/ir`, 0.30 for the section walk W-32 added (both languages:
#     86 library modules indexed by definition head, six of them stripped, and
#     `tm/src`'s 29 Rust files read once), 0.15 to walk the graph, 0.25 for the
#     second pass that measures the load-time class, and 0.00 for the exemption
#     file.  **The W-32 root costs 0.30 s of 2.68**, measured against HEAD's own
#     reach.py re-run in the same clone in the same minute: 2.57, 2.39, 2.36 s.
#
#     AND THE FIGURE THIS PARAGRAPH USED TO CARRY WAS STALE, which is §5.11
#     happening to §5.11's own paragraph.  It read "three runs at 1.65, 1.66 and
#     1.62 s ... 0.63-0.64 s to take 3,042 qualified `def` names out of the
#     source" -- measured before the same day's repair widened the population
#     from 2,365 to 2,926 and the source roster from 3,042 to 3,142 (gaps
#     2257/2258).  The repair moved the numbers the check PRINTS and not the
#     numbers this comment quotes, because only the first are measured where
#     they are read.
#
#     AND THE SECOND PASS IS DELIBERATE.  Folding it into the first reads the
#     45 MB tree once instead of twice and costs 0.65 s -> 0.88-0.94, because
#     6,655 initialiser bodies have to be brace-balanced too; check 12's wall is
#     the same either way, and CHECK 11 DOES NOT ASK THAT QUESTION -- the
#     one-read version was measured spending a quarter second of check 11's
#     budget on a measurement check 11 has no use for (1.64-1.68 s against its
#     1.42-1.45 s now, which is where W-30 left it).  A gate paying for another
#     gate's question is a cost that shows up as nobody's line item.  Check 11
#     reads the tree again in its own process; sharing that would need one
#     process.
out=$( python3 reach.py 2>&1 )
if [ $? -eq 0 ]; then
  say "every emitted definition is reached" "ok  ($( printf '%s\n' "$out" | tail -1 ))"
else
  say "every emitted definition is reached" "FAILED"; fail=1
  printf '%s\n' "$out" | head -20
fi

# 13. A FIELD THE WIRE EMITS MUST HAVE A WRITER THE DAY REACHES.  README gap
#     2403 (W-32's land step): the shipped binary's `--json plan` prints
#     twelve diagnostic fields with values in them, the kernel's
#     `Planner.Diagnostics` carries all twelve, `PlanWire.diagJson` emits all
#     twelve -- and `Planner.dayDiagnostics` writes THREE, leaving nine at
#     `Diagnostics.empty`.  The fourth composition gap of this campaign and
#     the fourth found BY HAND, because every gate measured the parts: a type
#     that matches the fork's shape pins nothing about the fork's values.  Gap
#     2419 is the same fact from the proof side -- `PlanCheck.impossibleKept`
#     is provably empty at every request because nothing writes `impossible`.
#
#     THE PROPERTY (`fields.py`, W-33 track A): for every key the planner wire
#     emits under `diagnostics`, the field it projects is assigned BY NAME
#     inside a definition that `Planner.dayPlan` REACHES in the emitted call
#     graph -- `callgraph.py`'s walk, rooted at the day builder instead of at
#     the door -- or it is named in `fields-exempt.txt` under a dated reason
#     with an EXIT.  Both directions of the wire beside it (5.8): every field
#     of the structure is emitted under some key, every key projects a field.
#     The emitter is found by the KEY, not by name; the writer's SUBJECT must
#     be of the structure's type as the source declares it, because
#     `SegFlags` has `underused`, `hot` and `deferred` too and the first run
#     counted `assignedSeg` as a writer of the diagnostics -- the gate was
#     green on its own class for one run and its author caught it.  The
#     exemptions are W-27's shape and may only SHRINK: a field listed there
#     that is written FAILS as STALE, which is how the nine leave one step at
#     a time -- W-33 track P writes `impossible`, and at that merge its line
#     goes STALE and is deleted.  AND THE OTHER DIRECTION IS CHECKED SINCE THE
#     W-33 REPAIR (README gap 2564): a line the file did not hold at HEAD, for a
#     field the structure already had there, FAILS as RATCHET -- driven, W-33's
#     auditor deleted `blocked :=` and added a dated line and this was green.
#
#     DRIVEN in a clone, five plants, control rc=0 between each: `hot :=
#     Capped.nil` added to `dayDiagnostics` (STALE, the exemption of a
#     written field); `notes :=` removed from it (UNWRITTEN by name); the
#     `"waiting"` pair removed from `diagJson` (NOT EMITTED); `d.blocket`
#     (NO SUCH FIELD); and a `PlannerWit` fixture building `{ Diagnostics.empty
#     with hot := .. }` (still UNWRITTEN: a witness is not the day).
#
#     WHAT IT CANNOT SEE is `fields.py`'s header: a positional constructor
#     (`Diagnostics.empty` is one, rightly counted as no write), a write that
#     copies a field, a writer the generator inlined, and a field written with
#     a value that is always the empty one -- written is a floor under
#     populated, and the witness that a field is POPULATED is a `PlannerWit`
#     request at which it is not `Diagnostics.empty`'s, which is check 9's to
#     demand of the step that writes it.
#
#     THE COST, MEASURED: 1.53, 1.57 and 1.52 s, three runs at load 9-10 with
#     this step's own cargo runs on the box, almost all of it the read of
#     `.lake/build/ir` that checks 11 and 12 also pay, each in its own process
#     (5.11: re-measure, do not quote).
#
#     AND THE SENT HALF (W-36 track H, README gap 2931): every JSON key path the
#     host codec's `planner_json` (tm-core/src/planwire.rs) writes must be
#     DECODED by the kernel's reader of the `planner` section, or be a dated
#     line of `sent-exempt.txt` with an EXIT, which may only shrink.  W-35
#     track R's `overtime.grown` was written and read by nothing, and the input
#     half above could not see it: it counts the fields of DECODED records, and
#     a key no reader decodes never becomes one.  `sentkeys.py` reads both
#     sides from source -- the Rust codec's `json!` literals, inserts and
#     helpers, and the Lean reader followed from the definition that `jget`s
#     `planner` off the request -- and its header says what that cannot see.
#     It asks ONE section of ONE encoder, and says so in its line (gap 3081).
#     AND THE WRITTEN HALF (W-36 repair, README gap 3132): the converse of the
#     sent half -- every key the kernel's planner reader DECODES must be written
#     by the host codec (`planner_json` and every codec function taking the
#     section as `&mut Value`), or be a dated line of `written-exempt.txt` with
#     an EXIT, which may only shrink.  `overrides.drop` is read by the day's
#     `d done` what-if and written by no host function.
out=$( python3 fields.py 2>&1 )
if [ $? -eq 0 ]; then
  say "every emitted field has a writer" "ok  ($( printf '%s\n' "$out" | tail -4 | head -1 ))"
  say "every decoded field has a reader" "ok  ($( printf '%s\n' "$out" | tail -3 | head -1 ))"
  say "every sent key has a reader" "ok  ($( printf '%s\n' "$out" | tail -2 | head -1 ))"
  say "every decoded key has a writer" "ok  ($( printf '%s\n' "$out" | tail -1 ))"
else
  say "every emitted field has a writer" "FAILED"; fail=1
  printf '%s\n' "$out" | head -20
fi

#     AND THE INPUT HALF (W-34 repair, README gap 2734): every field the
#     planner request DECODES must be READ by a definition `Planner.dayPlan`
#     reaches, or be a dated line of `inputs-exempt.txt` with an EXIT, which may
#     only shrink.  W-34's reuse critic measured five decoded fields no
#     definition of the day reads -- `RuntimeIn.brk`, `.lastHash`, `.yesterday`,
#     `PlanOverrides.estMin`, `.extraMin` -- which no gate could see: this check
#     was output-side only and check 12 counts a decoder as reached.  The gate's
#     first run found exactly those five and no other.  `fields.py`'s input
#     header has how a subject is typed and what that cannot see.  It prints
#     its own line below this check's, one process for both halves.
# 14. THE ENVIRONMENT CHECK 3 READS IS ONE THE KERNEL CHECKED.  W-34 repair,
#     README gap 2730.  `#print axioms` reads the environment and does not
#     re-check it, so a declaration added with the kernel check switched off is
#     audited as if it had been checked.  DRIVEN at `fb05f4e` in a clone: a
#     module importing `Lean` whose `def .. : True := by run_tac (withOptions
#     (skipKernelTC := true) (addDecl (thmDecl `Tm.v34Bad : False := True.intro)))`
#     let `theorem v34_one_is_two : (1 : Nat) = 2` build, print "does not depend
#     on any axioms", and pass checks 1-13, rc=0.  totality.py now refuses the
#     ROUTE (an import outside the kernel), and this is the PROPERTY: every
#     library module is replayed into the environment its imports give by the
#     pinned toolchain's `leanchecker`, whose `Environment.replay` runs the
#     kernel with no options to switch off.  On the plant: rc=1, "(kernel)
#     declaration type mismatch, 'Tm.v34Bad' has type True but it is expected
#     to have type False".  `replay.py`'s header has what it cannot see (an
#     axiom replays clean) and why it keeps a cache (a cold run is 3 min 21 s
#     wall at 6 jobs, 181 s of it PlannerWit; a remembered pass is keyed on the
#     module's .olean and every import's key, and a failure is never kept).
out=$( python3 replay.py 2>&1 )
if [ $? -eq 0 ]; then
  say "the kernel replays every module" "ok  ($( printf '%s\n' "$out" | tail -1 ))"
else
  say "the kernel replays every module" "FAILED"; fail=1
  printf '%s\n' "$out" | head -20
fi

exit $fail
