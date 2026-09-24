#!/usr/bin/env python3
"""check.sh's check 9 (D40): every definition a step ADDS is CONSTANT-FOLDED.

Three times in this campaign a definition shipped whose body nothing could tell
from a constant, and all three were found by a human reading code, never by a
gate:

  * W-17's P4 sort key -- the two halves swapped, 1,342 tests green.
  * W-18's nine candidate facts -- invert one, the whole suite green, and
    `tm plan` visibly re-ranks.
  * W-19's `Planner.Ranked.gatherable` -- `:= true`, and 168 build targets,
    every theorem in `Planner.lean`, all nineteen `PlannerWit` `decide`
    witnesses and check.sh 8/8 stay green.

That is README gap 577's class, and D40 is the gate that ends it: replace a
definition's body with a CONSTANT OF ITS TYPE, one constant at a time, and
something must FAIL.  If nothing fails, no theorem, witness or test in the
package distinguishes the definition from that constant, and the definition is
unwitnessed no matter how carefully it is written.

WHAT IS MUTATED.  Every `def` and `abbrev` in kernel/TmKernel/TmKernel/*.lean --
the library -- that is NEW OR CHANGED since the baseline commit named on the
first line of `mutations.txt`.  Scoped that way because D40 scoped it that way:
a full sweep of the existing kernel was DECLINED as producing a backlog rather
than preventing new instances, and the moment a definition is introduced is when
its distinguishing witness is cheapest to write.  "Changed" is by the sha1 of
the body text, so a step that rewrites an existing body owes a mutation for it
too, and a step that only re-indents one does not.

THE CONSTANTS, by the declared return type -- the text between the last
depth-zero `:` of the header and the `:=` that opens the body, RESOLVED first
through library `abbrev` synonyms and then through its own depth-zero arrows:

    Bool          true   and   false      (AGENTS 5.8: both directions)
    Prop          True   and   False
    Nat           0      and   1
    A -> ... -> T the constants of T under binders: `fun _ ... _ => c`
    anything else default

AND, BESIDE THEM AND NEVER INSTEAD OF THEM, THE IDENTITY ON THE ACCUMULATOR
(`identity_for`, README gap 985).  A constant of the type is not the only
degenerate body a definition can have, and for the half of this kernel whose
types have no `Inhabited` instance it is not even an available one.  When the
result type appears among the definition's own argument types, the degenerate
body is the argument:

    PlanReq.rePlaceWalk : ... -> Assign -> List ... -> Assign
        |->  fun a0 _ => a0
    PlanReq.deferWalk   : ... -> List Placed -> Assign -> List Placed
                                  -> List Placed × Assign
        |->  fun a0 a1 _ => (a0, a1)
    placeAt (q : Placed) (t : Nat) : Placed          |->  q
    PlanReq.deferOne (...) (a : Assign) (q : Placed) : Placed × Assign
        |->  (q, a)

That is the shape the walk-and-fold bug class actually takes -- a fold that
returns its accumulator unchanged on the branch that should have changed it is
not a constant, and no constant catches it -- and it EXISTS for an uninhabited
type, which is what makes it the one mutation that reaches an UNFOLDABLE
definition.  Measured at the run that added it: **395 of 2,853** library
definitions have one, **5 of the 23** UNFOLDABLE rows are reached by it (and
all five are PINNED), and **18 are not** -- three of step 6's algorithm
(`PlanReq.deferFold`, `PlanReq.finalAssign`, `dayDiagnostics`, none of which
takes an argument of its own result type) and the fifteen `PlannerWit` witness
fixtures, which take no arguments at all.

THE RESOLUTION IS NOT DECORATION, IT IS W-20'S BLOCKER.  Until this repair the
table was keyed on the type's LITERAL TEXT, so `Bool` got both directions and
`Nat -> Bool` got `default` -- and `default : Nat -> Bool` is `fun _ => false`,
which is the ONE direction that does not matter.  Driven at the repair step in a
`git clone --shared` sandbox: `def w21DirectBool (n : Nat) : Bool := true` was
caught (SURVIVED, gate rc=1) and the SAME CONSTANT arrow-spelled,
`def w21ArrowBool : Nat -> Bool := fun _ => true`, was reported `:= default
PINNED` with `python3 mutate.py --gate` EXITING 0.  `Planner.posLt` and
`Planner.victimLt` were in that class and are re-audited at both directions in
`mutations.txt`.  Measured over the library: 99 definitions are arrow-spelled to
a scalar and 19 more reach one through an `abbrev` (`Hist := Fin 6 -> Nat`,
`Day := Nat`, `PlanCheck.Eligible := ... -> Bool`, which is `gatherable`'s own
shape).  A type carrying a depth-zero `forall` or `,` keeps `default`: its
binders are not all anonymous, and an error inside the declaration is INVALID,
which fails the gate.

`default` is a constant of ANY inhabited type, arrow types included, so it
remains the fallback for every type the table cannot name.

HOW A MUTATION IS APPLIED, and why the line numbers do not move.  The body's
characters, from just after the header's `:=` to the end of the declaration
(`termination_by` and `decreasing_by` included), are replaced by the constant
followed by exactly as many newlines as were removed.  The file keeps its line
count and every other declaration keeps its line number, so an error's location
is comparable against the mutated declaration's own line range.

THE FOUR VERDICTS, and the reason each of the last two exists:

    PINNED      the build FAILED, and no error is inside the mutated
                declaration.  Something in the package can tell this definition
                from that constant.  This is the verdict a definition must earn.
    SURVIVED    the build SUCCEEDED.  Nothing distinguishes it.  check 9 FAILS.
    INVALID     the build failed WITH an error inside the mutated declaration
                that is NOT the one below.  check 9 FAILS, because a build that
                fails for the wrong reason is exactly the false PINNED this gate
                would otherwise hand out for free.
    UNFOLDABLE  the build failed inside the mutated declaration with exactly
                `failed to synthesize ... Inhabited T`: the type has NO constant
                to fold to, so D40's mutation does not exist for this
                definition.  ROSTERED BY NAME with the type in the reason
                column, counted on every run, and NOT fatal.
    LITERAL     the BODY is itself a constant -- `true`, `7`, `fun _ => true`.
                Raised BEFORE any build, alongside whatever the type's own
                constants then earn, never instead of them.  It is not fatal
                because the gate cannot tell a defect from a wire bound: 66
                library definitions are bare literals and 64 of them are bounds
                (`maxCands : Nat := 1024`), which are SUPPOSED to be constants.
                What it buys is that PINNED stops reading as "nothing can tell
                this from a constant" when the body IS one -- the repair step's
                probe `def w21Seven (_x : Nat) : Nat := 7` is PINNED by `0` and
                by `1` and is the constant 7, and before this verdict the gate
                printed only the two PINNEDs and `0 SURVIVED`.  A `Bool` or
                `Prop` literal, or a `Nat` literal 0 or 1, is still SURVIVED and
                still FATAL: `Planner.Ranked.gatherable := true`, the W-19
                defect D40 exists for, is caught by the constant, not by this.

WHY UNFOLDABLE EXISTS, AND WHY IT IS NOT A FREE PASS.  This verdict was added at
the W-20 LAND step, where check 9 met its first real step output -- 46 new or
changed definitions from tracks P and G -- and reported **23 PINNED, 23 INVALID,
0 SURVIVED**.  Every one of the 23 INVALID was the same error, and none was a
defect in the definition: `Look.Slot`, `Planner.Placed`, `Planner.Assign`'s
products, `Planner.Diagnostics`, `Planner.PlanReq`, `Capped _` and `WfPlan` have
no `Inhabited` instance, and `deriving instance Inhabited` was tried and Lean
answered "failed to generate" for four of the five.  THAT IS AGENTS 5.1 WORKING:
the kernel's types are `Bool` + `Subtype`, and a bounded type deliberately has no
inhabitant anybody can name without a proof.  Adding those instances to make the
gate green would hand out bounded values without their smart constructors, which
is a weakening of the kernel to suit a checker.

So the fold is UNREPRESENTABLE for such a definition, and this file says so by
name rather than by pattern.  THE SHAPE IS CHECK 8'S ALLOW-LIST, deliberately:
exact names, never a class; the reason recorded per name; the count printed on
every run so it cannot grow unnoticed.  **It narrows D40's letter** -- "the step
must show something FAILING for each" -- for the definitions in question, and the
W-20 land block puts that to the owner as a decision to confirm or reverse
(README gap 980).  Reversing it is one line: delete the UNFOLDABLE branch in
`mutate_one` and the gate fails again on all 23.

THE ROSTER.  `mutations.txt` holds the baseline commit and one row per audited
definition: the body's sha1, the file, the QUALIFIED name, the constants tried,
and the first error the build reported for each.  The key is `(file, qualified
name)` since W-25 track A; it was the SHORT name, which two definitions in one
file could share (README gap 1422, and 38 pairs do).  The qualified names are
not a guess: all 2,960 in the library were put through `#check @<name>` in one
kernel build at that step, and 2,957 resolved -- the three that did not are
`Plan.lean`'s `private def`s (`orientCore`, `orientDocs`, `orientPlan`), whose
constants Lean mangles and which no module outside can name.  check.sh's check 9 RUNS the mutation
for any new-or-changed definition with no matching row, and TRUSTS a row whose
sha1 matches -- otherwise every run of check.sh would re-build the kernel once
per audited definition forever, and the steady-state cost has to be ~0.

WHAT THIS CANNOT SEE.  Measured or argued, never guessed:
  * AN UNFOLDABLE DEFINITION THAT NO IDENTITY REACHES IS NOT AUDITED AT ALL.
    It is named and counted on its own line -- "pinned by nothing" -- and that
    is the whole of what it gets: nothing here says any theorem reads it.  At
    the W-20 land step this was HALF of what the step added, 23 of 46, and the
    half was not evenly composed: 15 are `PlannerWit` witness FIXTURES, where a
    literal body is correct and the exemption is benign, but the other EIGHT
    were step 6's own algorithm.  The identity on the accumulator (above) took
    FIVE of those eight -- `placeAt`, `PlanReq.displaceInto`,
    `PlanReq.deferOne`, `PlanReq.deferWalk` and `PlanReq.rePlaceWalk`, all
    PINNED -- and the exemption is now 18 of 46.  What is left is
    `PlanReq.deferFold`, `PlanReq.finalAssign` and `dayDiagnostics`, each of
    which takes a `PlanReq` and returns something else, so neither a constant
    nor an identity exists for it; README gap 980 puts the exemption itself to
    the owner and gap 1035 names what would reach these three.
  * A ROW IS A CLAIM.  check 9 does not re-run a mutation whose sha1 matches, so
    a row written by hand, with a plausible error string, passes.  What makes it
    not a bare claim: `mutate.py --write` appends a row only after watching the
    build fail, the row names the definition and the constants, and it lands in
    a diff.  `mutate.py --verify` re-runs every row and is what an auditor or a
    repair step uses; it is not in check.sh because it costs one kernel build
    per row.
  * A CONSTANT BODY IS NOT ALWAYS VISIBLE.  `literal_body` matches a bare
    scalar -- `true`, `7`, `"x"`, with or without `fun _ =>` in front.  A RECORD
    OR STRUCTURE LITERAL (`{ a := 1, b := 2 }`) is a constant too and is NOT
    matched: that is the witness-fixture shape, where a literal body is what the
    definition is FOR, and 15 of the 23 UNFOLDABLE rows are exactly that.
  * THE IDENTITY'S MATCH IS TEXTUAL TOO.  A result component is matched against
    a binder by EXACT type text after `abbrev` resolution, so a source spelled
    differently from the result -- definitionally equal, textually not -- is a
    miss.  It is never a false PINNED: an identity that does not elaborate is
    an error inside the declaration, which is INVALID, which FAILS the gate.
    Implicit, instance and strict-implicit binders are not offered as sources.
  * THE TYPE RESOLUTION IS TEXTUAL, AND ONE `abbrev` DEEP TIMES THREE.  A type
    spelled through a `def` synonym rather than an `abbrev` is not unfolded (a
    `def` is not reducible, and a constant written at the unfolded type would
    fail to elaborate); a type built by a function (`Capped n`) is not either.
    Those keep `default`, which is the old behaviour and not a regression.
  * ONLY `def`, `abbrev` AND `instance`, and only in the library.  `theorem` has
    no body to fold (its "constant" is a different proof of the same statement,
    which is not this defect class); `structure` and `inductive` are not
    mutated.  `instance` WAS OUTSIDE THIS SENTENCE AND INSIDE THE CODE, and
    `mutations.txt`:2 calls this docstring the specification -- so check 9's
    specification was stale about check 9's own scope (the W-28 repair step,
    README gap 1880).  `HEAD` matches `(def|abbrev|instance)` and
    `ANON_INSTANCE` synthesises a roster name for an anonymous one; the argument
    for it is at `HEAD`'s own comment, which is that an instance IS a definition
    with a body that can be folded.  Nothing could catch the drift: check 8 does
    not sweep this file as PROSE, and its header records that blind spot.
    `Check.lean`, `Negative.lean` and `Goals.lean` are outside the
    scope, and so is every line of Rust -- a constant-folded `fn` in
    `tm-core/src/planner.rs` is invisible to this (README gap 936).
  * A CONSTANT IS NOT AN INVERSION.  `gatherable := true` is caught here;
    `gatherable` with two of its five clauses swapped is NOT -- the body is
    still not a constant.  D40 buys the constant-fold class, which is the one
    that has actually shipped three times, and no more (README gap 937).
  * TWO CONSTANTS, NOT ALL.  A `Nat`-valued definition that every witness pins
    at 7 survives neither `0` nor `1`, but one that nothing reads except through
    `if n > 0` is pinned by `0` and says nothing about the rest of its range.
    AND THE VERDICT USED TO SAY MORE THAN THAT: a body that IS the constant 7
    earned PINNED, which is the word D40 coined for "something can tell this
    from a constant", and the run line said `0 SURVIVED`.  That is what the
    LITERAL verdict is for; PINNED means DISTINGUISHED FROM THE CONSTANTS TRIED
    and has never meant more.
  * THE EXTENT RULE IS TEXTUAL.  A declaration runs to the next line that starts
    at column zero with a declaration keyword, an attribute, a comment opener,
    `namespace`/`section`/`end`/`open`/`set_option`/`mutual` or `#`.  A
    definition laid out some other way is reported UNPARSED and fails the gate
    rather than being skipped silently -- INCLUDING an INDENTED one, which until
    the repair step produced no row at all: `HEAD` anchored at `^`, so
    `namespace T` / two spaces / `def indentedProbe : Bool := true` was neither
    audited nor reported while Lean accepted it and `citations.py` saw the name.
    `INDENTED` now reports it, outside block comments (`/- ... -/` nests, and a
    commented-out `def` must not fail the gate for a sentence).  There are 0
    indented definitions in the library today, so this is a latch, not a repair
    of live code.
  * THE FILE SET IS `git diff` PLUS `git ls-files --others`.  `git diff
    --name-only <commit>` never lists an UNTRACKED file, and AGENTS acceptance
    runs check.sh BEFORE the commit -- so until the repair step every definition
    in a step's brand-new module was exempt at exactly the moment the gate
    exists to bite.  Still unseen: a library file outside
    `kernel/TmKernel/TmKernel`, and anything `.gitignore` hides.
  * A KILLED RUN.  The mutation is restored in a `finally`, which covers an
    exception but not a SIGKILL, so the original bytes go to a `.mutate-in-flight`
    sidecar first and every run begins by putting back whatever it finds.  A
    machine that loses power between the two writes still leaves a mutated file,
    and `git status` is what catches that.
  * IT PROVES A WITNESS EXISTS, NOT THAT IT IS THE RIGHT ONE.  A definition
    whose only distinguishing witness is a `#print axioms` line, or a
    `Negative.lean` cheat, is PINNED by this gate and may still be under-stated.
"""

import collections
import hashlib
import os
import re
import subprocess
import sys

import leanfiles

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
PKG = os.path.join(HERE, "TmKernel")
LIB = os.path.join(PKG, "TmKernel")
ROSTER = os.path.join(HERE, "mutations.txt")
LAKE = os.path.expanduser("~/.elan/bin/lake")

DECL_KW = ("theorem", "lemma", "def", "abbrev", "structure", "inductive",
           "instance", "class", "example", "opaque", "axiom", "namespace",
           "section", "end", "open", "set_option", "mutual", "deriving",
           "attribute", "macro", "notation", "syntax", "@[", "/--", "/-!",
           "/-", "--", "#", "private", "protected", "noncomputable",
           "partial", "unsafe", "scoped", "local", "variable", "universe",
           "import", "where", "termination_by", "decreasing_by")

BODY_KW = ("termination_by", "decreasing_by")

# **`instance` IS A DEFINITION** (README gap 1421).  It carries computational
# content -- a `Decidable` instance decides, a `KeyHash` instance hashes -- and
# this pattern read `def|abbrev` only, so an instance was neither rostered nor
# OWED: `owed` is `[d for d in decls if d not in rostered]` over what this
# returns, so a declaration this cannot see is a declaration the gate reports
# `0 owed` about.  The hole was EMPTY when it was found (0 instances added since
# the baseline, verified by `git diff`), and it is the shape the obvious fix for
# README gap 1332's `pinned by nothing` rows would ADD: a hand-written
# `instance : Inhabited X := <a chosen default>` is a default constructor for a
# sum type entering the kernel through the one gate built to catch new
# definitions.
#
# AN ANONYMOUS INSTANCE HAS NO NAME TO ROSTER, and ALL TWELVE of the library's
# instances are anonymous (measured at the W-24 repair step; the five lines a
# naive grep calls a named instance are prose beginning with the word), so
# `ANON_INSTANCE` gives each one a name derived from its TYPE -- stable across
# line moves, which a line number would not be -- and the roster row is keyed on
# it like any other.
HEAD = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)[ \t]+)*"
    r"(def|abbrev|instance)[ \t]+([^\s(){}\[\],:]+)")

# `instance : C T := ...` and `instance (a b : T) : C T := ...` -- the forms
# with no name at all.  The synthesised name is an inst_ prefix plus the identifier
# characters of everything between the last depth-zero `:` of the header and
# the `:=`, which is the CLASS the instance is for.
ANON_INSTANCE = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)[ \t]+)*"
    r"instance[ \t]*(?=[:({\[])")

# The same header INDENTED.  Lean accepts it and this file's extent rule does
# not: `starts_declaration` answers False for any line beginning with a space,
# so an indented `def` used to produce no row at all -- neither audited nor
# UNPARSED -- while the header promised the opposite.  It is reported UNPARSED,
# which FAILS the gate, rather than supported: supporting it means a second
# extent rule, and there are 0 indented definitions in the library today.
INDENTED = re.compile(
    r"^[ \t]+(?:@\[[^\]]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)[ \t]+)*"
    r"(def|abbrev)[ \t]+([^\s(){}\[\],:]+)")

CONSTANTS = {"Bool": ["true", "false"], "Prop": ["True", "False"],
             "Nat": ["0", "1"]}

# An `abbrev` whose body is a type: `abbrev Hist := Fin 6 -> Nat`, `abbrev Day
# := Nat`, `abbrev PlanCheck.Eligible := PlanReq -> DayPlan -> Seg -> Id ->
# Bool`.  `abbrev` and not `def`, because an `abbrev` is reducible by
# construction and a constant written at the unfolded type elaborates at the
# folded one; a `def`-spelled synonym does not and is left alone.
ABBREV = re.compile(r"^abbrev[ \t]+([A-Za-z_][A-Za-z0-9_.']*)"
                    r"(?:[ \t]*:[ \t]*(?:Type|Sort)[^\n:=]*)?[ \t]*:=[ \t]*"
                    r"([^\n]+)$", re.M)
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")

# A body that IS a constant, with or without `fun` binders in front of it.  See
# `literal_body` and the LITERAL verdict.
LITERAL = re.compile(r"^(?:fun[ \t][^=]*=>[ \t]*)?"
                     r"(true|false|True|False|[0-9]+|\"[^\"]*\"|'.')$")


def read(path):
    with open(path, encoding="utf-8") as handle:
        return handle.read()


# THE WALK IS `leanfiles.lean_files` since the W-22 repair step; this file no
# longer has one of its own.  The prune list it used to hold named `target`,
# which is a legal Lean module path component, so a library module under
# `kernel/TmKernel/TmKernel/target/` was reported `NOT IN lib_files()` while
# `touched()` below saw it -- the same "two checkers disagreeing about whether a
# file exists" failure `touched()`'s docstring names, one layer down from the
# recursion W-21 repaired.  Driven: `lib_files()` stayed at 83 files with a
# `target/Probe.lean` holding a `partial def` on disk.


def lib_files():
    """The library's .lean files, RECURSIVELY, as relative paths under kernel/.

    IT USED TO BE ONE LEVEL DEEP, and `touched()` three functions below asks
    git with a RECURSIVE pathspec -- so a module in a SUBDIRECTORY was put into
    `moved` by one and then dropped by the other for not being in this list.
    `citations.py` and `totality.py` enumerated the same set the same wrong way
    and `check.sh` line 204 states it as `TmKernel/**.lean`, a recursion that
    did not exist anywhere.  DRIVEN at the W-21 repair step:
    `TmKernel/TmKernel/Sub/Probe.lean` holding `def w21SubGatherable (_n : Nat)
    : Bool := true` -- gatherable's own shape, the one D40 exists for -- and a
    `partial def`, which is a HARD RULE, gave `--gate` rc=0 "0 owed",
    `totality.py` rc=0 and `citations.py` rc=0 with byte-identical counts.  The
    control, the same definition at the top level of `PlanCheck.lean`, was
    OWED.  That is the "two checkers disagreeing about whether a file exists"
    failure `touched()`'s own docstring names, in this file, against itself.

    AND THE WALK IS NOT HERE ANY MORE (the W-22 repair step): four checkers
    enumerated the kernel four ways, `check.sh`'s check-3 roster grep was still
    one level deep, and the three recursive walks shared a prune list that hid a
    directory named `target`.  `leanfiles.lean_files` is the one enumeration.

    AND THE ROOT MODULE IS IN IT (the W-23 repair step; README gap 1314).  The
    walk was called on `LIB`, the module DIRECTORY, so `TmKernel/TmKernel.lean`
    -- which Lake compiles into the same library -- was never folded, the same
    way check 3's roster never audited a theorem there.
    `leanfiles.library_files` names the root."""
    return sorted(os.path.relpath(str(p), HERE).replace(os.sep, "/")
                  for p in leanfiles.library_files(PKG))


# ---------------------------------------------------------------------------
# WITNESS MODULES, AND THE VERDICT FIXTURE (README gap 1086).
#
# 18 of 77 rostered rows were "pinned by NOTHING" -- no constant of the type,
# no identity on an accumulator, no synthesised term -- and ALL 18 are in
# `PlannerWit.lean`.  That is not a coincidence and it is not a defect: a
# witness fixture's body is a literal BECAUSE the fixture is a named day, a
# named request, a named slot, and the theorem beside it computes the planner's
# answer AT that day.  Fold one to some other constant and its own theorem
# becomes false by construction, which measures nothing about any rule -- and
# for these types no constant exists to fold to in the first place, which is
# why they sit in the exemption rather than in the audit.
#
# So they are DECLARED exempt, and the declaration is a rule with three
# conjuncts, every one of them structural.  A definition is a FIXTURE when:
#
#   (a) it is declared in a module named in `WITNESS_MODULES` below -- EXACT
#       PATHS, never a pattern and never a name regex.  `^the[A-Z]` or
#       `.*Wit.*` would have swallowed a real rule the day someone named one
#       theEligibleFilter -- a name nothing declares, spelled without
#       backticks because check 8 is right to ask.  Check 8's allow-list
#       discipline, for the fourth time in this file;
#   (b) the module really is a LEAF of the module graph -- nothing in the
#       library imports it, so no definition outside it can consume what it
#       declares.  This is CHECKED (`witness_violations`), not assumed, and a
#       violation FAILS the gate: the whole force of (a) is that a witness
#       module cannot quietly become a library module, and the one thing that
#       would make it one is an import;
#   (c) the fold could not speak about it anyway -- every verdict it earned is
#       UNFOLDABLE or UNAVAILABLE.  A definition in a witness module that a
#       constant, an identity or a synthesised term DID pin stays PINNED and
#       stays audited; this verdict only re-labels rows that were already in
#       the "pinned by nothing" bucket, so it can subtract nothing from what
#       the gate measures.
#
# WHAT IT STILL CANNOT SEE, and what the rows need to leave the exemption:
#
#   * FIVE of the 18 are `Capped _`-typed -- `routineCap`, `crowdedCap`,
#     `lapsedCap`, `busyCap` and `busyCands` -- and README gap 1086 calls them
#     three, which is its own prose and not a measurement (`Capped RoutineIn`
#     four times and `Capped (Look.Cand x Option Look.Floor)` once).  A
#     constant of that type EXISTS and this kernel declares it:
#     `Capped.nil {a : Type} : Capped a := <[], by simp>` at Planner.lean:124.
#     Two rules here keep it out of reach, and both are textual, not deep:
#     `nullary_constants` is KEYED BY FILE on purpose (a name from another
#     module may need a prefix this file cannot compute) and `Capped.nil` is
#     in `Planner.lean` while the fixtures are in `PlannerWit.lean`; and
#     `type_constant` cannot resolve `Capped RoutineIn`, a type built by
#     applying a function, so it never asks.  Widening either is a decision
#     about what a checker may synthesise ACROSS modules, which is README gap
#     980's question, not a patch.
#   * The other thirteen are `PlanReq` (eight), `WfPlan`, `PlanReqIn`,
#     `Look.Slot`, `Look.PlanFacts` and `Look.Cand x Option Look.Floor`.
#     Those are `Bool` + `Subtype` types with no `Inhabited` instance (AGENTS
#     5.1), deliberately: handing them one to make a checker green would give
#     out bounded values without their smart constructors.  Gap 1088's fixture
#     swap -- one `PlannerWit` fixture for another -- is the different
#     experiment that reaches them, and it asks a different question.
#   * THE RULE IS ABOUT A MODULE, NOT ABOUT A BODY.  A definition in a witness
#     module that is NOT a fixture -- a helper rule somebody put there for
#     convenience -- is exempt by (a) the moment (c) holds of it.  What stops
#     that costing anything is (b): nothing outside the module can read it, so
#     a rule declared there is a rule nothing runs.
WITNESS_MODULES = ("TmKernel/TmKernel/PlannerWit.lean",)


def module_name(path):
    """`TmKernel/TmKernel/PlannerWit.lean` -> `TmKernel.PlannerWit`, the name
    an `import` line spells."""
    rel = path.split("/", 1)[1] if "/" in path else path
    return rel[:-len(".lean")].replace("/", ".")


def witness_violations():
    """Why `WITNESS_MODULES` may not be trusted, as a list of sentences.

    Two ways it can go wrong, and both FAIL the gate rather than quietly
    widening the exemption:

      * a listed path is not a library module at all (a rename, a deletion) --
        an allow-list entry that matches nothing, which is exactly what check
        8's `0 allow entries unused` line exists to catch;
      * some library module `import`s a listed module, which makes its
        definitions reachable from code the gate is supposed to audit and
        ends the leaf property conjunct (b) rests on.

    The import scan is TEXTUAL, like everything else here: `import <name>` at
    column zero, comment tail stripped.  What it cannot see is an import
    reached some other way -- there is no other way in Lean 4 -- and a module
    that imports a witness module's own importer, which is not the same claim
    and does not make the witness module non-leaf.

    **A MODULE THAT DECLARES NOTHING IS NOT AN IMPORTER FOR THIS PURPOSE**, and
    the W-23 repair step is where that had to be said out loud (README gap
    1314).  `lib_files()` was called on the module DIRECTORY and so had never
    seen `TmKernel/TmKernel.lean`; the moment the root module joined the walk,
    this check went RED -- the root module imports `TmKernel.PlannerWit`, as it
    must, or Lake would not compile it at all.  So conjunct (b) as it was
    written -- "nothing in the library imports those modules" -- was NEVER TRUE,
    and nobody could see it.

    What (b) is actually for is REACHABILITY OF DEFINITIONS: folding a witness
    fixture must not be able to change anything the rest of the library proves.
    A file with no declarations is the library's import manifest; it defines
    nothing, proves nothing and re-exports names no audited definition reads.
    So the rule is a PROPERTY -- `decl_spans` finds no declaration in it -- and
    not the root module's name, because a name list is what W-22's PRUNE
    finding was about.  Today exactly one library file has the property."""
    listed = set(WITNESS_MODULES)
    files = set(lib_files())
    out = ["%s is in WITNESS_MODULES and is not a library module" % m
           for m in sorted(listed - files)]
    names = {module_name(m): m for m in listed & files}
    for path in sorted(files - listed):
        if not decl_spans(read(os.path.join(HERE, path))):
            continue  # an import manifest declares nothing and reaches nothing
        for line in read(os.path.join(HERE, path)).split("\n"):
            head = line.split("--", 1)[0].rstrip()
            if not head.startswith("import "):
                continue
            imported = head[len("import "):].strip()
            if imported in names:
                out.append("%s imports the witness module %s, so %s is no "
                           "longer a leaf and its definitions are reachable"
                           % (path, imported, names[imported]))
    return out


def is_witness(path):
    return path in WITNESS_MODULES


def starts_declaration(line):
    if not line or line[0] in (" ", "\t"):
        return False
    head = line.split("(")[0]
    return any(line.startswith(k) for k in DECL_KW) or head.strip() in DECL_KW


def split_header(text, start):
    """Offsets of the header's `:=`, its return type, and its binder text.

    Returns a triple, or three Nones if the declaration has no depth-zero `:=`
    (equation-style `| a => ...`, which this cannot fold).  First the offset
    just past that `:=`; second the return type; third everything in FRONT of
    the depth-zero `:` -- the keyword, the name and the binders -- which is
    what `binders` reads a named accumulator out of, and which `declarations`
    stores under the key `header`."""
    depth = 0
    i = start
    colon = None
    n = len(text)
    while i < n:
        c = text[i]
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
        elif text.startswith("--", i):
            i = text.find("\n", i)
            if i < 0:
                return None, None, None
        elif text.startswith("/-", i):
            j = text.find("-/", i)
            if j < 0:
                return None, None, None
            i = j + 1
        elif c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            depth -= 1
        elif depth == 0 and text.startswith(":=", i):
            kind = text[colon + 1:i].strip() if colon is not None else ""
            return i + 2, kind, text[start:colon if colon is not None else i]
        elif depth == 0 and c == ":" and not text.startswith("::", i):
            colon = i
        elif depth == 0 and c == "|" and colon is not None \
                and not text.startswith("||", i) and text[i - 1] != "|":
            # Equation style: `def f : A -> B` then `| a => …`, whether the
            # first `|` opens its own line or follows the type on the head
            # line.  The header ends at that `|`, and the constant is written
            # with its own `:=`, which the signature does not have.
            kind = text[colon + 1:i].strip() if colon is not None else ""
            return -(i), kind, text[start:colon]
        i += 1
    return None, None, None


def anon_instance_name(line):
    """A stable roster name for an anonymous `instance`, off its CLASS.

    `instance : LT Instant := ...` is inst_LTInstant; `instance (a b :
    Instant) : Decidable (a < b) := ...` is inst_Decidableab.  It is derived
    from the header's text rather than from the line number because a roster
    key that moves when a comment is inserted is a roster key that rots -- which
    is README gap 1190, the defect the fifth column already carries.

    THE CLASS TEXT ALONE IS NOT UNIQUE, and the library proves it: `Cal.lean`
    declares `instance (a b : Instant) : Decidable (a < b)` and `Decidable (a
    \u2264 b)` on consecutive lines, and both reduce to `Decidableab` once the
    non-identifier characters go -- one roster key for two declarations, which
    the `(file, name)` dictionary would have swallowed in silence.  So a short
    digest of the whole normalised header goes on the end.  It is stable across
    line moves and across everything except an edit to the header itself, and an
    edit to the header IS a new declaration for this gate's purposes."""
    head = line.split(":=", 1)[0]
    body = head.split("instance", 1)[1]
    # Everything after the LAST top-level `:` is the class; a binder's own `:`
    # is inside brackets and is skipped.
    depth, cut = 0, None
    for i, c in enumerate(body):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and depth == 0:
            cut = i
    cls = body[cut + 1:] if cut is not None else body
    ident = "".join(c for c in cls if c.isalnum() or c == "_")
    tag = hashlib.sha1(" ".join(head.split()).encode("utf-8")).hexdigest()[:6]
    return "inst_%s_%s" % (ident or "anonymous", tag)


NAMESPACE = re.compile(r"^namespace[ \t]+([A-Za-z_][^\s]*)")
SECTION = re.compile(r"^section(?:[ \t]+([A-Za-z_][^\s]*))?[ \t]*$")
END = re.compile(r"^end(?:[ \t]+([A-Za-z_][^\s]*))?[ \t]*$")


def scope_step(stack, line):
    """Track Lean's namespace stack across one column-zero line (README gap 1422).

    THE KEY USED TO BE THE SHORT NAME, and `roster()` reads a repeated key as a
    deliberate re-audit -- so two DIFFERENT definitions sharing a short name in
    one file were indistinguishable from one definition audited twice, and only
    one of the two could ever match its row's sha.  Six pairs were live when the
    W-24 repair step found it, and the latch it left said so and stopped.

    `namespace A.B` pushes, `section` and `section foo` push an anonymous
    scope, `end A.B` pops back through whatever it names and a bare `end` pops
    one.  `open X in` is NOT a scope and does not appear here.

    WHAT THIS CANNOT SEE, and why the collision check below is kept rather than
    deleted: this is a textual tracker, not Lean's elaborator.  A `namespace`
    inside a `mutual` block, a scope opened on a line this regex spells
    differently, or an `end` that names a prefix of two open scopes would give a
    name Lean does not know.  The check that catches that is not here -- it is
    that every rostered name must be a constant Lean can `#check`, which the
    W-25 track A block records as one kernel build over all 154 rows."""
    m = NAMESPACE.match(line)
    if m:
        stack.append(("ns", m.group(1)))
        return
    if SECTION.match(line):
        stack.append(("sec", SECTION.match(line).group(1)))
        return
    if line.rstrip() == "mutual":
        # `mutual ... end` is a scope too, and MISSING IT WAS NOT SILENT: the
        # bare `end` that closes one popped `namespace Tm` instead, and 153 of
        # the library's definitions came back with no namespace at all.  That is
        # the shape of the whole gap -- a key that is not the name Lean knows.
        stack.append(("sec", None))
        return
    m = END.match(line)
    if not m:
        return
    want = m.group(1)
    if want is None:
        if stack:
            stack.pop()
        return
    for i in range(len(stack) - 1, -1, -1):
        if stack[i][1] == want:
            del stack[i:]
            return
    if stack:
        stack.pop()


def qualify(stack, name):
    """`Tm.EmitWire.u32Within` from the open namespaces and the declared name."""
    parts = [n for kind, n in stack if kind == "ns" and n]
    return ".".join(parts + [name]) if parts else name


def declarations(text, path):
    """Every `def`, `abbrev` and `instance` in one file: name, body, span, type.

    `name` is the QUALIFIED name -- the roster's key since W-25 track A."""
    out = []
    lines = text.split("\n")
    starts = []
    stack = []
    # `/- ... -/` nests in Lean, and a doc comment's continuation lines are
    # indented: without this tracker a commented-out `def` would be reported
    # UNPARSED and would fail the gate for a sentence.
    comment = 0
    for n, line in enumerate(lines):
        m = HEAD.match(line) if comment == 0 else None
        # **PROSE IS NOT A DECLARATION** here either (README gap 1308 closed the
        # same hole in `decl_spans` and left this one open, because `def` and
        # `abbrev` do not start English sentences and `instance` does -- eleven
        # phantom spans were measured from exactly that word).  The tracker
        # below already ran for `INDENTED`; it now runs for `HEAD` too.
        if m:
            starts.append((n, qualify(stack, m.group(2)), m.group(2)))
        elif comment == 0 and ANON_INSTANCE.match(line):
            nm = anon_instance_name(line)
            starts.append((n, qualify(stack, nm), nm))
        elif comment == 0 and INDENTED.match(line):
            out.append({"name": qualify(stack, INDENTED.match(line).group(2)),
                        "file": path,
                        "line": n + 1, "last": n + 1, "body": None,
                        "type": None, "at": None, "stop": None, "lead": "",
                        "indented": True})
        elif comment == 0:
            scope_step(stack, line)
        comment += line.count("/-") - line.count("-/")
        comment = max(comment, 0)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line) + 1)
    for n, name, raw in starts:
        end = len(lines)
        for j in range(n + 1, len(lines)):
            line = lines[j]
            if starts_declaration(line) and not line.startswith(BODY_KW):
                end = j
                break
        head_at = offsets[n]
        stop = offsets[end] - 1 if end < len(lines) else len(text)
        body_at, kind, header = split_header(text, head_at)
        lead = ""
        if body_at is not None and body_at < 0:
            body_at, lead = -body_at, ":= "
        if body_at is None or body_at > stop:
            out.append({"name": name, "raw": raw, "file": path, "line": n + 1,
                        "last": end, "body": None, "type": None,
                        "at": None, "stop": stop, "lead": "", "header": header})
            continue
        out.append({"name": name, "raw": raw, "file": path, "line": n + 1,
                    "last": end,
                    "body": text[body_at:stop], "type": kind.strip(),
                    "at": body_at, "stop": stop, "lead": lead,
                    "header": header})
    return out


def digest(body):
    return hashlib.sha1(" ".join(body.split()).encode("utf-8")).hexdigest()[:12]


SHADOWED = []


def roster():
    """(baseline sha, {(file, name): row}) from mutations.txt.

    A KEY WRITTEN TWICE IS RECORDED IN `SHADOWED`, not silently dropped.  This
    dict is keyed on (path, name), so a definition RE-AUDITED after its body
    changed -- the file is append-only, so the second audit appends a second row
    -- shadows its own earlier row, and the file then holds more physical rows
    than keys.  At the W-21 repair step it held 79 rows over 77 keys
    (`Planner.dayRows` and `Planner.dayDiagnostics` twice each, from W-20's land
    step and W-21 track P) while `mutations.txt`'s header documented only
    `posLt`/`victimLt` as intentional re-audits, so a hand count of the
    exemption -- `awk '$4 ~ /unfoldable/'` -- gave 29 where the gate printed 28.
    The gate's number was the right one; the file's own argument for the
    exemption is that it "can be counted and cannot grow unnoticed", and a count
    that two readers do differently is not that.  The success line now prints
    both, so the two can be reconciled without reading the file."""
    del SHADOWED[:]
    base, rows = None, {}
    if not os.path.exists(ROSTER):
        return None, {}
    for line in read(ROSTER).split("\n"):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        parts = line.split(None, 1)
        if parts[0] == "baseline":
            base = parts[1].strip()
            continue
        fields = line.split(None, 4)
        if len(fields) < 4:
            print("mutate.py: bad roster line: %s" % line)
            return None, None
        sha, path, name, consts = fields[0], fields[1], fields[2], fields[3]
        if (path, name) in rows:
            SHADOWED.append("%s %s" % (path, name))
        rows[(path, name)] = {"sha": sha, "consts": consts,
                              "why": fields[4] if len(fields) > 4 else ""}
    return base, rows


def at_commit(sha, path):
    got = subprocess.run(["git", "show", "%s:kernel/%s" % (sha, path)],
                         cwd=ROOT, capture_output=True, text=True)
    return got.stdout if got.returncode == 0 else None


def touched(base):
    """Library files whose BYTES differ from `base` -- git, two calls.

    A file identical to the baseline cannot hold a new or changed definition,
    and at a settled tree that is all of them, which is what keeps check 9 at
    ~0.05 s instead of one `git show` per module.

    THE SECOND CALL IS UNTRACKED FILES, and it is not optional.  `git diff
    --name-only <commit>` NEVER lists a file that has not been `git add`ed, and
    AGENTS acceptance runs check.sh BEFORE the commit -- so without this every
    definition in a step's brand-new module was exempt at exactly the moment
    the gate exists to bite, while `citations.py`, written in the same run,
    globs the filesystem and saw the same file.  Two checkers disagreeing about
    whether a file exists is the shape of a gate going quietly useless."""
    files, tracked = set(), set()
    for argv, into in ((["git", "diff", "--name-only", base,
                         "--", "kernel/TmKernel/TmKernel"], files),
                       (["git", "ls-files", "--others", "--exclude-standard",
                         "--", "kernel/TmKernel/TmKernel"], files),
                       (["git", "ls-files", "--",
                         "kernel/TmKernel/TmKernel"], tracked)):
        got = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
        if got.returncode != 0:
            raise SystemExit("mutate.py: %s failed: %s"
                             % (" ".join(argv[:3]), got.stderr.strip()))
        into |= {line[len("kernel/"):] for line in got.stdout.split("\n")
                 if line.endswith(".lean")}
    # **THE THIRD CALL IS THE W-22 REPAIR STEP'S, and it is the same failure one
    # layer down.**  `--exclude-standard` asks git's IGNORE RULES, and this
    # repository's `.gitignore` line 2 is `**/target` -- so a library module at
    # `kernel/TmKernel/TmKernel/target/Probe.lean` is not "other", it is
    # IGNORED, and the second call above does not list it.  With `lib_files()`
    # repaired to walk it, `--gate` STILL printed "0 owed" on a `def
    # w22TargetGatherable : Bool := true` sitting on disk -- D40's exact class,
    # green.  So the file list and the git list are RECONCILED rather than
    # trusted: a `.lean` file the walk finds and git does not TRACK is new,
    # whatever git's ignore rules think of it.  That also subsumes the second
    # call; it is kept because it is the cheap answer for the ordinary
    # not-yet-added module and because losing it would make this reconciliation
    # the only thing standing between an untracked module and the gate.
    files |= {path for path in lib_files() if path not in tracked}
    return files


def new_or_changed(base):
    """Library defs that do not exist at `base`, or whose body differs there."""
    out = []
    moved = touched(base)
    for path in lib_files():
        if path not in moved:
            continue
        now = read(os.path.join(HERE, path))
        was = at_commit(base, path)   # None for a file the baseline lacks
        # A multiset, not a dict: one file may declare the same SHORT name in
        # two namespaces (`Replay.HMap.get` and `Replay.KMap.get` are both
        # spelled `get`), and keying by name alone reported four such pairs as
        # changed when nothing had changed.
        old = collections.Counter()
        if was is not None:
            for d in declarations(was, path):
                if d["body"] is not None:
                    old[(d["name"], digest(d["body"]))] += 1
        for d in declarations(now, path):
            d["sha"] = digest(d["body"]) if d["body"] is not None else None
            if d["sha"] is not None and old[(d["name"], d["sha"])] > 0:
                old[(d["name"], d["sha"])] -= 1
                continue
            out.append(d)
    return out


def build():
    got = subprocess.run([LAKE, "build", "TmKernel:static"], cwd=PKG,
                         capture_output=True, text=True,
                         env=dict(os.environ, LEAN_NUM_THREADS="4"))
    return got.returncode, (got.stdout or "") + (got.stderr or "")


# lake v4.33.1 prints `error: TmKernel/PlannerWit.lean:3167:26: Type mismatch`
# -- the word `error` comes FIRST, before the location.  A regex written the
# other way round (location, then `error`) matches NOTHING, which is how the
# first version of this file reported every failing build as PINNED with "no
# located error" and could never have raised INVALID at all.  Both orders are
# accepted so that a `lean` invocation's own format works too.
ERR = re.compile(r"^(?:error: )?(?:\./)?(\S+\.lean):(\d+):\d+:(?: error)?", re.M)

# The one error that is NOT the definition's fault and NOT a free PINNED: the
# constant `default` does not exist, because the return type has no `Inhabited`
# instance.  AGENTS 5.1 is why -- the kernel's types are `Bool` + `Subtype`, and
# a bounded type has NO inhabitant you can name without a proof, deliberately.
# `deriving instance Inhabited` does not rescue it either: it was tried at the
# W-20 land step on `Look.Slot`, `Planner.Placed`, `Planner.Diagnostics` and
# `Planner.PlanReq` and Lean answered "failed to generate `Inhabited` instance"
# for all four.  See UNFOLDABLE in the verdict table above.
INHAB = re.compile(r"failed to synthesize[^\n]*\n\s*Inhabited ([^\n]+)")


SIDECAR = os.path.join(HERE, ".mutate-in-flight")
LOCK = os.path.join(HERE, ".mutate-lock")


def take_the_tree(argv):
    """Hold the SHARED WORKING TREE for this run, exclusively.

    **THIS GATE MUTATES THE TREE EVERY OTHER PROCESS IS READING** (W-29 repair
    step, README gap 2011).  `restore_in_flight` and `arm_signals` closed gap
    1788's KILL case; neither is about CONCURRENCY, and there was no lock.
    OBSERVED LIVE by an auditor at 01:50 in the shared checkout: `git status`
    showed ` M kernel/TmKernel/TmKernel/Boundary.lean` with a constant-folded
    `readState` planted, while `ps` showed `python3 mutate.py --gate` beside a
    `lean Boundary.lean` whose parent chain was `lake build TmKernel:static` <-
    `cargo test -p tm --test planner_invariants` -- another session's acceptance
    run compiling the mutated source.  Its `0 failed` was not a fact about HEAD
    and nothing said so.

    The lock is `flock` on a file of this directory, held for the whole run and
    released by the kernel when the process dies however it dies -- so a KILLED
    run leaves no stale lock, which a pid file would.  A second mutate run is
    refused BY NAME with the pid that holds the tree.

    The other half of the class -- an acceptance run started by a DIFFERENT tool
    while a mutation is live -- is answered where it can be seen:
    `tm/tests/mutation_in_flight.rs` fails when the sidecar exists, so a
    `cargo test --workspace` that overlaps this gate reports a FAILURE instead of
    a `0 failed` about a kernel nobody committed."""
    import fcntl

    handle = open(LOCK, "w", encoding="utf-8")
    try:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        print("mutate.py: another mutate run holds %s -- this gate mutates the "
              "SHARED working tree and two of them would interleave plants. "
              "Wait for it, or run in a clone." % os.path.relpath(HERE))
        return None
    handle.write("%d %s\n" % (os.getpid(), " ".join(argv)))
    handle.flush()
    return handle


def restore_in_flight():
    """Put back a file a KILLED run left mutated.

    `mutate_one` restores in a `finally`, which covers an exception but not a
    SIGKILL -- and a mutated library file left in the tree is the one outcome
    this gate must never produce, because it is a constant-folded kernel that
    looks like a commit.  So the original bytes go to a sidecar BEFORE the file
    is written, and every run starts by putting back whatever it finds."""
    if not os.path.exists(SIDECAR):
        return
    with open(SIDECAR, encoding="utf-8") as handle:
        rel, text = handle.read().split("\n", 1)
    with open(os.path.join(HERE, rel), "w", encoding="utf-8") as handle:
        handle.write(text)
    os.remove(SIDECAR)
    print("mutate.py: restored %s from a killed run" % rel, flush=True)


def arm_signals():
    """Restore on a SIGNAL, not only on an exception (README gap 1788).

    `mutate_one`'s `finally` covers an exception; it does not cover a signal
    that terminates the process, and DRIVEN by an independent auditor at W-28 a
    killed `--gate` run left a library definition with the body `0` in the tree.
    The sidecar made that RECOVERABLE -- the next run puts it back -- but the
    window between the kill and that run is a window in which a constant-folded
    kernel looks like a commit, and `check.sh` now FAILS on the sidecar rather
    than repairing it quietly.

    The three signals a kill actually sends are handled here: SIGTERM (what
    `kill` sends by default), SIGINT (Ctrl-C) and SIGHUP (a closed terminal).
    Each restores and then re-raises with the default disposition, so the exit
    status still says the process was killed.  SIGKILL cannot be handled by
    anything, which is why the sidecar and `check.sh`'s test both stay."""
    import signal

    def handler(signum, _frame):
        try:
            restore_in_flight()
        finally:
            signal.signal(signum, signal.SIG_DFL)
            os.kill(os.getpid(), signum)

    for name in ("SIGTERM", "SIGINT", "SIGHUP"):
        sig = getattr(signal, name, None)
        if sig is not None:
            signal.signal(sig, handler)


# ---------------------------------------------------------------------------
# WHERE THE BUILD BROKE, AS A NAME (README gap 1190, the W-22 repair step).
#
# The roster's fifth column used to be `Emit.lean:373` -- a LINE NUMBER, which
# is the one kind of citation this campaign has already learned rots.  Measured
# at W-22 by an independent auditor: 25 of 25 track-P rows re-ran at a different
# line from the one committed, systematically (+1 in `Emit.lean`, +6 and +9 in
# `PlannerWit.lean`), because the step edited doc comments and inserted a
# witness row AFTER its mutation sweep.  The verdicts were all still PINNED --
# no soundness was lost -- and the column's whole purpose, being the one
# human-readable evidence that a mutation was watched to fail, was.
#
# So the site is recorded as `<file>:<line> <declaration>`: the line for the
# person reading the build output, and the DECLARATION THE ERROR FELL INSIDE,
# which does not move when a doc comment above it does.  That is gap 1190's own
# item 4, and it is what makes a build-free staleness check possible -- see
# `stale_sites`, which `--gate` runs on every check.sh run at no cost.
#
# The scan is deliberately its own and not `declarations()`: that one finds the
# `def`s and `abbrev`s this file MUTATES, and a pin site is almost always a
# THEOREM, which it does not return.
DECL_START = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)*"
    r"(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+|partial[ \t]+"
    r"|unsafe[ \t]+|scoped[ \t]+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|example"
    r"|opaque|axiom)[ \t]+([^\s(){}\[\]:]+)")

_SPANS = {}


def decl_spans(text):
    """[(first line, name)] for every column-zero declaration, doc comment first.

    The doc comment is INSIDE the span because that is where Lean reports the
    error for a failed declaration: `Emit.lean:374` is the `/--` line of
    `cells_are_the_nine_in_order`, not its `theorem` line.

    **PROSE IS NOT A DECLARATION** (README gap 1308).  `DECL_START` is anchored
    at column zero and a doc comment's own continuation lines are flush left, so
    a sentence beginning with `instance`, `class`, `structure` or `example`
    registered a phantom declaration named after the NEXT WORD -- `at`, `is`,
    `the`, `of`, `takes` -- which then SHADOWED the real theorem the site
    belonged to, because `site()` takes the last span at or before the line.
    Measured over the library before the repair: 8,103 spans, **11 phantom**,
    and `kernel/mutations.txt` carried one of them (`PlannerWit.lean:3641 at`,
    from the prose *"instance at the slot's own start ..."*), which check 9
    counted as a NAMED pin site -- the gate green on exactly the class gap 1196
    exists to close.

    The tracker is `declarations()`'s own, lines 511-514, and so is its blind
    spot: `/-` and `-/` are counted as bytes, so a `/-` inside a string literal
    or a `--` line comment would open a span that never closes.  The library
    holds none; `stale_sites` is what would notice, because every site in
    `mutations.txt` after such a line would stop resolving."""
    lines = text.split("\n")
    depth, inside = 0, []
    for line in lines:
        inside.append(depth)
        depth += line.count("/-") - line.count("-/")
        depth = max(depth, 0)
    out = []
    for i, line in enumerate(lines, 1):
        if inside[i - 1] > 0:
            continue
        m = DECL_START.match(line)
        if not m:
            continue
        start = i
        # Walk back over the doc comment that belongs to this declaration.
        j = i - 2
        if j >= 0 and lines[j].rstrip().endswith("-/"):
            while j >= 0:
                if lines[j].lstrip().startswith("/--") or lines[j].lstrip().startswith("/-!"):
                    start = j + 1
                    break
                j -= 1
        out.append((start, m.group(1)))
    return sorted(out)


def site(where, line):
    """`<file>:<line> <declaration>` for an error at `where:line`."""
    base = os.path.basename(where)
    if base not in _SPANS:
        path = next((p for p in lib_files() if os.path.basename(p) == base), None)
        _SPANS[base] = (decl_spans(read(os.path.join(HERE, path)))
                        if path else [])
    name = None
    for start, decl in _SPANS[base]:
        if start <= line:
            name = decl
        else:
            break
    return "%s:%d%s" % (base, line, (" " + name) if name else "")


# A pin site that carries its declaration: `Emit.lean:374
# cells_are_the_nine_in_order`.  The name is what this can check without a
# build; the number is what a reader needs to find the line.
NAMED_SITE = re.compile(
    r"\b([A-Za-z][A-Za-z0-9_]*\.lean):(\d+)[ \t]+([A-Za-z_][A-Za-z0-9_.']*)")
BARE_SITE = re.compile(r"\b[A-Za-z][A-Za-z0-9_]*\.lean:\d+")


def stale_sites(rows):
    """(stale, un-upgraded) over the roster's fifth column.  NO BUILD.

    README gap 1190: the column records where the build first errored, and
    nothing re-checked it, so 25 of 25 track-P rows re-ran at a different line
    from the one committed and `check.sh` was 9/9 throughout.  A row whose site
    carries a DECLARATION NAME can be checked for free -- the name must still be
    the one that encloses that line -- and that check runs on every gate run.

    THE SECOND NUMBER IS THE HONEST HALF.  A row whose site is a bare
    `file:line` cannot be checked at all and is COUNTED rather than passed over
    in silence, which is check 8's allow-list discipline: an exemption nobody
    counts is how a gate goes quietly useless.  Those rows are upgraded by
    `mutate.py --verify --write`, which costs one kernel build per constant, so
    the count falls as steps re-verify their own files and not before."""
    stale, unnamed = [], 0
    for (path, name), row in sorted(rows.items()):
        why = row.get("why", "")
        hits = NAMED_SITE.findall(why)
        if not hits:
            unnamed += 1 if BARE_SITE.search(why) else 0
            continue
        for base, line, decl in hits:
            want = "%s:%s %s" % (base, line, decl)
            got = site(base, int(line))
            if got != want:
                stale.append("%s %s: roster says `%s`, %s:%s is now in `%s`"
                             % (path, name, want, base, line,
                                got.split(" ", 1)[-1] if " " in got else "no declaration"))
    return stale, unnamed


def mutate_one(decl, const, synthesised=False):
    """Apply one constant, build, restore.  -> (verdict, first error line).

    `synthesised` marks a constant this file BUILT out of the type's own text --
    `extra_constant`'s named nullary or structure literal.  An error inside the
    mutated declaration is then UNAVAILABLE, not INVALID: what failed to
    elaborate is the checker's guess at a term, not the definition, and failing
    the gate on it would make a correct definition unshippable because
    `type_constant` read a field type wrong.  It is NOT a free PINNED -- it is
    reported by name, counted on the "pinned by nothing" line, and the row
    records `unavailable`, so the exemption is visible exactly the way
    `unfoldable` is."""
    full = os.path.join(HERE, decl["file"])
    text = read(full)
    span = text[decl["at"]:decl["stop"]]
    new = " " + decl.get("lead", "") + const + "\n" * span.count("\n")
    with open(SIDECAR, "w", encoding="utf-8") as handle:
        handle.write(decl["file"] + "\n" + text)
    with open(full, "w", encoding="utf-8") as handle:
        handle.write(text[:decl["at"]] + new + text[decl["stop"]:])
    try:
        code, out = build()
    finally:
        with open(full, "w", encoding="utf-8") as handle:
            handle.write(text)
        os.remove(SIDECAR)
    if code == 0:
        return "SURVIVED", "build completed"
    first = None
    hits = list(ERR.finditer(out))
    for idx, m in enumerate(hits):
        where, line = m.group(1), int(m.group(2))
        if first is None:
            first = site(where, line)
        if os.path.basename(where) == os.path.basename(decl["file"]) \
           and decl["line"] <= line <= decl["last"]:
            stop = hits[idx + 1].start() if idx + 1 < len(hits) else len(out)
            want = INHAB.search(out[m.end():stop])
            if want:
                return "UNFOLDABLE", "no Inhabited %s" % want.group(1).strip()
            if synthesised:
                return "UNAVAILABLE", "%s -- the synthesised constant does " \
                    "not elaborate here" % site(where, line)
            return "INVALID", "%s is inside the declaration" % site(where, line)
    return "PINNED", first or "build failed with no located error"


_SYNONYMS = {}


def synonyms():
    """Short name -> body text, for every library `abbrev` that names a TYPE.

    Read once per run from the same files `lib_files` mutates.  Keyed on the
    last dotted segment, which is how a declared type is usually spelled at the
    use site (`PlanCheck.Eligible` and `Eligible` are the same abbrev)."""
    if not _SYNONYMS:
        for path in lib_files():
            for m in ABBREV.finditer(read(os.path.join(HERE, path))):
                _SYNONYMS.setdefault(m.group(1).split(".")[-1], m.group(2).strip())
    return _SYNONYMS


def arrow_parts(text):
    """Split a type on its DEPTH-ZERO arrows: `A -> (B -> C) -> D` is three."""
    depth, parts, cur, i = 0, [], "", 0
    while i < len(text):
        c = text[i]
        if c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            depth -= 1
        if depth == 0 and (c == "→" or text.startswith("->", i)):
            parts.append(cur)
            cur = ""
            i += 2 if c == "-" else 1
            continue
        cur += c
        i += 1
    parts.append(cur)
    return [p.strip() for p in parts]


def resolve_type(text):
    """Unfold a declared type through library `abbrev`s, up to three levels."""
    seen = set()
    for _ in range(3):
        text = text.strip()
        last = text.split(".")[-1]
        if not IDENT.match(text) or last in seen or last not in synonyms():
            break
        seen.add(last)
        text = synonyms()[last]
    return text.strip()


# A `structure T where` and the types of its fields, for `type_constant`.
STRUCT = re.compile(r"^structure[ \t]+([A-Za-z_][A-Za-z0-9_.']*)")
FIELD = re.compile(r"^[ \t]+([A-Za-z_][A-Za-z0-9_']*)[ \t]*:[ \t]*([^\n]+?)[ \t]*$")

# The last segment of a name this kernel spells as the canonical empty of its
# type.  See `nullary_constants`: any other nullary constant is another FIXTURE,
# and swapping fixtures is a different experiment (gap 1088).
EMPTIES = {"empty", "nil", "none", "zero"}

_NULLARY = {}
_FIELDS = {}


def nullary_constants():
    """(file, resolved type) -> a NAMED closed term of that type, per file.

    A `def n : T := …` with NO binders is a constant of `T` that this kernel
    itself declares -- `Diagnostics.empty` is one, at Planner.lean:398 -- and it
    is a constant of a type that has no `Inhabited` instance, which is exactly
    where `default` is not available.  README gap 1035 said of
    `PlanReq.deferFold`, `PlanReq.finalAssign` and `dayDiagnostics` that
    "nothing below the gate says any theorem reads those three"; W-21's audit
    refuted that by hand, folding `dayDiagnostics` to `Diagnostics.empty` and
    watching PlannerWit.lean fail in three places.  This is that mutation, made
    the gate's.

    KEYED BY FILE, and that is not an optimisation: the mutation is applied in
    place, so the constant has to resolve in the mutated declaration's own
    namespace context, and a name declared in another module may need a prefix
    this file cannot compute.  Same file is the case it can be sure of."""
    if not _NULLARY:
        for path in lib_files():
            for d in declarations(read(os.path.join(HERE, path)), path):
                if d["body"] is None or d["type"] is None:
                    continue
                # `header` is the whole text in FRONT of the depth-zero `:`
                # -- the keyword and the name included -- so the binders are
                # what is left after `HEAD` has eaten those two.
                head = HEAD.match(d.get("header") or "")
                if head is None or (d["header"][head.end():]).strip():
                    continue          # it has binders; not a constant
                if d["name"].split(".")[-1] not in EMPTIES:
                    continue
                _NULLARY.setdefault((path, resolve_type(d["type"].strip())),
                                    d["name"])
    return _NULLARY


def struct_fields():
    """Short structure name -> the declared types of its fields, in order."""
    if not _FIELDS:
        for path in lib_files():
            name, fields, depth = None, [], 0
            for line in read(os.path.join(HERE, path)).split("\n"):
                depth += line.count("/-") - line.count("-/")
                if depth > 0 or line.lstrip().startswith("--"):
                    continue
                head = STRUCT.match(line)
                if head:
                    if name:
                        _FIELDS.setdefault(name.split(".")[-1], fields)
                    name, fields = head.group(1), []
                    continue
                if name is None:
                    continue
                if line[:1] not in ("", " ", "\t"):
                    _FIELDS.setdefault(name.split(".")[-1], fields)
                    name, fields = None, []
                    continue
                got = FIELD.match(line)
                if got and "--" not in got.group(2):
                    fields.append(got.group(2).strip())
            if name:
                _FIELDS.setdefault(name.split(".")[-1], fields)
    return _FIELDS


def type_constant(text, path, depth=0):
    """A closed term of type `text` that is NOT `default`, or None.

    `default` is a constant of every INHABITED type and of no other, and half of
    this kernel's types deliberately have no `Inhabited` instance (AGENTS 5.1).
    These are the constants that exist anyway, in the order they are tried:

        List _        []                  Option _      none
        A × B         (cA, cB)            Nat/Bool/Prop 0 / true / True
        a nullary `def T.empty : T` in the SAME FILE      T.empty
        a `structure T` whose every field has one         ⟨c1, …, cn⟩

    THE NAMED ONE IS SPELLED `.empty`/`.nil`/`.none`/`.zero`, AND THAT IS NOT A
    CONVENIENCE.  Any nullary `def n : T` is a constant of `T`, but most of them
    are OTHER FIXTURES -- `theCrowdedRequest := theRequest`, `routinePlan :=
    recurPlan` -- and swapping one witness fixture for another is a DIFFERENT
    experiment from folding a definition to a constant: it asks whether two
    populations are distinguishable, not whether a body is degenerate.  Measured
    at the W-21 repair step: taking every nullary constant reached 21 of the 23
    "pinned by nothing" rows, 15 of them by a fixture swap, and one of those 15
    would have replaced a definition's body with ITS OWN NAME.  The canonical
    empty is the one that is a constant fold in D40's sense.  The fixture swap
    is README gap 1088, with the shape it would have to take.

    The last two are the W-21 repair step's, and the structure literal is
    OFFERED ONLY WHEN EVERY FIELD RESOLVES: `Planner.Assign`'s three fields are
    `List (Option Nat)`, `List Group` and `Nat`, so `⟨[], [], 0⟩` elaborates,
    while `Planner.Diagnostics` has `Capped _` fields -- a type built by a
    function, which nothing here can name a value of -- so no literal is offered
    for it and its own `Diagnostics.empty` is what reaches it.  A type whose
    fields this cannot name is NOT given a half-built literal.

    EVERY TERM THIS RETURNS IS SYNTHESISED BY A TEXTUAL RULE, so it may fail to
    elaborate where a hand-written one would not; see the UNAVAILABLE verdict,
    which is why that is not a gate failure."""
    if depth > 3:
        return None
    text = resolve_type(text.strip())
    while text.startswith("(") and text.endswith(")") and \
            arrow_parts(text[1:-1]) and len(product_parts(text[1:-1])) >= 1 and \
            text[1:-1].count("(") == text[1:-1].count(")"):
        text = text[1:-1].strip()
    if not text or "∀" in text or "," in text or len(arrow_parts(text)) > 1:
        return None
    if text in CONSTANTS:
        return CONSTANTS[text][0]
    parts = product_parts(text)
    if len(parts) > 1:
        picks = [type_constant(part, path, depth + 1) for part in parts]
        return None if any(c is None for c in picks) else "(%s)" % ", ".join(picks)
    head = text.split()[0]
    if head == "List":
        return "[]"
    if head == "Option":
        return "none"
    named = nullary_constants().get((path, text))
    if named is not None:
        return named

    fields = struct_fields().get(text.split(".")[-1])
    if fields:
        picks = [type_constant(f, path, depth + 1) for f in fields]
        if not any(c is None for c in picks):
            return "⟨%s⟩" % ", ".join(picks)
    return None


def extra_constant(decl):
    """`type_constant` of the RESULT type, under the declaration's binders.

    Beside `constants_for` and `identity_for`, never instead of them, and never
    a duplicate of what those already try."""
    kind = resolve_type((decl.get("type") or "").strip())
    if "∀" in kind or not kind:
        return None
    parts = arrow_parts(kind)
    const = type_constant(parts[-1], decl["file"])
    if const is None or const in CONSTANTS.get(parts[-1], []):
        return None
    if len(parts) == 1:
        return const
    return "fun " + "_ " * (len(parts) - 1) + "=> " + const


def literal_body(decl):
    """The body if it IS a constant -- `true`, `7`, `fun _ => true` -- else None.

    A definition whose body is a bare literal is not DISTINGUISHABLE from a
    constant of its type by anything, ever: it is one.  `Planner.Ranked
    .gatherable := true` -- the W-19 defect D40 was written for -- is this
    shape, and so is every wire bound (`maxCands : Nat := 1024`, 66 of them in
    the library today).  The gate cannot tell those two apart, so this is a
    REPORTED verdict and not a fatal one; see LITERAL in the header.  A record
    or structure literal body (`{ a := 1, b := 2 }`) is also a constant and is
    NOT matched here -- that is the witness-fixture shape, where a literal body
    is what the definition is for."""
    body = " ".join((decl["body"] or "").split())
    m = LITERAL.match(body)
    return m.group(0) if m else None


def constants_for(decl):
    """The constants to fold this definition to, by its DECLARED type.

    Resolved through `abbrev` synonyms and through the type's depth-zero
    arrows, so that a `Bool` spelled `Nat -> Bool`, or spelled `Eligible`, gets
    `fun _ => true` and `fun _ => false` rather than `default` alone.  Keying
    on the type's literal TEXT was W-20's blocker: `default : Nat -> Bool` is
    `fun _ => false`, so only the `false` direction was ever tried for an
    arrow-spelled `Bool`, and AGENTS 5.8 asks for both.  99 library
    definitions are arrow-spelled to a scalar and 19 more reach one through an
    `abbrev`.

    A type carrying a depth-zero `forall` or `,` is left on `default`: its
    binders are not all anonymous and `fun _ => c` may not elaborate, and an
    error inside the declaration is INVALID, which fails the gate."""
    text = resolve_type((decl["type"] or "").strip())
    if "∀" in text or "," in arrow_parts(text)[0]:
        return ["default"]
    parts = arrow_parts(text)
    consts = CONSTANTS.get(parts[-1])
    if consts is None:
        return ["default"]
    if len(parts) == 1:
        return list(consts)
    binders = "fun " + "_ " * (len(parts) - 1) + "=> "
    return [binders + c for c in consts]


BINDER = re.compile(r"\(([^():]+?):([^()]*(?:\([^()]*\)[^()]*)*)\)")


def binders(decl):
    """The EXPLICIT named binders of a header: [(name, type text), ...].

    `def f (r : PlanReq) (budget : Nat) (a : Assign)` gives three. Implicit
    (`{}`), instance (`[]`) and strict-implicit (`⦃⦄`) binders are skipped:
    a mutation that names one would be writing a term the elaborator was
    going to supply, which is a different experiment.

    The header is the text from just after the declaration's name to the
    depth-zero `:` that opens its type; `split_header` has already found that
    colon, so this re-walks only what is in front of it."""
    text = decl.get("header") or ""
    out = []
    for m in BINDER.finditer(text):
        kind = m.group(2).strip()
        for name in m.group(1).split():
            if IDENT.match(name):
                out.append((name, kind))
    return out


def product_parts(text):
    """Split a type on its DEPTH-ZERO `×`: `Placed × Assign` is two."""
    depth, parts, cur, i = 0, [], "", 0
    while i < len(text):
        c = text[i]
        if c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            depth -= 1
        if depth == 0 and c == "×":
            parts.append(cur)
            cur = ""
            i += 1
            continue
        cur += c
        i += 1
    parts.append(cur)
    return [p.strip() for p in parts]


def identity_for(decl):
    """**The identity on the accumulator** (README gap 985), or `None`.

    D40's constant fold does not exist for a definition whose result type has
    no `Inhabited` instance, and at the W-20 land step that was HALF of what
    the step added -- 23 of 46, EIGHT of them step 6's own algorithm. The
    kernel's types are `Bool` + `Subtype` and a bounded type deliberately has
    no inhabitant anybody can name without a proof (AGENTS 5.1), so the answer
    is not to hand out instances; it is a degenerate body that EXISTS for an
    uninhabited type.

    For a function whose result type appears among its own argument types, that
    body is the argument itself:

        PlanReq.rePlaceWalk : ... -> Assign -> List ... -> Assign
            |->  fun a0 _ => a0
        PlanReq.deferWalk : ... -> List Placed -> Assign -> List Placed
                                     -> List Placed × Assign
            |->  fun a0 a1 _ => (a0, a1)
        placeAt (q : Placed) (t : Nat) : Placed
            |->  q
        PlanReq.deferOne (...) (a : Assign) (q : Placed) : Placed × Assign
            |->  (q, a)

    **This is the shape the walk-and-fold bug class actually takes.** A fold
    that forgets to fold -- that returns its accumulator unchanged on the
    branch that should have changed it -- is not a constant and no constant
    catches it; it is exactly this term. It is a mutation the type system
    accepts where `default` does not, so it reaches definitions the constants
    cannot.

    HOW A SOURCE IS FOUND, and the two places it gives up:

      * the result type is split on its depth-zero `×`, so a fold returning a
        pair is served when BOTH halves are available;
      * a component is matched, by **exact type text** after `abbrev`
        resolution, first against the explicit named binders of the header and
        then against the anonymous binders of the declared type's depth-zero
        arrows;
      * if any component has no source, there is no identity and this returns
        `None` -- `PlanReq.deferFold : List Placed × Assign` takes only a
        `PlanReq`, so nothing here reaches it.

    The match is TEXTUAL, like everything else in this file: `Assign` and a
    definitionally-equal spelling of `Assign` are two different strings here,
    and the one this cannot see is a component whose source is spelled
    differently from the result. That is a miss, never a false PINNED -- an
    identity that does not elaborate is INVALID, which FAILS the gate."""
    kind = resolve_type((decl.get("type") or "").strip())
    if "∀" in kind or not kind:
        return None
    parts = arrow_parts(kind)
    if "," in parts[0] and len(parts) == 1:
        return None
    wants = product_parts(parts[-1])
    named = {t: n for n, t in reversed(binders(decl))}
    anon = parts[:-1]
    used, picks = set(), []
    for want in wants:
        if want in named:
            picks.append(named[want])
            continue
        where = next((i for i, t in enumerate(anon) if t == want), None)
        if where is None:
            return None
        used.add(where)
        picks.append("a%d" % where)
    if not picks:
        return None
    body = picks[0] if len(picks) == 1 else "(%s)" % ", ".join(picks)
    if not anon:
        return body
    lam = " ".join("a%d" % i if i in used else "_" for i in range(len(anon)))
    return "fun %s => %s" % (lam, body)


def write_rows(rows):
    """Append each row -- or REPLACE the row that already holds its key.

    `--write` used to append unconditionally, so a definition RE-AUDITED after
    its body changed left its stale row in the file, shadowed by `roster()`'s
    dict.  Measured at the W-21 repair step: 79 physical rows over 77 keys, and
    a hand count of the exemption that disagreed with the gate's by one.  A row
    is a claim about a (file, name) at a body sha; two claims about one key is
    one claim too many, and the older one is the one nobody can act on."""
    text = read(ROSTER)
    lines = text.split("\n")
    keyed = {}
    for i, line in enumerate(lines):
        bare = line.split("#", 1)[0].strip()
        fields = bare.split(None, 4)
        if len(fields) >= 4 and fields[0] != "baseline":
            keyed[(fields[1], fields[2])] = i
    added, replaced = [], 0
    for row in rows:
        fields = row.split(None, 4)
        at = keyed.get((fields[1], fields[2]))
        if at is None:
            added.append(row)
        else:
            lines[at] = row
            replaced += 1
    out = "\n".join(lines)
    if added:
        if not out.endswith("\n"):
            out += "\n"
        out += "\n".join(added) + "\n"
    with open(ROSTER, "w", encoding="utf-8") as handle:
        handle.write(out)
    print("%d row(s) appended, %d replaced in mutations.txt"
          % (len(added), replaced))


def run(decls, write, verbose=True):
    """Mutate each declaration with each of its constants.

    -> (bad, soft, pinned, by, rows).  `bad` fails the gate; `soft` is the
    UNFOLDABLE roster -- named, counted and printed on every run, never silent;
    `rows` is what this run WOULD write, which is what `--verify` compares the
    committed roster against (README gap 1190)."""
    rows, bad, soft, pinned = [], [], [], set()
    # Which mutation earned the pin, per definition.  Counted rather than
    # inferred: the summary used to read "pinned by an identity" off the mere
    # PRESENCE of an UNFOLDABLE verdict beside the pin, which was true while the
    # identity was the only thing that could pin an unfoldable definition and
    # stopped being true the moment a synthesised constant could -- gap 871's
    # class, a checker's own prose misquoting the measurement beside it.
    by = collections.Counter()
    for decl in decls:
        tag = "%s:%s" % (decl["file"], decl["name"])
        if decl["body"] is None:
            why = ("indented; this file's extent rule is column-zero"
                   if decl.get("indented")
                   else "no depth-zero `:=` (equation-style?)")
            bad.append((tag, "UNPARSED", why))
            if verbose:
                print("  %-58s UNPARSED  %s" % (tag, why), flush=True)
            continue
        literal = literal_body(decl)
        if literal is not None:
            soft.append((tag, "LITERAL", "the body IS the constant `%s`" % literal))
            if verbose:
                print("  %-58s %-9s %-8s %-38s"
                      % (tag, ":= " + literal, "LITERAL",
                         "the body IS this constant"), flush=True)
        verdicts = []
        # **The identity on the accumulator, BESIDE the type's constants and
        # never instead of them** (README gap 985).  It exists for a type with
        # no `Inhabited` instance, which is exactly where `default` does not,
        # so it is the one mutation that reaches an UNFOLDABLE definition.
        ident = identity_for(decl)
        # **A named nullary constant, or a structure literal** (W-21 repair
        # step).  `default` is not the only constant a type has, and for a type
        # with no `Inhabited` instance it is not one at all: `Diagnostics.empty`
        # is a constant of `Diagnostics` this kernel declares, and `⟨[], [], 0⟩`
        # is one of `Assign`.  README gap 1035 counted all three of step 6's
        # remaining definitions as pinned by NOTHING; an auditor folded two of
        # them by hand and watched the build fail.  Beside the others, never
        # instead of them, and marked synthesised so a guess that does not
        # elaborate is UNAVAILABLE rather than a gate failure.
        extra = extra_constant(decl)
        tries = [(c, False) for c in constants_for(decl)]
        if ident:
            tries.append((ident, False))
        if extra:
            tries.append((extra, True))
        for const, synth in tries:
            if verbose:
                # BEFORE the build, flushed: one mutation is a whole kernel
                # build, and a gate with no progress output looks like a hang.
                print("  %-58s %-9s building…" % (tag, ":= " + const),
                      end="\r", flush=True)
            verdict, why = mutate_one(decl, const, synth)
            if verbose:
                print("  %-58s %-9s %-8s %-38s" % (tag, ":= " + const, verdict, why),
                      flush=True)
            verdicts.append((const, verdict, why))
            if verdict in ("UNFOLDABLE", "UNAVAILABLE"):
                soft.append((tag, verdict, ":= %s -- %s" % (const, why)))
            elif verdict != "PINNED":
                bad.append((tag, verdict, ":= %s -- %s" % (const, why)))
        if any(v == "PINNED" for _, v, _ in verdicts):
            pinned.add(tag)
            if ident and any(c == ident and v == "PINNED" for c, v, _ in verdicts):
                by["identity"] += 1
            if extra and any(c == extra and v == "PINNED" for c, v, _ in verdicts):
                by["synthesised"] += 1
        if all(v in ("PINNED", "UNFOLDABLE", "UNAVAILABLE") for _, v, _ in verdicts):
            rows.append("%s %s %s %s %s" % (
                decl["sha"], decl["file"], decl["name"],
                # WHITESPACE-FREE, because the roster is whitespace-delimited
                # and `fun _ _ => true` is one FIELD, not four.
                ",".join("".join(c.split()) if v == "PINNED" else v.lower()
                         for c, v, _ in verdicts)
                + ("" if literal is None else ",literal"),
                "; ".join(w for _, _, w in verdicts)
                + ("" if literal is None
                   else "; the body IS the constant `%s`" % literal)))
    if write and rows:
        write_rows(rows)
    return bad, soft, pinned, by, rows


FLAGS = ("--gate", "--write", "--verify", "--only", "--since")


def main(argv):
    # An unrecognised flag is REFUSED, not ignored.  A typo used to fall through
    # to the default path, which mutates every new definition -- one kernel
    # build per constant, minutes of it, for a misspelling.
    known = set(FLAGS)
    skip = False
    for i, arg in enumerate(argv):
        if skip:
            skip = False
            continue
        if arg not in known:
            print("mutate.py: unknown argument %r; flags are %s"
                  % (arg, " ".join(FLAGS)))
            return 2
        skip = arg in ("--only", "--since")
    held = take_the_tree(argv)
    if held is None:
        return 2
    restore_in_flight()
    arm_signals()
    base, rows = roster()
    if rows is None:
        return 2
    if base is None:
        print("mutate.py: mutations.txt has no `baseline <sha>` line")
        return 2
    gate = "--gate" in argv
    write = "--write" in argv
    verify = "--verify" in argv
    only = None
    if "--only" in argv:
        only = argv[argv.index("--only") + 1]
    if "--since" in argv:
        base = argv[argv.index("--since") + 1]

    if verify:
        # **`--only` NARROWS A VERIFY** (the W-22 repair step).  A full
        # re-verification is one kernel build per constant -- 114 rows and ~285
        # constants at this commit, measured at about two minutes a constant on
        # this machine, so hours -- and until now the flag an auditor reaches for
        # to ask about ONE row re-ran all of them or nothing.  It matches a
        # definition's name, its `file:name` tag, or a FILE, so "re-verify
        # `Emit.lean`" is a sentence this tool can be asked.
        decls = [d for path in lib_files()
                 for d in declarations(read(os.path.join(HERE, path)), path)
                 if (d["file"], d["name"]) in rows]
        if only:
            decls = [d for d in decls
                     if d["name"] == only
                     or "%s:%s" % (d["file"], d["name"]) == only
                     or d["file"] == only
                     or os.path.basename(d["file"]) == only]
            if not decls:
                print("mutate.py: --only %r matches no rostered definition"
                      % only)
                return 2
        for d in decls:
            d["sha"] = digest(d["body"]) if d["body"] is not None else None
        print("re-running %d rostered mutation(s)" % len(decls))
        bad, soft, _, _, fresh = run(decls, write)
        # **THE FIFTH COLUMN IS COMPARED, NOT ONLY RE-RUN** (README gap 1190).
        # `--verify` used to re-run every row and throw the result away except
        # for its verdict, so a row whose recorded pin SITE had gone stale --
        # the file and line where the build first errored -- re-verified clean.
        # Measured at the W-22 repair step: 25 of 25 track-P rows re-ran at a
        # DIFFERENT line from the one committed (+1 in `Emit.lean`, +6 and +9 in
        # `PlannerWit.lean`), because the step edited doc comments and inserted a
        # witness row after its sweep and re-ran only one row.  The land step
        # reported the class as TWO rows and blamed the merge; it is systematic
        # and the merge is not its cause.  It costs no soundness -- every verdict
        # re-derived PINNED -- and it costs the column's whole purpose, which is
        # to be the one human-readable evidence that a mutation was watched to
        # fail.  `--verify --write` rewrites the drifted rows; `--verify` alone
        # names them and FAILS, because a roster whose evidence column has rotted
        # is a roster nobody can audit by reading.
        norm = lambda t: " ".join(t.split())
        stale = []
        for row in fresh:
            got = row.split(None, 4)
            was = rows.get((got[1], got[2]), {})
            mine = (norm(got[3]), norm(got[4] if len(got) > 4 else ""))
            theirs = (norm(was.get("consts", "")), norm(was.get("why", "")))
            if mine != theirs:
                stale.append((got[1], got[2], theirs, mine))
        for path, name, theirs, mine in stale:
            print("  STALE ROW %s %s" % (path, name))
            print("    roster: %s | %s" % theirs)
            print("    actual: %s | %s" % mine)
        print("%d rostered definition(s) failed re-verification, "
              "%d unfoldable, %d row(s) whose recorded verdict or pin site "
              "had drifted%s"
              % (len(bad), len(soft), len(stale),
                 " (rewritten)" if write and stale else ""))
        return 1 if bad or (stale and not write) else 0

    decls = new_or_changed(base)
    if only:
        decls = [d for d in decls if d["name"] == only
                 or "%s:%s" % (d["file"], d["name"]) == only]
        if not decls:
            for path in lib_files():
                for d in declarations(read(os.path.join(HERE, path)), path):
                    if d["name"] == only:
                        d["sha"] = digest(d["body"]) if d["body"] else None
                        decls.append(d)
    # `d["sha"] is not None` is load-bearing: an UNPARSED declaration has no
    # sha, and an absent roster row's `.get("sha")` is None too, so without it
    # `None == None` counted every unparsable definition as ALREADY AUDITED and
    # the gate reported it rostered with 0 owed.
    rostered = [d for d in decls
                if d["sha"] is not None
                and rows.get((d["file"], d["name"]), {}).get("sha") == d["sha"]]
    owed = [d for d in decls if d not in rostered]
    # `--only NAME` means AUDIT EXACTLY THIS, whether or not a row already holds
    # it.  Without this it was a no-op on every definition already rostered --
    # which is all of them at a settled tree -- so the flag an auditor reaches
    # for could not re-run the one row they were asking about.  It is not in
    # `check.sh` and cannot change what the gate does.
    if only:
        rostered, owed = [], list(decls)

    # The UNFOLDABLE count is printed on EVERY run, owed or not: a definition the
    # fold cannot reach is an exemption, and check 8's allow-list is the precedent
    # -- an exemption nobody counts is how a gate goes quietly useless.
    # `unfold` is every row the CONSTANT fold could not reach; `mute` is the
    # ones nothing reached, the identity on an accumulator included (README gap
    # 985).  They are printed as two numbers because they are two claims: the
    # first says `default` does not typecheck, the second says no mutation of
    # this definition exists at all, and only the second is an exemption.
    consts_of = lambda d: rows.get((d["file"], d["name"]), {}).get("consts", "")
    # The constants column, minus `literal`, which is a note about the BODY and
    # not a mutation's verdict.
    col = lambda d: [c for c in consts_of(d).split(",") if c and c != "literal"]
    unfold = sum(1 for d in decls if "unfoldable" in consts_of(d))
    # PINNED BY NOTHING: no constant, no identity and no synthesised term told
    # this definition from a fold.  `unavailable` counts here beside
    # `unfoldable` -- a constant that did not elaborate pins nothing either.
    exempt_rows = [d for d in decls
                   if col(d) and all(c in ("unfoldable", "unavailable")
                                     for c in col(d))]
    fixture_rows = sum(1 for d in exempt_rows if is_witness(d["file"]))
    mute_rows = len(exempt_rows) - fixture_rows
    lit = sum(1 for d in decls if "literal" in consts_of(d))
    # The physical row count beside the key count, so that a hand count of the
    # exemption and this line cannot disagree in silence; see `roster`.
    shadow = ("" if not SHADOWED
              else ", %d row(s) superseded by a re-audit" % len(SHADOWED))
    # **The declared exemption is checked before it is trusted** (README gap
    # 1086).  `WITNESS_MODULES` buys the FIXTURE verdict on the strength of
    # one property -- nothing in the library imports those modules -- so the
    # property is asserted here, on every run, and a violation FAILS rather
    # than widening the exemption in silence.
    violations = witness_violations()
    if violations:
        print("WITNESS_MODULES is not what it claims:")
        for why in violations:
            print("  %s" % why)
        return 1

    # **THE KEY IS THE QUALIFIED NAME** (README gap 1422, CLOSED at W-25 track
    # A).  It was the SHORT name, and `roster()` reads a repeated key as a
    # deliberate RE-AUDIT -- so two DIFFERENT definitions sharing a short name
    # in one file were indistinguishable from one definition audited twice, and
    # only one of the two could ever match its row's sha.  The W-24 repair step
    # found it while adding `instance`, latched it as a STOP, and reported SIX
    # live pairs.
    #
    # **THERE ARE 38, NOT SIX**, measured over the whole library once the
    # namespace stack existed: the six named (Boundary `readTz`/`readStep`,
    # Line `setEst`/`keyOf`, Replay `get`/`alter`) plus `wf` in FIVE files
    # (Cal, Line, Lookahead, Planner, Seal), `empty`, `finish` and `name` in
    # two each, `Json.go`, `Log.tag`, `Close.bump`, `Lookahead.view` and
    # nineteen more, across TEN files rather than three.  The latch was a stop
    # for three files and silence for the other six, because the count was
    # taken over the step's own diff and written down as a fact about the
    # library.
    #
    # THE CHECK STAYS, AND ITS MEANING CHANGES.  Lean cannot hold two
    # declarations of one QUALIFIED name, so a collision here is no longer a
    # limitation of the roster -- it is `scope_step` disagreeing with Lean's
    # elaborator, which is the one way the new key can be wrong and the one
    # thing nothing else below the gate would notice.
    seen = collections.Counter((d["file"], d["name"]) for d in decls)
    clash = sorted(k for k, n in seen.items() if n > 1)
    if clash:
        print("%d QUALIFIED name(s) declared twice in one file -- Lean cannot "
              "hold that, so `scope_step` has the namespace stack wrong "
              "(README gap 1422):" % len(clash))
        for path, name in clash:
            print("  %s %s" % (path, name))
        return 1

    # **AND A ROW WHOSE DECLARATION HAS GONE IS A CLAIM ABOUT NOTHING** (the
    # W-28 repair step, README gap 1888).  `roster()` is a dict keyed on
    # (file, name), so a row whose declaration was deleted or moved to another
    # file is never consulted again: it is not re-run, not re-verified, and not
    # reported -- the same free exemption `citations.py`'s unused-allow-entry
    # ratchet closes, one gate over.  Measured when this went in: 230 rows, 3,039
    # declarations, and the only two orphans were the two duplicate emitters the
    # same step deleted.  A row is a claim that SOMETHING was watched to fail;
    # when its subject goes, the row goes with it, in the same diff.
    live = {(d["file"], d["name"]) for path in lib_files()
            for d in declarations(read(os.path.join(HERE, path)), path)}
    orphan = sorted(k for k in rows if k not in live)
    if orphan:
        print("%d roster row(s) naming a declaration this library no longer "
              "holds -- delete the row with its subject, or say which file the "
              "declaration moved to:" % len(orphan))
        for path, name in orphan:
            print("  %s %s" % (path, name))
        return 1

    # **THE RECORDED PIN SITE IS RE-RESOLVED, on every run and without a build**
    # (README gap 1190).  A row whose site names the declaration the error fell
    # inside is checked against the tree as it stands; a row whose site is still
    # a bare line number cannot be checked and is COUNTED.
    drifted, unnamed = stale_sites(rows)
    if drifted:
        print("%d roster row(s) whose recorded pin site has drifted -- "
              "`mutate.py --verify --write` re-runs and rewrites them:"
              % len(drifted))
        for why in drifted:
            print("  %s" % why)
        return 1

    if gate:
        if not owed:
            print("%d new or changed since %s, %d rostered "
                  "(%d unfoldable, %d witness fixtures, %d pinned by nothing; "
                  "%d literal)%s, 0 owed, %d pin site(s) still a bare line "
                  "number"
                  % (len(decls), base[:7], len(rostered), unfold,
                     fixture_rows, mute_rows, lit, shadow, unnamed))
            return 0
        print("%d new or changed since %s, %d rostered, %d OWED A MUTATION"
              % (len(decls), base[:7], len(rostered), len(owed)))
    bad, soft, pinned, by, _ = run(owed, write)
    if soft:
        print("%d definition(s) the fold cannot speak about -- "
              "UNFOLDABLE (no constant of the type exists) or "
              "LITERAL (the body IS one):" % len(soft))
        for tag, verdict, why in soft:
            print("  %-58s %-11s %s" % (tag, verdict, why))
    # **An UNFOLDABLE definition that an IDENTITY pins is audited after all**
    # (README gap 985).  One that neither reaches is the half nothing below the
    # gate speaks about, and it is named and counted on its own line so the
    # exemption cannot shrink out of sight -- check 8's allow-list discipline,
    # for the third time in this file.
    exempt = sorted({tag for tag, verdict, _ in soft
                     if verdict in ("UNFOLDABLE", "UNAVAILABLE")
                     and tag not in pinned})
    # **The declared exemption, split from the undeclared one** (README gap
    # 1086).  A row in a `WITNESS_MODULES` leaf is a FIXTURE: named, counted,
    # and exempt BY A RULE that is written down above.  A row anywhere else is
    # still pinned by NOTHING, which is the number that must not grow.
    fixture = [t for t in exempt if is_witness(t.rsplit(":", 1)[0])]
    mute = [t for t in exempt if t not in fixture]
    if fixture:
        print("%d of them are WITNESS FIXTURES -- declared exempt by "
              "WITNESS_MODULES, a leaf nothing in the library imports:"
              % len(fixture))
        for tag in fixture:
            print("  %s" % tag)
    if mute:
        print("%d of them are pinned by NOTHING -- no constant of the type, no "
              "identity on an accumulator and no synthesised term:" % len(mute))
        for tag in mute:
            print("  %s" % tag)
    if bad:
        print("%d definition(s) not pinned by a constant:" % len(bad))
        for tag, verdict, why in bad:
            print("  %-58s %-9s %s" % (tag, verdict, why))
        return 1
    if owed:
        kinds = collections.Counter(v for _, v, _ in soft)
        # `pinned` is per DEFINITION, not per verdict: a definition whose
        # `default` is UNFOLDABLE and whose identity is PINNED is pinned, and
        # counting the soft list instead reported five such rows as "0 pinned,
        # 5 unfoldable" on the run that introduced them.
        print("%d definition(s) audited (%d pinned, %d of them by an identity "
              "on an accumulator and %d by a synthesised constant; "
              "%d unfoldable, %d unavailable, %d witness fixtures, "
              "%d pinned by nothing; %d literal)"
              % (len(owed), len(pinned), by["identity"], by["synthesised"],
                 kinds["UNFOLDABLE"], kinds["UNAVAILABLE"], len(fixture),
                 len(mute), kinds["LITERAL"]))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
