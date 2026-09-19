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
definition: the body's sha1, the file, the name, the constants tried, and the
first error the build reported for each.  check.sh's check 9 RUNS the mutation
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
  * ONLY `def` and `abbrev`, and only in the library.  `theorem` has no body to
    fold (its "constant" is a different proof of the same statement, which is
    not this defect class); `structure`, `inductive` and `instance` are not
    mutated; `Check.lean`, `Negative.lean` and `Goals.lean` are outside the
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

HEAD = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)[ \t]+)*"
    r"(def|abbrev)[ \t]+([^\s(){}\[\],:]+)")

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


def lib_files():
    """The library's .lean files, as relative paths under kernel/."""
    return sorted("TmKernel/TmKernel/" + n for n in os.listdir(LIB)
                  if n.endswith(".lean"))


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


def declarations(text, path):
    """Every `def`/`abbrev` in one file: name, body text, char span, type."""
    out = []
    lines = text.split("\n")
    starts = []
    # `/- ... -/` nests in Lean, and a doc comment's continuation lines are
    # indented: without this tracker a commented-out `def` would be reported
    # UNPARSED and would fail the gate for a sentence.
    comment = 0
    for n, line in enumerate(lines):
        m = HEAD.match(line)
        if m:
            starts.append((n, m.group(2)))
        elif comment == 0 and INDENTED.match(line):
            out.append({"name": INDENTED.match(line).group(2), "file": path,
                        "line": n + 1, "last": n + 1, "body": None,
                        "type": None, "at": None, "stop": None, "lead": "",
                        "indented": True})
        comment += line.count("/-") - line.count("-/")
        comment = max(comment, 0)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line) + 1)
    for n, name in starts:
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
            out.append({"name": name, "file": path, "line": n + 1,
                        "last": end, "body": None, "type": None,
                        "at": None, "stop": stop, "lead": "", "header": header})
            continue
        out.append({"name": name, "file": path, "line": n + 1, "last": end,
                    "body": text[body_at:stop], "type": kind.strip(),
                    "at": body_at, "stop": stop, "lead": lead,
                    "header": header})
    return out


def digest(body):
    return hashlib.sha1(" ".join(body.split()).encode("utf-8")).hexdigest()[:12]


def roster():
    """(baseline sha, {(file, name): row}) from mutations.txt."""
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
    files = set()
    for argv in (["git", "diff", "--name-only", base,
                  "--", "kernel/TmKernel/TmKernel"],
                 ["git", "ls-files", "--others", "--exclude-standard",
                  "--", "kernel/TmKernel/TmKernel"]):
        got = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
        if got.returncode != 0:
            raise SystemExit("mutate.py: %s failed: %s"
                             % (" ".join(argv[:3]), got.stderr.strip()))
        files |= {line[len("kernel/"):] for line in got.stdout.split("\n")
                  if line.endswith(".lean")}
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


def mutate_one(decl, const):
    """Apply one constant, build, restore.  -> (verdict, first error line)."""
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
            first = "%s:%d" % (os.path.basename(where), line)
        if os.path.basename(where) == os.path.basename(decl["file"]) \
           and decl["line"] <= line <= decl["last"]:
            stop = hits[idx + 1].start() if idx + 1 < len(hits) else len(out)
            want = INHAB.search(out[m.end():stop])
            if want:
                return "UNFOLDABLE", "no Inhabited %s" % want.group(1).strip()
            return "INVALID", "%s:%d is inside the declaration" % (
                os.path.basename(where), line)
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


def run(decls, write, verbose=True):
    """Mutate each declaration with each of its constants.

    -> (bad, soft).  `bad` fails the gate; `soft` is the UNFOLDABLE roster --
    named, counted and printed on every run, never silent."""
    rows, bad, soft, pinned = [], [], [], set()
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
        for const in constants_for(decl) + ([ident] if ident else []):
            if verbose:
                # BEFORE the build, flushed: one mutation is a whole kernel
                # build, and a gate with no progress output looks like a hang.
                print("  %-58s %-9s building…" % (tag, ":= " + const),
                      end="\r", flush=True)
            verdict, why = mutate_one(decl, const)
            if verbose:
                print("  %-58s %-9s %-8s %-38s" % (tag, ":= " + const, verdict, why),
                      flush=True)
            verdicts.append((const, verdict, why))
            if verdict == "UNFOLDABLE":
                soft.append((tag, verdict, ":= %s -- %s" % (const, why)))
            elif verdict != "PINNED":
                bad.append((tag, verdict, ":= %s -- %s" % (const, why)))
        if any(v == "PINNED" for _, v, _ in verdicts):
            pinned.add(tag)
        if all(v in ("PINNED", "UNFOLDABLE") for _, v, _ in verdicts):
            rows.append("%s %s %s %s %s" % (
                decl["sha"], decl["file"], decl["name"],
                # WHITESPACE-FREE, because the roster is whitespace-delimited
                # and `fun _ _ => true` is one FIELD, not four.
                ",".join("".join(c.split()) if v == "PINNED" else "unfoldable"
                         for c, v, _ in verdicts)
                + ("" if literal is None else ",literal"),
                "; ".join(w for _, _, w in verdicts)
                + ("" if literal is None
                   else "; the body IS the constant `%s`" % literal)))
    if write and rows:
        with open(ROSTER, "a", encoding="utf-8") as handle:
            handle.write("\n".join(rows) + "\n")
        print("%d row(s) appended to mutations.txt" % len(rows))
    return bad, soft, pinned


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
    restore_in_flight()
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
        decls = [d for path in lib_files()
                 for d in declarations(read(os.path.join(HERE, path)), path)
                 if (d["file"], d["name"]) in rows]
        for d in decls:
            d["sha"] = digest(d["body"]) if d["body"] is not None else None
        print("re-running %d rostered mutation(s)" % len(decls))
        bad, soft, _ = run(decls, False)
        print("%d rostered definition(s) failed re-verification, "
              "%d unfoldable" % (len(bad), len(soft)))
        return 1 if bad else 0

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

    # The UNFOLDABLE count is printed on EVERY run, owed or not: a definition the
    # fold cannot reach is an exemption, and check 8's allow-list is the precedent
    # -- an exemption nobody counts is how a gate goes quietly useless.
    # `unfold` is every row the CONSTANT fold could not reach; `mute` is the
    # ones nothing reached, the identity on an accumulator included (README gap
    # 985).  They are printed as two numbers because they are two claims: the
    # first says `default` does not typecheck, the second says no mutation of
    # this definition exists at all, and only the second is an exemption.
    consts_of = lambda d: rows.get((d["file"], d["name"]), {}).get("consts", "")
    unfold = sum(1 for d in decls if "unfoldable" in consts_of(d))
    mute_rows = sum(1 for d in decls
                    if [c for c in consts_of(d).split(",") if c] == ["unfoldable"])
    lit = sum(1 for d in decls if "literal" in consts_of(d))
    if gate:
        if not owed:
            print("%d new or changed since %s, %d rostered "
                  "(%d unfoldable, %d of those pinned by nothing; %d literal), "
                  "0 owed"
                  % (len(decls), base[:7], len(rostered), unfold, mute_rows,
                     lit))
            return 0
        print("%d new or changed since %s, %d rostered, %d OWED A MUTATION"
              % (len(decls), base[:7], len(rostered), len(owed)))
    bad, soft, pinned = run(owed, write)
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
    mute = sorted({tag for tag, verdict, _ in soft
                   if verdict == "UNFOLDABLE" and tag not in pinned})
    if mute:
        print("%d of them are pinned by NOTHING -- no constant of the type and "
              "no identity on an accumulator:" % len(mute))
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
              "on an accumulator; %d unfoldable, %d pinned by nothing; "
              "%d literal)"
              % (len(owed), len(pinned),
                 sum(1 for t in pinned
                     if any(x == t and v == "UNFOLDABLE" for x, v, _ in soft)),
                 kinds["UNFOLDABLE"], len(mute), kinds["LITERAL"]))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
