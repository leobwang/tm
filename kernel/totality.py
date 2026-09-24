#!/usr/bin/env python3
"""The kernel must be total.

A Lean panic prints a C backtrace to stderr, returns `Inhabited.default`, and
gives the host exit code 0 -- a silent wrong answer, which is the exact failure
class this rebuild exists to remove.  `lean_set_exit_on_panic(true)` is no
better: it is exit(1) with no unwind, so a ratatui terminal is left in raw mode.
So the kernel is total instead, and this enforces it.

`.toOption` is banned for the same reason at the boundary: it is how the FFI
spike silently turned `est: -3` into `est: null`.

Usage: `totality.py <dir> [<dir> ...]`.  Each directory is scanned
RECURSIVELY, with build and tooling entries pruned on the PROPERTY
`leanfiles.is_derived` states and never on a name (the sentence here said
".lake, target and .git" until W-29, which is the name list W-22 deleted).  `check.sh` passes both
`TmKernel/TmKernel` (the library) and `TmKernel` (the package root, which holds
`Check.lean`, `Negative.lean` and `Goals.lean`), so the exemption below is
load-bearing rather than decorative.

THE RECURSION IS THE W-21 REPAIR STEP'S, and it closes a hole three checkers
shared.  This scan used to be one level deep, and so did `citations.py`'s
`LEAN_FILES` and `mutate.py`'s `lib_files` -- while `mutate.py`'s own
`touched()` asks git with a RECURSIVE pathspec, and `check.sh` line 204 states
the swept set as `TmKernel/**.lean`.  DRIVEN before the repair:
`TmKernel/TmKernel/Sub/Probe.lean` holding `partial def w21SubLoop` (R4, a HARD
RULE), `def w21SubGatherable (_n : Nat) : Bool := true` (D40's exact class) and
a backticked Look.zzz_no_such_thing gave this file rc=0, `citations.py` rc=0
with byte-identical counts, and `mutate.py --gate` rc=0 "0 owed".  A library
module in a SUBDIRECTORY was invisible to checks 2, 8 and 9 at once.

AND THE W-22 REPAIR STEP MOVED THE WALK OUT OF THIS FILE, because the W-21
repair left two holes of the same shape.  `check.sh`'s check-3 roster grep was
never made recursive -- a theorem in a subdirectory was never required to have a
`#print axioms` line -- and the three walks that WERE repaired shared a prune
list holding the name `target`, a legal Lean module path component, so a library
module under `kernel/TmKernel/TmKernel/target/` was invisible to checks 2, 8 and
9 again.  Both driven; `leanfiles.py` is the one enumeration all four now use,
and it prunes on a PROPERTY (a leading dot, or a CACHEDIR.TAG file) rather than
on a name.

AND THE EXEMPTION NARROWED WITH IT.  `Goals.lean` is exempt only AT THE ROOT of
a directory named on the command line; a `Sub/Goals.lean` is scanned like any
other file.  Without that test the recursion would have widened the one
exemption into a directory anybody could create.
"""
import bisect, re, sys, pathlib

import leanfiles

# The one exemption, named file by file rather than by loosening a pattern.
#
# `Goals.lean` holds the outstanding goals of stages 3-6 as theorem statements
# with `sorry` proofs -- an unproved statement that *elaborates* is the whole
# point of the file, because it is checked to be well-formed and to name real
# definitions.  It is safe because it is imported by nothing: `TmKernel.lean`
# does not import it and no module of the library does, so its `sorry`s cannot
# reach a proved theorem.  `check.sh`'s axiom audit is what enforces that -- a
# `sorryAx` in `Check.lean` means this file leaked.
#
# NAMED BY PATH, NOT BY NAME-AT-A-ROOT (the W-27 repair step).  The test used to
# be "called `Goals.lean` AND sitting at the root of some directory on the
# command line", and `check.sh` names TWO roots -- `TmKernel/TmKernel` and
# `TmKernel` -- so the library directory was *also* a root and
# `TmKernel/TmKernel/Goals.lean`, a real compiled library module, was exempt
# from every rule in this file.  DRIVEN in a `git archive HEAD` clone: that path
# holding `partial def` and `unsafe def`, imported by `TmKernel.lean` and built
# by `lake build TmKernel:static`, gave rc=0 and no output; the identical file
# named `Probe.lean` was named on both lines.  The header above claimed the
# opposite ("without that test the recursion would have widened the one
# exemption into a directory anybody could create") -- the SECOND ROOT was that
# widening.  Same class as gap 1314: the walk was shared, the exemption was not.
#
# So the exemption is now ONE PATH, resolved against this file's own directory,
# and it does not depend on how a caller spells its arguments.
EXEMPT_PATHS = {(pathlib.Path(__file__).resolve().parent / "TmKernel" / "Goals.lean")}

# A CHARACTER LITERAL AND AN INTERPOLATION PREFIX ARE THE TWO PLACES A `!` IS
# NOT PART OF A NAME, and both are blanked before the scan so that the ban below
# can be a CLASS instead of a list.  `renderPrio` in `Line.lean` writes `'!'` (33
# occurrences) and 25 lines write `s!"..."`; under a rule that reads any `!`
# after an identifier character those 58 lines are false positives, and a false
# positive is how a class-shaped rule gets narrowed back into a name list.
#
# Both tests are SHAPES, not letters.  `CHAR_LIT` is Lean's character literal --
# one character, or one backslash escape, between apostrophes -- and the
# apostrophe matters because `'` is also an identifier character in Lean
# (`h'`, `foo'`), which is why the two `'`s must be exactly two characters apart.
# `INTERP` is a ONE-LETTER prefix with no identifier character in front of it and
# a string literal immediately after: `s!"`, and `m!"` and `f!"` if they are ever
# used.  A `!`-accessor written flush against a string (`xs.get!"k"`) is three
# letters, not one, so it is still caught -- which is the whole reason the test
# counts letters instead of listing `s`.
CHAR_LIT = leanfiles.CHAR_LIT  # defined beside `strip_comments`, its other caller
INTERP = re.compile(r"(?<![A-Za-z0-9_'])([a-z])!(?=\")")

# WHAT IS BANNED, AND THE HALF OF R4 THAT WAS NEVER MECHANISED.
#
# AGENTS R4 bans `partial def`, `unsafe`, `opaque`, `@[implemented_by]`, `panic!`
# and `!`-ACCESSORS.  Until W-27 this list held seven regexes and R4's own row in
# AGENTS 3 said, in the "checked by" column, that `unsafe`, `opaque` and
# `@[implemented_by]` were "audit items" -- an audit that appears nowhere in
# `check.sh` and that no step of this campaign has ever performed.  They are
# mechanised here; the row now says `totality.py` for the whole of R4.
#
# AND THE `!`-ACCESSORS WERE A NAME LIST, which is the shape this campaign has
# now found wrong eight times.  R4 bans the CLASS and says `.get!` and `xs[i]!`
# as EXAMPLES; the list held exactly those two examples, so `.head!`,
# `.getLast!`, `.back!`, `.find!`, `.getD!` and every other member of the class
# compiled and gave this file rc=0.  DRIVEN in a `git archive HEAD` clone at
# W-27: `.head!`, `.getLast!`, `.back!` and `.find!` each planted alone in
# `Emit.lean` left this file at rc=0 and are each named by it now.
#
# THE CLASS IS A `!` THAT ENDS A NAME: preceded by an identifier character or by
# the `]` of an index, and not followed by `=` (`a != b` is `BEq` negation, and
# Lean tokenises `a!=b` as `a`, `!=`, `b`, so a `!`-accessor can never be
# immediately followed by `=` -- the exclusion is exact, not a hole).  Prefix
# `!` (Boolean `not`) has a space, a bracket or nothing in front of it and is
# untouched.  MEASURED over the scanned files at W-27: 509 `!` characters in
# code, of which 33 are character literals, 25 are `s!` prefixes and the
# remaining 451 are prefix `not` or the `!=` of `BEq` negation.  None is an
# accessor, which is why this widening lands green.
#
# `panic!` KEEPS ITS OWN ROW because it is separately named in R4 and in this
# file's own header, and the class rule excludes it by a lookbehind so that a
# `panic!` is reported once under its own name.  The lookbehind can only ever
# cause a MISSED SECOND REPORT of a line the row above already catches, never a
# missed line: if it went wrong, `panic!` still fires.
# **AND `@[implemented_by]` WAS ONE SPELLING OF A CLASS** (the W-28 repair step,
# README gap 1875).  R4 bans "the compiled implementation is not the Lean
# definition" and gave `@[implemented_by]` as its spelling, so the list held
# exactly that spelling.  `@[extern "sym"] def f .. := <lean body>` has exactly
# the same effect -- every proof and every `#print axioms` sees the Lean body
# while the linked archive runs the C symbol -- and it was UNBANNED.  DRIVEN in
# a `git archive HEAD` clone: `@[extern "tm_evil_probe"] def w28ExternProbe
# (n : Nat) : Nat := n` appended to `Emit.lean` left this file at rc=0.  Pointed
# at a symbol the archive already defines it links and runs.  That is W-27's
# finding -- the proof layer cannot see WHICH definition the archive exports --
# reached on the BODY, and R4's own row records the precedent: the `!`-accessors
# were a two-example list and six members of the class walked through it.
#
# SO THE ATTRIBUTES ARE AN ENUMERATION YOU JOIN TO BE EXEMPT, NOT ONE YOU JOIN
# TO BE BANNED.  A longer ban list would be the ninth instance of the shape this
# campaign keeps paying for: it would need a row for `@[extern]`, then for
# `@[init]`, `@[builtin_init]`, `@[never_extract]`, `@[macro_inline]` and for
# whatever a later toolchain adds.  `ALLOWED_ATTRS` below is the whole set this
# kernel uses, and ANY OTHER attribute is reported BY NAME.
#
#   simp       a rewrite-rule tag.  It cannot change a definition; it changes
#              what `simp` tries.  20 live.
#   csimp      a COMPILER simp lemma -- and it is the one entry that touches
#              the compiled body, which is why it is safe: `@[csimp] theorem
#              f_eq : f = fFast` is a PROVED equality, so the body the archive
#              runs is provably the Lean definition.  84 live.
#   reducible  a unfolding-transparency tag.  2 live.
#   export     R9's one symbol -- it EXPOSES the Lean body under a C name; it
#              does not replace it.  1 live, and `PlanWire.callExport` is it.
#
# THE COST IS DECLARED, and it is the cost every residue rule in this gate has:
# an attribute that is HARMLESS but new -- `@[inline]`, `@[specialize]` -- fails
# this check until somebody adds it above with a sentence saying why it cannot
# change what the archive runs.  That is one line and a reason, and the
# alternative is a ban list that is complete only against the members somebody
# has already thought of.
#
# **AND THE RESIDUE READ ONE OF LEAN'S TWO SPELLINGS** (W-29, README gap 1950).
# The sentence that used to stand here said, as a declared blind spot, that an
# attribute applied by the `attribute [..] name` COMMAND was not seen -- and
# argued it away because the library writes none.  W-27's own second half is the
# precedent for what a declared-and-unmechanised audit is worth: it is never
# performed.  DRIVEN in a `git archive HEAD` clone at W-29:
#
#     def w29ExternProbe (n : Nat) : Nat := n
#     attribute [extern "tm_kernel_call_c"] w29ExternProbe
#
# appended to `Emit.lean` BUILT (`lake build TmKernel:static`, "Build completed
# successfully") and left this file at **rc=0, no output** -- while the SAME
# attribute on the SAME declaration, written `@[extern "tm_kernel_call_c"] def
# w29ExternProbe ..`, is named.  One rule, two spellings, one of them read: that
# is gap 1875's own shape reached through the syntax rather than through the
# attribute list, and `@[implemented_by]`'s command spelling was caught only by
# the unrelated bare-token row below, never by this residue.
#
# So an ATTRIBUTE APPLICATION is the class, and `ATTR_SPELLINGS` is every way
# Lean has of writing one.  MEASURED at W-29 and declared rather than argued:
# the command form does NOT redirect code generation in this toolchain --
# the generated C under .lake still carries the probe's own Lean body after the
# plant, and so does the `implemented_by` form --
# so the plant is a GATE hole and this file does not claim it landed an escape.
# The gate bans the class because the gate cannot know which spelling a later
# toolchain wires up, and because `attribute [instance]` and `attribute [simp]`
# change what later elaboration sees whatever the compiler does.
#
# WHAT IT STILL CANNOT SEE: an `attribute` command whose brackets are built by a
# macro (the kernel defines none -- `macro`, `macro_rules`, `elab` and `syntax`
# are all refused by `ALLOWED_COMMANDS` below); a `deriving` clause, which is a
# different grammar and instantiates rather than replaces; and the word
# `attribute` inside a string literal, which `strip_comments` blanks -- so the
# false positive it could cause cannot happen and a true one cannot hide.
ALLOWED_ATTRS = {"simp", "csimp", "reducible", "export"}
# The two spellings, ONE rule.  `@[a, b]` is the declaration block; `attribute
# [a, b] name` is the command.  The lookbehind is the identifier alphabet, so a
# name that ENDS in the word is not a token of it.
ATTR_SPELLINGS = (re.compile(r"@\[([^\]]*)\]"),
                  re.compile(r"(?<![\w'?!.«])attribute\s*\[([^\]]*)\]"))

# **AN OPTION IS AN ESCAPE HATCH TOO** (W-29, README gap 1951).  `set_option` was
# unbanned and its ARGUMENT unread, and the option namespace holds
# `debug.skipKernelTC` -- the switch that turns the kernel typechecker OFF, which
# is every `#print axioms` line in `Check.lean` and the whole of check 3 read
# through a check that no longer runs.  DRIVEN in a clone:
#
#     set_option debug.skipKernelTC true in
#     theorem w29SkipTC : (1 : Nat) + 1 = 2 := rfl
#
# appended to `Emit.lean` BUILT and left this file at **rc=0**.  (What the plant
# shows is the HOLE: no term the elaborator accepts and the kernel rejects was
# constructed here, so no unsound proof is claimed to have landed.)
#
# A BAN LIST WOULD BE THE NEXT LENGTHENING: it would need a row for
# `debug.skipKernelTC`, then for `compiler.*`, `debug.*`, `backward.*` and for
# whatever a later toolchain adds.  So the options are a RESIDUE, the same shape
# `ALLOWED_ATTRS` is: these four are every option this kernel sets, each with the
# sentence that says why it cannot change what is PROVED or what RUNS, and any
# other option is named.
#
#   maxRecDepth            an elaboration resource bound.  Exceeding it is an
#                          ERROR, never a silent acceptance.  314 live.
#   maxHeartbeats          the same, in time rather than in stack.  1 live.
#   linter.unusedSimpArgs  a LINT -- it changes what is reported, and a linter
#                          has never been what accepts a proof.  1 live.
#   exponentiation.threshold  a guard on how large a literal exponent the
#                          elaborator will evaluate; a bound, like the first two.
#                          1 live.
ALLOWED_OPTIONS = {"maxRecDepth", "maxHeartbeats", "linter.unusedSimpArgs",
                   "exponentiation.threshold"}
SET_OPTION = re.compile(r"(?<![\w'?!.«])set_option\s+([A-Za-z_][A-Za-z0-9_.']*)")

# **AND THE COMMANDS THEMSELVES ARE A RESIDUE** (W-29, README gap 1952).  Every
# row of `BANNED` below is one member of one class -- `partial def`, `unsafe`,
# `opaque`, `axiom`, `example` are all *commands or modifiers somebody thought
# of*, and the campaign has now watched that shape fail nine times.  DRIVEN in a
# clone: `def w29Diverge (n : Nat) : Option Nat := w29Diverge (n + 1)` with
# `partial_fixpoint` on the next line BUILT and left this file at **rc=0** -- a
# definition Lean never had to justify the recursion of, spelled without the
# `partial` keyword the list holds.
#
# MEASURED over the library at W-29: TWENTY-TWO distinct words begin a
# column-zero line in stripped source, and every one of them is a command or a
# declaration keyword this kernel uses.  That is small, it is stable, and it is
# the enumeration to invert: a command must JOIN this set to be allowed, so
# `partial`, `unsafe`, `opaque`, `axiom`, `example`, `attribute`, `initialize`,
# `builtin_initialize`, `macro`, `macro_rules`, `elab`, `syntax`, `notation`,
# `register_builtin_option` and whatever a later toolchain adds are all refused
# BY NAME without this file learning their names.
#
# WHAT IT CANNOT SEE, and it is the blind spot W-28's roster repair named: a
# command written MID-LINE after an `in` combinator (`open Nat in unsafe def
# ..`).  Every member of the class this campaign knows about is ALSO caught by
# its own token row below, which is why those rows stay: the residue is the net
# under the members nobody has thought of, and the rows are the net under the
# spelling this one cannot reach.
ALLOWED_COMMANDS = {
    "abbrev", "class", "decreasing_by", "def", "deriving", "end", "import",
    "include", "inductive", "instance", "mutual", "namespace", "omit", "open",
    "private", "section", "set_option", "structure", "termination_by",
    "theorem", "variable", "where",
}
COMMAND_WORD = re.compile(r"(?m)^([A-Za-z_][A-Za-z0-9_'.]*)")

BANNED = [
    # **THE KEYWORD IS A STEM, NOT A WORD** (W-29, README gap 1952).  This row
    # was `partial\s+def`, and `partial_fixpoint` -- Lean 4.33's other way of
    # writing a definition whose recursion it did not have to justify -- is not
    # `partial` followed by `def`, nor even `\bpartial\b`, because `_` is a word
    # character.  The rule is the token `partial` with anything but a LETTER
    # after it: `partial def`, `partial_fixpoint`, and any `partial_*` a later
    # toolchain adds.  The one identifier in the library that begins with the
    # word -- `partialDoneAt`, 11 occurrences -- continues in a letter and is
    # not a token of it; the cost is declared: a THEOREM named `partial_...`
    # would fail here and have to be renamed or allowed.
    (r"(?<![\w'])partial(?![A-Za-z])",
     "partial (R4: `partial def` and `partial_fixpoint` -- a definition Lean "
     "did not have to justify the recursion of)"),
    (r"\baxiom\b", "axiom (HARD RULE: no new axiom)"),
    (r"panic!", "panic!"),
    (r"native_decide", "native_decide"),
    (r"\bsorry\b", "sorry"),
    (r"(?<=[A-Za-z0-9_'\]])(?<!panic)!(?!=)", "`!`-accessor (R4)"),
    (r"\bunsafe\b", "unsafe (R4)"),
    (r"\bopaque\b", "opaque (R4)"),
    (r"\bimplemented_by\b", "@[implemented_by] (R4)"),
    (r"\.toOption", ".toOption"),
    # **AN UNAUDITABLE PROOF** (the W-28 repair step, README gap 1883).  check 3
    # reconciles the DECLARED theorems against the `#print axioms` lines, and
    # `leanfiles.THEOREM` is the keyword token `theorem` -- one declaration
    # keyword.  `example` is the member of the proof-carrying class that can
    # never be reconciled, because it has no name to audit: an `example` whose
    # proof depended on `sorryAx` would be invisible to check 3 by
    # construction.  0 live in this library, so banning it costs nothing and
    # closes the half of gap 1883 that is closeable here.  The OTHER half --
    # a `def`, `abbrev` or `instance` whose TYPE is a Prop, which `#print
    # axioms` accepts and the roster does not demand -- needs the library
    # ELABORATED to decide which types are Props, and that is gap 1883's own
    # shape.  Nothing leaks today because the bare token `sorry` is banned
    # above, in every file but `Goals.lean`.
    (r"(?<![\w'?!.\u00AB])example(?![\w'?!])", "example (an unauditable proof, R4/check 3)"),
]

# THE ENUMERATION IS `leanfiles.lean_files`, and it is not this file's any more
# (the W-22 repair step).  Four checkers answered "which files ARE the kernel"
# separately; three were made recursive at W-21 and the fourth -- `check.sh`'s
# check-3 roster grep -- was not, because nothing named it.  Worse, the three
# that were repaired shared a hard-coded prune list holding the name `target`,
# which is a LEGAL Lean module path component, so a library module under
# `kernel/TmKernel/TmKernel/target/` was invisible to checks 2, 8 and 9 at once
# -- W-21's `Sub/` class reached through the prune list instead of through the
# non-recursion.  DRIVEN before the repair: a `target/Probe.lean` holding
# `partial def w22TargetLoop`, a HARD RULE, gave this file rc=0.  The prune rule
# is now a PROPERTY a build directory has (a leading dot, or a CACHEDIR.TAG
# file) and never a name.

bad = 0
# `check.sh` passes `TmKernel/TmKernel` AND `TmKernel`, so with the recursion
# every library file is reached twice; a SET is what keeps it scanned once.  It
# is a set and no longer a path->at-a-root dict because the exemption above is a
# PATH now and does not care which argument reached the file.
files = set()
for d in sys.argv[1:]:
    files.update(leanfiles.lean_files(pathlib.Path(d)))
for p in sorted(files):
    if p.resolve() in EXEMPT_PATHS:
        continue
    code = leanfiles.strip_comments(p.read_text())
    code = CHAR_LIT.sub("''", code)
    code = INTERP.sub(lambda m: m.group(1) + " ", code)
    # WHOLE-FILE, not line by line.  `partial\s+def` can only cross a newline if
    # the text it is matched against holds one: DRIVEN in a clone, `partial` and
    # `def critLoopA ..` on two lines built (`Build completed successfully`) and
    # left this file at rc=0, while the same body on one line was named.  The
    # rule was written for exactly that construct.  Line numbers come from the
    # match offset instead of from the loop.
    nl = [i for i, ch in enumerate(code) if ch == "\n"]
    hits = set()
    for pat, name in BANNED:
        for m in re.finditer(pat, code):
            hits.add((bisect.bisect_right(nl, m.start()) + 1, name))
    # THE ATTRIBUTE RULE, and it is a residue and not a list: every attribute
    # this kernel uses is in `ALLOWED_ATTRS` with a sentence, and anything else
    # is named here.  A block may hold several (`@[simp, csimp]`); the leading
    # token of each comma-separated entry is the attribute's NAME and the rest
    # is its argument (`export tm_kernel_call`, `extern "sym"`).
    #
    # BOTH SPELLINGS, ONE LOOP (W-29).  `ATTR_SPELLINGS` is the `@[..]` block and
    # the `attribute [..] name` command, and writing the rule twice would be the
    # §5.3 defect this gate exists to catch in the library.
    for spelling in ATTR_SPELLINGS:
        for m in spelling.finditer(code):
            for entry in m.group(1).split(","):
                word = entry.split()
                if not word:
                    continue
                if word[0] not in ALLOWED_ATTRS:
                    hits.add((bisect.bisect_right(nl, m.start()) + 1,
                              "@[%s] -- not in ALLOWED_ATTRS (R4: the compiled "
                              "implementation must be the Lean definition)" % word[0]))
    # THE OPTION RULE (W-29): `set_option <name>` names an option or it is named
    # here.  `debug.skipKernelTC` is the member that reads every `#print axioms`
    # line in `Check.lean` through a check that no longer runs.
    for m in SET_OPTION.finditer(code):
        if m.group(1) not in ALLOWED_OPTIONS:
            hits.add((bisect.bisect_right(nl, m.start()) + 1,
                      "set_option %s -- not in ALLOWED_OPTIONS (R4: an option "
                      "may not change what is proved or what runs)" % m.group(1)))
    # THE COMMAND RULE (W-29): the word that begins a column-zero line is a
    # command this kernel uses, or it is named here.  It is the net under the
    # members of R4's class nobody has thought of yet -- `partial_fixpoint` was
    # one, and it went green under a list of five spellings.
    for m in COMMAND_WORD.finditer(code):
        if m.group(1) not in ALLOWED_COMMANDS:
            hits.add((bisect.bisect_right(nl, m.start()) + 1,
                      "`%s` begins a line and is not in ALLOWED_COMMANDS (R4: a "
                      "command this kernel does not use)" % m.group(1)))
    for n, name in sorted(hits):
        print(f"{p}:{n}: banned: {name}")
        bad += 1
sys.exit(1 if bad else 0)
