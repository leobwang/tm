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
# **AND A COMMAND IS A TOKEN, NOT A COLUMN** (the W-29 repair step, README gap
# 2009).  This residue used to be anchored at column zero, and it said so in its
# own blind-spot paragraph -- which is W-27's lesson (a declared-and-unmechanised
# audit is never performed) written about itself.  DRIVEN in a clone whose
# `.lake` was warmed from the shared tree: `open Nat in macro "w29mac" : term =>
# `(0)` and `open Nat in initialize w29Ref2 : IO.Ref Nat <- IO.mkRef 0`, each on
# ONE line appended to `Emit.lean`, both BUILT (`Build completed successfully`)
# and left this file at rc=0 with NO output; the same two commands at column zero
# were both named.  `macro`, `syntax`, `elab`, `notation`, `initialize`,
# `macro_rules`, `builtin_initialize` and `register_builtin_option` are exactly
# the escapees, because they are the commands with no token row of their own.
#
# THE RULE IS LEAN'S OWN: a command begins the source, and a command begins
# again after the `in` of a command combinator (`open X in ..`, `set_option ..
# in ..`, `variable .. in ..`).  So `command_positions` below reads the word at
# the start of every line AND the word after every `in` token, and both are put
# through the same residue.  The one `in` that is NOT a combinator is the `in`
# of a `for` loop, and it is told apart by its own binder rather than by a list
# of words: an `in` whose nearest preceding token among {`for`, `in`} is `for`
# binds a loop variable (3 live, all in `Boundary.lean`'s `for .. in .. do`).
#
# MEASURED over the library at the repair step: 362 `in` tokens, 359 of them at
# end of line (the command is on the next line and was already read), 3 of them
# `for`-loop binders, and the residue is UNCHANGED at rc=0 -- so the rule costs
# nothing here and closes the hole.
#
# WHAT IT CANNOT SEE: a command produced by a macro (the kernel defines none);
# a binder form spelled `x in e` that this library does not write, whose
# following word would be read as a command and NAMED -- a failing gate, which
# is the loud direction, and the cost is declared rather than silent; and the
# blind spots `strip_comments` lists.
ALLOWED_COMMANDS = {
    "abbrev", "class", "decreasing_by", "def", "deriving", "end", "import",
    "include", "inductive", "instance", "mutual", "namespace", "omit", "open",
    "private", "section", "set_option", "structure", "termination_by",
    "theorem", "variable", "where", "#print",
}
# THE FIRST WORD OF EVERY LINE, indented or not (W-30).  It was anchored at
# column zero, which is the hole `command_keywords` exists to close; the two
# populations are told apart by whether the leading-space group is empty.
#
# **AND THE WORD CLASS WAS SHORTER THAN LEAN'S** (W-31 repair, README gap 2255).
# W-30 closed the KEYWORD SET and left `[A-Za-z_]` standing, so a `#`-command --
# `#eval`, `#check`, `#print`, `#reduce`, `#synth`, and the twenty-two more the
# derivation below now reads out of the pin -- never entered `command_positions`
# AT ALL: not indented, not at column zero.  `#eval` elaborates arbitrary
# `CommandElabM`, which is `run_cmd` by another spelling, and `run_cmd` is the
# construct W-30 drove a NEW AXIOM past every gate with.  DRIVEN in a `cp -a`
# clone with its own build tree: `#eval show CommandElabM Unit from liftCoreM <|
# Lean.addDecl (Lean.Declaration.axiomDecl { name := `Tm.w31Planted, type :=
# mkConst ``False, .. })` appended to `Emit.lean` inside a `section`, plus
# `theorem w31_one_is_two : (1:Nat) = 2 := (w31Planted).elim`, BUILT at rc=0
# ("Build completed successfully (174 jobs)") and left this file at RC=0 WITH NO
# OUTPUT.  With the `#?` below it is named at both columns.
#
# AND THE POSITION WAS ONLY HALF OF IT: `KEYWORD` -- the filter the derivation
# puts its own keywords through -- carried the same short class, so `#eval` was
# not in `command_keywords()` either and the INDENTED spelling still walked
# past.  DRIVEN, with this line widened and `KEYWORD` left alone: the same plant
# INDENTED inside its `section` gave rc=1 naming Check.lean's two documentation
# `#eval`s and NOT `Emit.lean:534`.  One rule read through one spelling, twice
# over, in the two places that had to agree -- the twelfth counted instance.
#
# **AND THE `in` POSITION KEPT THE SHORT CLASS** (W-33 repair, README gap 2561).
# The W-31 widening went into `COMMAND_WORD` and `KEYWORD` and not into `WORD`,
# the class `command_positions` reads the word after a combinator's `in` with --
# so `open Lean Elab Command in #eval show CommandElabM Unit from do ..addDecl
# (.axiomDecl ..)` on ONE line passed this file at rc=0 with no output while
# check 3 named the new axiom (driven by W-33's auditor in a clone: 10 of 11
# spellings bit, this one did not).  The two POSITION readers -- the line head
# and the word after `in` -- read ONE class now, `COMMAND_WORD_CLASS`, so the
# next widening cannot land in one of them; `KEYWORD` below is the filter on
# the derived keyword set, and it carries the same leading `#?`.
COMMAND_WORD_CLASS = r"#?[A-Za-z_][A-Za-z0-9_'.]*"
COMMAND_WORD = re.compile(r"(?m)^([ \t]*)(%s)" % COMMAND_WORD_CLASS)
# The `in` combinator and the `for` binder that is not one, as TOKENS.
IN_TOKEN = re.compile(r"(?<![\w'?!.\u00AB])in(?![\w'?!])")
FOR_TOKEN = re.compile(r"(?<![\w'?!.\u00AB])for(?![\w'?!])")
# What may stand between a command position and the command's own word: layout,
# and the attribute blocks `ALLOWED_ATTRS` already answers for.
LEADING = re.compile(r"(?:\s|@\[[^\]]*\])*")
WORD = re.compile(COMMAND_WORD_CLASS)


def command_positions(code):
    """Every offset in stripped `code` at which a Lean COMMAND may begin.

    Yields `(offset, word, certain)`.  `certain` is True where a command MUST
    begin -- column zero, and the word after a command combinator's `in` -- and
    False where one MAY begin, which is every other line head.  The two carry
    different rules below, and the second is W-30's (README gap 2091).
    """
    for m in COMMAND_WORD.finditer(code):
        yield m.start(2), m.group(2), not m.group(1)
    fors = [m.start() for m in FOR_TOKEN.finditer(code)]
    ins = [m for m in IN_TOKEN.finditer(code)]
    for k, m in enumerate(ins):
        prev_in = ins[k - 1].start() if k else -1
        prev_for = max([f for f in fors if f < m.start()], default=-1)
        if prev_for > prev_in:
            continue  # `for x in xs` -- a binder, not a combinator
        j = LEADING.match(code, m.end()).end()
        w = WORD.match(code, j)
        if w:
            yield w.start(), w.group(0), True


# **AND THE COMMAND RESIDUE WAS ANCHORED AT COLUMN ZERO** (W-30 track A, README
# gap 2091).  W-29 made the commands a residue and gave the `in` combinator its
# own position, and left the LINE HEAD at column zero -- so `macro`, `syntax`,
# `elab`, `notation`, `initialize`, `macro_rules` and `builtin_initialize`, the
# seven commands with no `BANNED` row of their own, escaped by being INDENTED.
# Lean does not care: a command may begin at any column, and this library writes
# `section .. end` in eleven files, which is where an indented command looks
# like it belongs.  DRIVEN in a `git archive HEAD` clone with a warmed `.lake`:
# two spaces in front of `macro "w30mac" : term => `(0)` and of `initialize
# w30Ref : IO.Ref Nat <- IO.mkRef 0`, appended to `Emit.lean` inside a
# `section`, BUILT and left this file at rc=0 with no output; at column zero
# both are named.  That is W-29's own finding -- one rule, one spelling read --
# reached through the COLUMN instead of through the syntax, and it is the tenth
# time this campaign has found a rule stated over a spelling somebody thought of.
#
# WIDENING THE POPULATION IS NOT ENOUGH, AND IT IS WHY THIS TOOK A KEYWORD SET.
# The residue's rule is "the word here is in ALLOWED_COMMANDS or it is named",
# and at an INDENTED line head that rule is false of correct Lean: a proof step,
# a `match` arm, a structure field and a `let` all begin lines, and none of them
# is a command.  MEASURED over this library: 22 distinct words begin a
# column-zero line and 1,133 begin an indented one.  A residue over 1,133 words
# is a list again -- the ninth instance of the shape, written by the file whose
# header says it costs the campaign a finding a run.
#
# SO THE INDENTED RULE ASKS LEAN'S OWN GRAMMAR.  A word at a MAY-begin position
# is refused when it is a word Lean declares a command by -- and that set is
# READ OUT OF THE PINNED TOOLCHAIN'S PARSER SOURCES, not written here.  Nothing
# has to be added for `macro_rules` or for a command a later toolchain invents:
# the set comes from the toolchain that compiles this kernel, and a toolchain
# that adds a command adds it here.
#
# **AND THAT SENTENCE NAMED `register_builtin_option` AND WAS FALSE OF IT**
# (W-30 repair, README gap 2125).  The derivation read ONE of Lean's two ways of
# declaring a command -- a `def` carrying `@[builtin_command_parser]` -- and
# `register_builtin_option` is declared the other way, `macro (name :=
# registerBuiltinOption) .. : command` at `Lean/Data/Options.lean:228`.  So the
# file written to close "a claim of having checked that was never made" made
# one, about the very keyword it named.  MEASURED: the parser-`def` derivation
# yields 52 keywords and the `: command` SYNTAX CATEGORY yields 66, of which 66
# are new -- 118 in the union.  Among the 66: `run_cmd`, `run_elab`, `run_meta`,
# `seal`, `unseal`, `test_extern`, `reprove`, `register_builtin_option`.
#
# THE FIRST THREE ELABORATE ARBITRARY METACODE, AND THAT IS A NEW AXIOM PAST
# EVERY GATE.  DRIVEN in a `git archive HEAD` clone against the built library
# (`LEAN_PATH=kernel/TmKernel/.lake/build/lib/lean`, 8G, timeout 300): a file
# whose `section` holds an INDENTED `run_cmd liftCoreM <| Lean.addDecl
# (Lean.Declaration.axiomDecl { name := w30Planted, .. type := mkConst ``False
# .. })` elaborates at rc=0 and prints that the planted name depends on an axiom
# of its own, and the same for a `theorem w30Anything : (1:Nat) = 2` proved from
# it.  The word `axiom` never appears, so the
# `axiom` token row below never fires; check 3 fails on `sorryAx` and the
# planted axiom is not `sorryAx`.  Before this repair `totality.py
# TmKernel/TmKernel TmKernel` gave rc=0 and NO OUTPUT on that file; with
# `run_cmd` moved to COLUMN ZERO it gave rc=1.  The escape was the indentation
# -- exactly the hole W-30 track A opened (gap 2091), closed for seven commands
# and left open for this one because the KEYWORD SET, not the position, was
# short.  After this repair the same file is named at rc=1 indented.
#
# THE FIX IS THE SECOND DERIVATION, NOT EIGHT MORE NAMES.  A command keyword is
# a word a `syntax`/`macro`/`elab` declaration in the `command` CATEGORY
# consumes first, as much as it is one a `@[builtin_command_parser] def`
# consumes first, and both are read out of the pin.
#
# THE DERIVATION, and it is four sentences of Lean's own convention:
#
#   * a command parser is a `def` carrying `@[builtin_command_parser]` (or
#     `@[command_parser]`).  FOUR files of `src/lean` declare one.
#   * a command is ALSO declared by a `syntax`, `macro` or `elab` whose
#     declaration head ends `: command` (before its `=>`, and with string
#     literals masked so the ` " : " ` inside `register_builtin_option`'s own
#     head is not read as the category).  Its keyword is the first string
#     literal of that head.
#   * its KEYWORD is the parser's «»-escaped name where it has one -- Lean
#     escapes exactly the names that are reserved words -- and otherwise the
#     first string literal of its body, which is the token it consumes first.
#     A `<|>` of named parsers (`declaration`) names its alternatives in `«»`
#     too, and each of those is a keyword.
#   * a parser whose body is NOTHING BUT string literals contributes all of
#     them: `initializeKeyword := leading_parser "initialize " <|>
#     "builtin_initialize "` is the one in this toolchain, and it is how
#     `builtin_initialize` -- named in W-29's own comment as an escapee -- gets
#     into the set at all.
#
# MEASURED at W-30: 52 keywords, of which 35 are outside ALLOWED_COMMANDS; the
# derivation is 0.046 s once per run and cached, against this file's 1.48 s
# (three runs each, before and after, and the two are the same to the hundredth
# -- 1.47-1.49 before, 1.48 after).  Over the whole library, every indented line
# head, the widened rule fires ZERO times.  So it closes the hole and costs nothing here, which is the
# evidence that it is a rule about COMMANDS and not a wider net.
#
# WHAT IT CANNOT SEE, measured rather than argued:
#
#   * a DECLARATION MODIFIER reached only through a multi-parser helper --
#     `private`, `protected`, `noncomputable`, `partial`, `unsafe`, `nonrec`
#     live in `declModifiers`, which is not a pure token parser, so they are not
#     in the set.  `partial`, `unsafe`, `opaque`, `axiom` and `example` have
#     `BANNED` rows of their own that are TOKEN rules at any column, so the
#     class R4 bans is covered; the rest are ALLOWED_COMMANDS members anyway.
#   * a command a MACRO produces (the kernel defines none -- `macro`,
#     `macro_rules`, `elab` and `syntax` are all refused here).
#   * a command keyword that is ALSO a term or tactic word would be a FALSE
#     POSITIVE at an indented line head, which is the loud direction and is
#     measured at zero on this library today.
#   * the blind spots `strip_comments` lists.
_KEYWORDS = []
# A `def` in the toolchain's parser sources: its attribute block, its name
# (possibly «»-escaped) and its body, up to the next command.
CORE_DEF = re.compile(
    r"(?m)^(?:@\[([^\]]*)\][ \t\r\n]*)?def[ \t]+"
    r"(«[^»]+»|[A-Za-z_][A-Za-z0-9_'.]*)[ \t]*(?::[^\n]*)?:="
    r"([\s\S]*?)(?=\n(?:@\[|def |/-|namespace |end |\Z))")
CORE_STR = re.compile(r'"([^"\\\n]*)"')
CORE_ESC = re.compile(r"«([^»]+)»")
CORE_REF = re.compile(r"(?<![\w'?!.])([A-Za-z_][A-Za-z0-9_'.]*)")
# A COMMAND KEYWORD, and the leading `#` is Lean's, not a decoration (W-31
# repair, gap 2255).  Twenty-seven of the pinned toolchain's command keywords
# begin with one -- thirteen from the `@[builtin_command_parser] def` half
# (`#eval`, `#print`, `#check`, `#synth`, `#exit`, ..) and fourteen from the
# `: command` syntax half (`#reduce`, `#guard_msgs`, ..) -- and this filter
# dropped every one of them, which is why `COMMAND_WORD`'s widening alone left
# the indented spelling open.  118 keywords before, 145 after; the floors below
# name a `#` member of each half so the class cannot quietly narrow again.
KEYWORD = re.compile(r"^#?[A-Za-z_][A-Za-z0-9_']*$")
# The parser combinators, which are references and not keywords.  A name that is
# not one of these and not a parser this scan saw is simply ignored, so the list
# only ever costs a keyword it cannot reach -- never a false one.
CORE_COMB = {"leading_parser", "trailing_parser"}
# A SYNTAX DECLARATION's head: the declaring command, through its modifiers and
# its attribute block.  `scoped`/`local`/`builtin`/`private`/`protected` are the
# modifiers this toolchain spells in front of one.
CORE_SYNTAX = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t\r\n]*)?"
    r"(?:(?:scoped|local|private|protected|builtin)[ \t]+)*"
    r"(?:syntax|macro|elab)(?![\w'!?])")
# A string literal, ESCAPES INCLUDED -- the masking below must not stop inside
# one, or a head holding `" := "` would be cut in the wrong place.
CORE_STRQ = re.compile(r'"(?:[^"\\\n]|\\.)*"')
# The category a syntax declaration declares INTO, at the end of its head.
CORE_CAT = re.compile(r":[ \t]*command[ \t]*$")


def _syntax_head(text, start):
    """The declaration head at `start`: its own line and indented continuations,
    cut at the `=>` that ends it, with string literals MASKED."""
    rest = text[start:start + 4000]
    masked = CORE_STRQ.sub(lambda m: '"' + "@" * (len(m.group(0)) - 2) + '"', rest)
    acc = ""
    for k, line in enumerate(masked.split("\n")):
        if k and (line[:1] not in (" ", "\t") or "=>" in acc):
            break
        acc = line if not k else acc + "\n" + line
    if "=>" in acc:
        acc = acc[:acc.index("=>")]
    return acc, rest


def _syntax_command_keywords(text):
    """Every keyword a `: command` syntax declaration in `text` consumes first."""
    for m in CORE_SYNTAX.finditer(text):
        head, rest = _syntax_head(text, m.end())
        if not CORE_CAT.search(head.rstrip()):
            continue
        lit = CORE_STRQ.search(rest[:len(head)])
        if lit:
            word = lit.group(0)[1:-1].strip()
            if KEYWORD.match(word):
                yield word


def command_keywords():
    """Every word Lean's own grammar declares a COMMAND by, from the pin.

    A hard error rather than an empty set: a residue over no keywords reports
    nothing, and a gate that reports nothing is how this campaign's defects have
    always looked from the outside.  The floor below is the assertion that the
    derivation still works against the toolchain it is pointed at."""
    if _KEYWORDS:
        return _KEYWORDS[0]
    src = leanfiles.toolchain_src()
    parsers, commands, from_syntax = {}, [], set()
    for path in sorted(src.rglob("*.lean")):
        text = path.read_text(encoding="utf-8", errors="replace")
        has_parser = "command_parser" in text
        if ": command" in text or ":command" in text:
            from_syntax.update(_syntax_command_keywords(text))
        if not has_parser:
            continue
        for m in CORE_DEF.finditer(text):
            attr, name, body = m.group(1) or "", m.group(2), m.group(3)
            parsers[name.strip("«»")] = body
            if "command_parser" in attr:
                commands.append((name, body))
    # A parser that is nothing but tokens: every literal in it is a keyword.
    tokens = {name for name, body in parsers.items()
              if CORE_STR.search(body)
              and not ({r.group(1) for r in CORE_REF.finditer(CORE_STR.sub(" ", body))}
                       - CORE_COMB)}
    kws = set()
    for name, body in commands:
        bare = name.strip("«»")
        if name.startswith("«") and KEYWORD.match(bare):
            kws.add(bare)
        first = CORE_STR.search(body)
        if first and KEYWORD.match(first.group(1).strip()):
            kws.add(first.group(1).strip())
        for alt in CORE_ESC.finditer(body):
            if KEYWORD.match(alt.group(1)):
                kws.add(alt.group(1))
        for ref in CORE_REF.finditer(CORE_STR.sub(" ", body)):
            if ref.group(1) in tokens:
                for lit in CORE_STR.finditer(parsers[ref.group(1)]):
                    if KEYWORD.match(lit.group(1).strip()):
                        kws.add(lit.group(1).strip())
    # THE FLOOR, AND IT IS ONE PER DERIVATION (W-30 repair, gap 2125).  Not a
    # second list of what is banned -- these are the commands W-29 and W-30 each
    # DROVE an escape with, plus the declaration keywords every Lean file
    # spells.  Asserting the union would let EITHER derivation rot silently
    # while the other carried the floor, which is how the parser-`def` half came
    # to be the only half: each floor is checked against its OWN source, so a
    # derivation that has stopped working says so here instead of reporting a
    # clean library.
    parser_floor = {"macro", "macro_rules", "syntax", "elab", "notation",
                    "initialize", "builtin_initialize", "attribute", "theorem",
                    "abbrev", "instance", "namespace", "section", "end", "open",
                    "set_option",
                    # W-31 repair, gap 2255.  `#eval` elaborates arbitrary
                    # `CommandElabM` -- it is `run_cmd` by another spelling and
                    # a NEW AXIOM was driven past every gate with it.  `#print`
                    # is the one this kernel uses; the other three are here so
                    # that a `KEYWORD` class that narrows back to `[A-Za-z_]`
                    # fails loudly instead of reporting a clean library.
                    "#eval", "#print", "#check", "#synth"}
    # Declared `syntax .. : command` (the first four) and `macro .. : command`
    # (`register_builtin_option`, which this file's own header used to name as
    # covered and was not).  `run_cmd`, `run_elab` and `run_meta` each elaborate
    # arbitrary `CommandElabM`, which is how a NEW AXIOM was driven past every
    # gate in this tree.
    syntax_floor = {"run_cmd", "run_elab", "run_meta", "unseal", "seal",
                    "test_extern", "reprove", "register_builtin_option",
                    # The `#`-commands this half declares (W-31, gap 2255).
                    "#reduce", "#guard_msgs"}
    for what, got, floor, least in (
            ("@[builtin_command_parser] def", kws, parser_floor, 40),
            ("a `: command` syntax declaration", from_syntax, syntax_floor, 50)):
        if not floor <= got or len(got) < least:
            raise SystemExit(
                "totality.py: the command-keyword derivation no longer reads %s "
                "out of %s -- %d keywords, missing %s.  The residue below would "
                "be silent." % (what, src, len(got), sorted(floor - got)))
    _KEYWORDS.append(frozenset(kws | from_syntax))
    return _KEYWORDS[0]

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

PKG = pathlib.Path(__file__).resolve().parent / "TmKernel"
IMPORT_LINE = re.compile(
    r"(?m)^[ \t]*(?:public[ \t]+|meta[ \t]+|private[ \t]+)*import[ \t]+(?:all[ \t]+)?(\S+)")

KERNEL_DECIDE = re.compile(r"\bdecide\b[ \t]*(?:\+kernel\b|\([^)]*\bkernel[ \t]*:=[ \t]*true)")
DECL_BEFORE = re.compile(r"(?<![\w'?!.\u00AB])(?:theorem|def|abbrev|instance)[ \t\r\n]+([^\s(){}:]+)")
KERNEL_DECIDE_FILE = pathlib.Path(__file__).resolve().parent / "kernel-decide-exempt.txt"


def read_exempt(text):
    return {ln.strip() for ln in text.splitlines()
            if ln.strip() and not ln.lstrip().startswith("#")}


kernel_decide_exempt = read_exempt(KERNEL_DECIDE_FILE.read_text()) \
    if KERNEL_DECIDE_FILE.is_file() else set()
seen_kernel_decide = set()

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
    # THE COMMAND RULE (W-29): the word at a COMMAND POSITION is a command this
    # kernel uses, or it is named here.  It is the net under the members of R4's
    # class nobody has thought of yet -- `partial_fixpoint` was one, and it went
    # green under a list of five spellings.
    for off, word, certain in command_positions(code):
        if word in ALLOWED_COMMANDS:
            continue
        if certain:
            hits.add((bisect.bisect_right(nl, off) + 1,
                      "`%s` stands where a command begins and is not in "
                      "ALLOWED_COMMANDS (R4: a command this kernel does not "
                      "use)" % word))
        elif word in command_keywords():
            # THE INDENTED HALF (W-30).  Lean lets a command begin at any
            # column; this position may be a proof step instead, so the rule is
            # not "in ALLOWED_COMMANDS" but "not a command Lean declares".
            hits.add((bisect.bisect_right(nl, off) + 1,
                      "`%s` is a COMMAND keyword of the pinned toolchain "
                      "standing at an indented command position, and is not in "
                      "ALLOWED_COMMANDS (R4: a command this kernel does not "
                      "use, spelled with a leading space)" % word))
    # THE IMPORT RULE (W-34 repair, README gap 2730).  A kernel file imports
    # the kernel's own modules and nothing else -- a PROPERTY of the import
    # line, not a list of forbidden packages.  `import Lean` put `Lean.addDecl`
    # and withOptions in scope, and run_tac -- a TACTIC, which no command
    # rule above reads -- used them to add `Tm.v34Bad : False` with
    # `debug.skipKernelTC` set, so `theorem v34_one_is_two : (1:Nat) = 2`
    # passed all thirteen checks (driven at `fb05f4e` in a clone; without the
    # import line the same file fails at `Unknown constant
    # Lean.Elab.Tactic.TacticM`).  Every live import is `TmKernel` or
    # `TmKernel.<Mod>` today, so the rule costs nothing.  Check 14
    # (`replay.py`) is the semantic half and does not care how a declaration
    # got in.
    for m in IMPORT_LINE.finditer(code):
        target = m.group(1)
        parts = target.split(".")
        if not (parts[0] == PKG.name
                and (len(parts) == 1 and (PKG / (PKG.name + ".lean")).is_file()
                     or PKG.joinpath(*parts).with_suffix(".lean").is_file())):
            hits.add((bisect.bisect_right(nl, m.start()) + 1,
                      "import %s -- a kernel file imports the kernel's own "
                      "modules only (R2/R6: an outside module puts the "
                      "metaprogramming API in scope)" % target))
    # THE KERNEL-DECIDE RULE (W-34 repair, README gap 2732).  AGENTS §5.10a:
    # "never reach for `decide +kernel` on a large computation -- it removes the
    # one budget there is", and a cap kill is answered by shrinking the input or
    # deriving the fact.  W-34 answered an 8 GB elaborator kill with exactly
    # that tactic, over the whole planner, and nothing read the rule.  The
    # property: a proof that switches the elaborator's decision off stands only
    # in a declaration `kernel-decide-exempt.txt` names, and that file may only
    # SHRINK (held against its committed self below).
    for m in KERNEL_DECIDE.finditer(code):
        decl = DECL_BEFORE.findall(code, 0, m.start())
        where = "%s.%s" % (p.stem, decl[-1] if decl else "?")
        seen_kernel_decide.add(where)
        if where not in kernel_decide_exempt:
            hits.add((bisect.bisect_right(nl, m.start()) + 1,
                      "`decide +kernel` in %s -- not in kernel-decide-exempt.txt "
                      "(AGENTS §5.10a: shrink the input or derive the fact)" % where))
    for n, name in sorted(hits):
        print(f"{p}:{n}: banned: {name}")
        bad += 1
# The exemption file's two directions.  A line naming no live site is STALE
# (the file may only shrink, so a fixed site takes its line with it), and a
# line the COMMITTED file does not hold is growth, which fails whatever it says
# -- the ratchet `reach.py` learned at W-31 (gap 2259): a count held against
# itself is not a ratchet.
for where in sorted(kernel_decide_exempt - seen_kernel_decide):
    print("%s: STALE: %s has no `decide +kernel` -- delete its line"
          % (KERNEL_DECIDE_FILE.name, where))
    bad += 1
try:
    import subprocess
    head = subprocess.run(["git", "-C", str(KERNEL_DECIDE_FILE.parent), "show",
                           "HEAD:./" + KERNEL_DECIDE_FILE.name],
                          capture_output=True, text=True, timeout=60)
    committed = read_exempt(head.stdout) if head.returncode == 0 else None
except (OSError, subprocess.SubprocessError):
    committed = None
if committed is not None:
    for where in sorted(kernel_decide_exempt - committed):
        print("%s: GROWTH: %s is not in the committed file -- it may only shrink"
              % (KERNEL_DECIDE_FILE.name, where))
        bad += 1
sys.exit(1 if bad else 0)
