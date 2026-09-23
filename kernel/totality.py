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
RECURSIVELY, with `.lake`, `target` and `.git` pruned.  `check.sh` passes both
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
import re, sys, pathlib

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
# Listed by name so that a `sorry` in any real module is still caught.
EXEMPT = {"Goals.lean"}

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
CHAR_LIT = re.compile(r"'(?:\\.|[^'\\])'")
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
BANNED = [
    (r"partial\s+def", "partial def"),
    (r"panic!", "panic!"),
    (r"native_decide", "native_decide"),
    (r"\bsorry\b", "sorry"),
    (r"(?<=[A-Za-z0-9_'\]])(?<!panic)!(?!=)", "`!`-accessor (R4)"),
    (r"\bunsafe\b", "unsafe (R4)"),
    (r"\bopaque\b", "opaque (R4)"),
    (r"\bimplemented_by\b", "@[implemented_by] (R4)"),
    (r"\.toOption", ".toOption"),
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
# path -> is it at the ROOT of any directory named on the command line.  A dict
# and not a set of pairs: `check.sh` passes `TmKernel/TmKernel` AND `TmKernel`,
# so with the recursion every library file is reached twice -- at the root of
# the first and one level down from the second -- and a set of (path, at_root)
# pairs holds both, which scans every library file twice and double-counts
# every banned line it finds.
files = {}
for d in sys.argv[1:]:
    root = pathlib.Path(d)
    for p in leanfiles.lean_files(root):
        files[p] = files.get(p, False) or p.parent == root
for p in sorted(files):
    if files[p] and p.name in EXEMPT:
        continue
    src = p.read_text()
    src = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), src, flags=re.S)
    for n, line in enumerate(src.splitlines(), 1):
        code = line.split("--")[0]
        code = CHAR_LIT.sub("''", code)
        code = INTERP.sub(lambda m: m.group(1) + " ", code)
        for pat, name in BANNED:
            if re.search(pat, code):
                print(f"{p}:{n}: banned: {name}")
                bad += 1
sys.exit(1 if bad else 0)
