#!/usr/bin/env python3
"""Two names for ONE definition: the §5.3 sweep, as a SCRIPT.

AGENTS §5.3 is the rule this kernel is named after -- two definitions of one
concept is the bug -- and track A has swept for it by hand at several steps.
W-29's audit found the cost of hand-sweeping: the run reported *"seventeen
groups, all seventeen accounted for"*, and **five character-identical `def`
pairs were in none of them**, each pair joined by a `@[csimp]` proved by a bare
`rfl`:

    Tm.planWf      (Plan.lean)     / Tm.planWfFast      (Fast.lean)
    Tm.edf         (Capacity.lean) / Tm.edfFast         (Capacity.lean)
    Tm.edfGrants   (Capacity.lean) / Tm.edfGrantsFast   (Capacity.lean)
    Tm.daysIn      (Seal.lean)     / Tm.daysInT         (SealTwin.lean)
    Tm.daysFrom    (Seal.lean)     / Tm.daysFromT       (SealTwin.lean)

**The sweep was hand-run and no script was committed, so the number could not be
re-measured.**  That is the defect this file removes: the sweep is a program, it
is in the repository, and the next step runs it instead of believing a sentence.

WHAT IT IS.  Every `def` of the library, its BODY normalised to its non-space
characters, grouped by that body.  A group of more than one is two names for one
definition -- the exact shape §5.3 bans -- and it is printed with its members.
The body is everything from the `:=` that opens it to the start of the next
command position, which is `totality.py`'s own rule imported rather than
restated.

WHAT IT CANNOT SEE, and the list matters because the hand sweep's own declared
blind spot is where four of the five above hid:

  * a duplicate that reaches its own auxiliary BY NAME (`edf` calls `edfCaps`,
    `edfFast` calls `edfCapsFast`) -- the bodies differ in one identifier, so
    this file reports the AUXILIARIES as the twins and not the callers.  It is
    still named, one level down.
  * a duplicate whose bodies differ by a `let` hoist or an argument order
    (`Tm.sitesInRange` / `sitesInRangeFast` hoists `let n := p.docs.length`) --
    NOT character-identical, and a `@[csimp]`-proved-by-`rfl` grep alone is not
    the rule either.
  * a duplicate spelled as a `theorem`, an `abbrev` or an `instance`.  `def` is
    the population this run's finding is about; widening it is the next step's.
  * a duplicate across the Rust and the Lean sides.

USAGE: `twins.py [<dir> ...]` (default: the library).  It PRINTS and exits 0;
it is a sweep, not a gate -- several of the pairs above are deliberate
`@[csimp]` fast/slow shells whose bodies have converged, and turning this into a
check would need an exemption LIST, which is the shape this campaign keeps
finding wrong.  The gate it should become is one that states why a pair is
allowed to exist; README gap 2017 carries that.
"""
import collections
import pathlib
import re
import sys

import leanfiles

# A `def`'s name, as a keyword TOKEN (`leanfiles.THEOREM`'s discipline).
DEF = re.compile(r"(?<![\w'?!.«])def[ \t\r\n]+([^\s(){}:]+)")
# Where a command begins again: a non-space character in column zero.
NEXT_COMMAND = re.compile(r"(?m)^\S")


def bodies(path):
    """`(name, normalised body)` for every `def` declared in `path`."""
    code = leanfiles.strip_comments(pathlib.Path(path).read_text())
    for m in DEF.finditer(code):
        stop = NEXT_COMMAND.search(code, m.end())
        chunk = code[m.end():stop.start() if stop else len(code)]
        head, sep, tail = chunk.partition(":=")
        if not sep:
            continue  # a `def .. where` or a pattern match: no single body
        yield m.group(1), "".join(tail.split())


def main(argv):
    roots = argv or [str(pathlib.Path(__file__).resolve().parent / "TmKernel")]
    groups = collections.defaultdict(list)
    files = set()
    for d in roots:
        files.update(leanfiles.lean_files(pathlib.Path(d)))
    for p in sorted(files):
        for name, body in bodies(p):
            if body:
                groups[body].append("%s:%s" % (p, name))
    twins = {b: ns for b, ns in groups.items() if len(ns) > 1}
    for body in sorted(twins, key=lambda b: (-len(twins[b]), b)):
        print("twin body (%d chars): %s" % (len(body), body[:70]))
        for n in twins[body]:
            print("    %s" % n)
    print("%d file(s) swept, %d def bodies, %d group(s) of two or more names"
          % (len(files), sum(len(v) for v in groups.values()), len(twins)))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
