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

AND THE EXEMPTION NARROWED WITH IT.  `Goals.lean` is exempt only AT THE ROOT of
a directory named on the command line; a `Sub/Goals.lean` is scanned like any
other file.  Without that test the recursion would have widened the one
exemption into a directory anybody could create.
"""
import re, sys, pathlib

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

BANNED = [
    (r"partial\s+def", "partial def"),
    (r"panic!", "panic!"),
    (r"native_decide", "native_decide"),
    (r"\bsorry\b", "sorry"),
    (r"\]!", "list index `[..]!`"),
    (r"\.get!", ".get!"),
    (r"\.toOption", ".toOption"),
]

# Build directories and checkouts, never sources.  There are 0 `.lean` files
# under `kernel/TmKernel/.lake` today; pruning is what keeps a future layout --
# or a vendored toolchain -- from being scanned as if it were this kernel.
PRUNE = {".lake", "target", ".git"}

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
    for p in root.rglob("*.lean"):
        if PRUNE & set(p.parts):
            continue
        files[p] = files.get(p, False) or p.parent == root
for p in sorted(files):
    if files[p] and p.name in EXEMPT:
        continue
    src = p.read_text()
    src = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), src, flags=re.S)
    for n, line in enumerate(src.splitlines(), 1):
        code = line.split("--")[0]
        for pat, name in BANNED:
            if re.search(pat, code):
                print(f"{p}:{n}: banned: {name}")
                bad += 1
sys.exit(1 if bad else 0)
