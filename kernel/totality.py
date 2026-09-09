#!/usr/bin/env python3
"""The kernel must be total.

A Lean panic prints a C backtrace to stderr, returns `Inhabited.default`, and
gives the host exit code 0 -- a silent wrong answer, which is the exact failure
class this rebuild exists to remove.  `lean_set_exit_on_panic(true)` is no
better: it is exit(1) with no unwind, so a ratatui terminal is left in raw mode.
So the kernel is total instead, and this enforces it.

`.toOption` is banned for the same reason at the boundary: it is how the FFI
spike silently turned `est: -3` into `est: null`.

Usage: `totality.py <dir> [<dir> ...]`.  Each directory is scanned one level
deep, non-recursively.  `check.sh` passes both `TmKernel/TmKernel` (the library)
and `TmKernel` (the package root, which holds `Check.lean`, `Negative.lean` and
`Goals.lean`), so the exemption below is load-bearing rather than decorative.
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

bad = 0
files = sorted({p for d in sys.argv[1:] for p in pathlib.Path(d).glob("*.lean")})
for p in files:
    if p.name in EXEMPT:
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
