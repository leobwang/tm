#!/usr/bin/env python3
"""The kernel must be total.

A Lean panic prints a C backtrace to stderr, returns `Inhabited.default`, and
gives the host exit code 0 -- a silent wrong answer, which is the exact failure
class this rebuild exists to remove.  `lean_set_exit_on_panic(true)` is no
better: it is exit(1) with no unwind, so a ratatui terminal is left in raw mode.
So the kernel is total instead, and this enforces it.

`.toOption` is banned for the same reason at the boundary: it is how the FFI
spike silently turned `est: -3` into `est: null`.
"""
import re, sys, pathlib

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
for p in sorted(pathlib.Path(sys.argv[1]).glob("*.lean")):
    src = p.read_text()
    src = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), src, flags=re.S)
    for n, line in enumerate(src.splitlines(), 1):
        code = line.split("--")[0]
        for pat, name in BANNED:
            if re.search(pat, code):
                print(f"{p}:{n}: banned: {name}")
                bad += 1
sys.exit(1 if bad else 0)
