#!/usr/bin/env python3
"""Every `#[ignore]`d ORACLE ARM of the workspace, read off the test sources.

run-oracle.sh's input set 7 runs what this prints.  The W-46 audit (README gap
4896) found the script's six sets a LIST where the rule is a CLASS: track C moved
eleven test targets' comparands to `tm-oracle capacity` and none of them was in
the script, so "the whole sweep in one command" ran a part of it.  This reads
the class instead: a test function under `#[ignore]` whose body asks the oracle
(`TM_ORACLE`, or a helper named `oracle`) and is not a bless (a bless rewrites a
committed fixture, which is a decision and never part of a sweep, AGENTS §7.2 —
each needs a `*_BLESS` variable as well and is inert here anyway).

Prints one line per arm: `<package> <test target> <function>`.  A proptest arm
(`fn name(bytes in …)` inside `proptest!`) is printed like any other: cargo's
filter matches its name.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
TARGETS = [("tm", ROOT / "tm" / "tests"), ("tm-core", ROOT / "tm-core" / "tests")]
FN = re.compile(r"^\s*(?:pub\s+)?fn\s+([a-z0-9_]+)\s*\(")


def arms(path: Path):
    lines = path.read_text().splitlines()
    out = []
    for i, line in enumerate(lines):
        if not re.match(r"^\s*#\[ignore", line):
            continue
        # The function the attribute stands on: the next `fn` line.
        j = i + 1
        while j < len(lines) and not FN.match(lines[j]):
            j += 1
        if j == len(lines):
            continue
        name = FN.match(lines[j]).group(1)
        # Its body: up to the next attribute-led test or the next top-level item.
        k = j + 1
        while k < len(lines) and not re.match(r"^\s*(#\[test\]|#\[ignore|fn |pub fn |///)", lines[k]):
            k += 1
        body = "\n".join(lines[j:k])
        if "oracle" not in body.lower():
            continue
        if "bless" in name or "redrawn" in name or re.search(r'env::var(?:_os)?\(\s*"TM_[A-Z_]*BLESS', body):
            continue
        out.append(name)
    return out


def main() -> int:
    for package, d in TARGETS:
        for f in sorted(d.glob("*.rs")):
            for name in arms(f):
                print(package, f.stem, name)
    return 0


if __name__ == "__main__":
    sys.exit(main())
