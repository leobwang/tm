#!/usr/bin/env python3
"""check.sh's check 10: the PARITY register has one home, and it is checked.

A parity entry is a recorded divergence between this branch and the fork point
`4748911` (owner D21/D22): the comparand is outside the tree, every difference
must be on the list with the decision behind it, and stage 5's acceptance is
that list.  It had no single home and no gate, and it cost a duplicate TWICE:

  * **P32**, five months of blocks apart, by two tracks -- README gap 226.
  * **P38**, at W-24 track A -- README gap 1417.  Gap 402's block had taken it;
    four later blocks wrote "P38 still free"; track A believed the later ones.

AGENTS 6.5 item 7 gave the merge a COMMAND after the second duplicate, and said
in the same breath why it is not a gate: a `P<n>` in this repository is also a
stage-6 STEP name (P0-P8, and track P itself), so no regex over `P<n>` can tell
an issuance from a reference.  THAT IS TRUE, AND IT IS THE REASON FOR AN INDEX
RATHER THAN THE REASON FOR NOTHING.  `parity.txt` is the index -- one row per
number, naming the file and LINE where the entry is recorded -- and this file
re-resolves every anchor without building anything, exactly as `mutate.py`'s
`stale_sites` re-resolves a pin site.

WHAT §6.5's COMMAND COULD NOT SEE, measured at W-25 track A before this existed:

    grep -noE '\\*\\*Parity P[0-9]+ taken\\*\\*|^\\| \\*\\*P[0-9]+\\*\\* \\|' README.md

  * It required the register row to be **BOLD**, and the FIRST TWELVE are not:
    `| P1 |` ... `| P12 |` at README.md:7836-8477 are plain.  Twelve of the
    thirty-nine numbers in use were invisible to the reconciliation written to
    find them.
  * It matched the P38 issuance INSIDE BACKTICKS in the W-24 repair block's own
    prose, so on the repaired tree it reported P38 twice -- a quotation counted
    as an issuance.  Inline code is stripped here before anything is matched.
  * It read README.md alone.  **P13, P22, P28, P29 and P31 have never had a
    README row** (their home is design §17's table) and **P36 has never had a
    row anywhere**: its only record is a comment in `Replay.lean` and one in
    `Log.lean`.  Gap 226 said the list lives in three places and named the
    code as one of them; gap 1417's measurement dropped that place and
    concluded 17 numbers were "not locatable mechanically".  They are all
    locatable; what was missing was a list of where to look.

THE THREE IDIOMS, an ALLOW-LIST and not a pattern (check 8's discipline):

    taken   `**Parity P<n> taken**` at column zero -- the CANONICAL ISSUANCE
            line.  A block that takes a number writes this, and nothing else
            counts as taking one.
    row     `| P<n> |` or `| **P<n>** |` at column zero -- a register table row.
    cite    `parity ... P<n>` in prose or in a source comment.

A row names which idiom to expect, so a line that drifts FAILS rather than
resolving to something else.

WHAT THIS CANNOT SEE.  Measured or argued, never guessed:
  * A NUMBER NOBODY INDEXED, IN A FILE THE INDEX DOES NOT NAME.  The files read
    are README.md plus whatever the index anchors point into -- three today.  A
    register row or an issuance line in a fourth file is invisible, and that is
    why the two SUPERSEDED draft numberings in `design/stage5/` are named in
    `parity.txt`'s header rather than left to be rediscovered.  Inside the files
    it does read, an unindexed number is caught in both spellings: a planted
    `| **P41** |` row with no issuance line and no index row went GREEN until
    the row half of the check below was added.  What stops the index going quietly
    short is `--gate`'s CONTIGUITY check: the rows must cover P1..Pmax with no
    gap unless the gap carries a `hole P<n> <why>` line of its own.  An index
    17 numbers short cannot pass, which is exactly what gap 1417 describes.
  * A LINE ANCHOR DRIFTS.  README.md is append-only (AGENTS 6.4) so its numbers
    are stable, but a design doc edited above an anchor moves it.  That FAILS
    here, by name, and the fix is to re-anchor the row -- it is never silent.
  * THE STATEMENT COLUMN IS PROSE AND NOTHING CHECKS IT.  A row whose sentence
    no longer describes the entry is invisible, the same way `mutations.txt`'s
    fifth column is a claim until `--verify` re-runs it.
  * A STEP NAME IS STILL A STEP NAME.  This does not try to classify the 1,400
    bare `P<n>` mentions in the ledger, and it is not a spell-checker for them;
    it makes the register enumerable, which is what "the next free number" needs.
"""

import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
INDEX = os.path.join(HERE, "parity.txt")

IDIOMS = {
    "taken": lambda n: re.compile(r"^\*\*Parity P%d taken\*\*" % n),
    "row": lambda n: re.compile(r"^\| \*{0,2}P%d(?: \(refined\))?\*{0,2} \|" % n),
    "cite": lambda n: re.compile(r"[Pp]arity (?:entry |entries )?\*{0,2}P%d\b" % n),
}

# The canonical issuance line, for ANY number: what a new block writes, and the
# one spelling a duplicate is checked over.
TAKEN = re.compile(r"^\*\*Parity P(\d+) taken\*\*")

# Any register-table row, for the "no unregistered number" half.
ANY_ROW = re.compile(r"^\| \*{0,2}P(\d+)(?: \(refined\))?\*{0,2} \|")

INLINE_CODE = re.compile(r"`[^`]*`")


def read(path):
    with io.open(path, encoding="utf-8") as handle:
        return handle.read()


def strip_code(line):
    """Inline code is a QUOTATION, not an issuance.  §6.5's command missed this
    and reported P38 twice on the tree its own repair had just fixed."""
    return INLINE_CODE.sub("", line)


def index():
    """([(n, idiom, file, line, text)], {n: why}) from parity.txt."""
    rows, holes = [], {}
    for raw in read(INDEX).split("\n"):
        line = raw.split("#", 1)[0].strip() if raw.startswith("#") else raw.rstrip()
        if not line.strip():
            continue
        fields = line.split(None, 3)
        if fields[0] == "hole":
            holes[int(fields[1][1:])] = fields[2] if len(fields) > 2 else ""
            continue
        if not re.match(r"^P\d+$", fields[0]):
            continue
        n = int(fields[0][1:])
        idiom = fields[1]
        where, _, at = fields[2].rpartition(":")
        rows.append((n, idiom, where, int(at), fields[3] if len(fields) > 3 else ""))
    return rows, holes


def main(argv):
    rows, holes = index()
    bad = []

    seen = {}
    for n, idiom, where, at, _ in rows:
        if n in seen:
            bad.append("P%d has TWO index rows (%s:%d and %s:%d)"
                       % (n, seen[n][0], seen[n][1], where, at))
        seen[n] = (where, at)
        if idiom not in IDIOMS:
            bad.append("P%d names an idiom this file does not know: %r" % (n, idiom))

    # **CONTIGUITY**: the index is a closed enumeration or it is decoration.
    top = max(seen) if seen else 0
    for n in range(1, top + 1):
        if n not in seen and n not in holes:
            bad.append("P%d is in neither the index nor the declared holes -- "
                       "the register is short, which is README gap 1417's own "
                       "shape" % n)

    # **EVERY ANCHOR RE-RESOLVES**, without a build.
    cache, files = {}, set()
    for n, idiom, where, at, _ in rows:
        if idiom not in IDIOMS:
            continue
        path = os.path.join(HERE, where)
        files.add(where)
        if where not in cache:
            if not os.path.exists(path):
                bad.append("P%d names %s, which does not exist" % (n, where))
                cache[where] = []
                continue
            cache[where] = read(path).split("\n")
        lines = cache[where]
        if at < 1 or at > len(lines):
            bad.append("P%d names %s:%d, past the end of the file" % (n, where, at))
            continue
        if not IDIOMS[idiom](n).search(strip_code(lines[at - 1])):
            bad.append("P%d: %s:%d no longer carries a `%s` for it -- re-anchor "
                       "the row" % (n, where, at, idiom))

    # **THE CANONICAL ISSUANCE LINE IS UNIQUE AND REGISTERED**, and **NO REGISTER
    # ROW NAMES A NUMBER THE INDEX DOES NOT HOLD**.  The second half was added
    # after a planted probe went GREEN without it: `| **P41** |` appended to
    # README.md with no issuance line and no index row passed, which is an
    # instance of exactly the class this gate exists to catch.  It reads the
    # NUMBER and not the row, because P1 legitimately has two rows (plain and
    # refined) and README.md carries a `| P33 |` row that is a DENOMINATOR in a
    # coverage table rather than a register row -- both are numbers the index
    # already holds, so neither has to be exempted by name.
    issued = {}
    rows_seen = 0
    for where in sorted(files | {"README.md"}):
        path = os.path.join(HERE, where)
        if not os.path.exists(path):
            continue
        for i, line in enumerate(read(path).split("\n"), 1):
            clean = strip_code(line)
            m = TAKEN.match(clean)
            if m:
                n = int(m.group(1))
                if n in issued:
                    bad.append("P%d is TAKEN twice: %s:%d and %s:%d"
                               % (n, issued[n][0], issued[n][1], where, i))
                issued[n] = (where, i)
                if n not in seen:
                    bad.append("P%d is taken at %s:%d and has NO index row"
                               % (n, where, i))
            m = ANY_ROW.match(clean)
            if m:
                rows_seen += 1
                n = int(m.group(1))
                if n not in seen and n not in holes:
                    bad.append("%s:%d carries a register row for P%d and the "
                               "index has none" % (where, i, n))

    if bad:
        print("%d parity register problem(s):" % len(bad))
        for why in bad:
            print("  %s" % why)
        return 1
    by = {}
    for _, idiom, _, _, _ in rows:
        by[idiom] = by.get(idiom, 0) + 1
    print("%d registered (P1-P%d%s), %d anchor(s) re-resolved in %d file(s) "
          "(%s), %d register row(s) and %d canonical issuance line(s) read, "
          "next free P%d"
          % (len(rows), top, "" if not holes else ", %d declared hole(s)" % len(holes),
             len(rows), len(files),
             ", ".join("%d %s" % (v, k) for k, v in sorted(by.items())),
             rows_seen, len(issued), top + 1))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
