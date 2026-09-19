#!/usr/bin/env python3
"""check.sh's check 8 (D39): resolve the identifiers the prose CITES.

Five consecutive runs of the stage-6 campaign shipped a stale prose citation --
a doc comment or a README line naming a theorem that had been deleted or
renamed -- and every one was found by hand by an independent auditor, because
no check in check.sh reads a doc comment.  Check 3 reads `#print axioms` lines
and says so in its own comment; check 4 reads `/- CHEAT` headers.  Nothing read
the sentences.  That is README gap 779, and this is the check that ends it.

WHAT IS SWEPT.  Every backticked span on one line of

    kernel/TmKernel/TmKernel/*.lean   the library
    kernel/TmKernel/*.lean            Check, Negative, Goals, TmKernel
    kernel/README.md                  the ledger

whose content is a dotted identifier with at least one underscore in it -- the
shape this kernel's theorem names have.  camelCase `def`s are NOT swept; see
"WHAT THIS CANNOT SEE" below.

WHAT IT RESOLVES AGAINST.  Five declaration sets, in this order.  None of them
is prose: every one is a place where the name is *declared*, so resolving
against it cannot launder one stale sentence with another.

    1. Lean declarations -- theorem/lemma/def/abbrev/structure/inductive/
       instance/class/example/opaque/axiom in the files above, plus the fields
       of a `structure` and the constructors of an `inductive`.
    2. Lean string literals in those files.  A wire key, a refusal tag and a
       JSON field name are declared by the literal that spells them, and
       `"cap_done_min"` in Boundary.lean is that declaration.
    3. Rust declarations -- fn/struct/enum/const/static/type/trait/mod/union
       and struct fields -- in tm/src, tm-core/src, tm/tests, tm-core/tests and
       kernel/tm-kernel-ffi/{src,tests,examples}.  The FORK's planner is
       in-tree (tm-core/src/planner.rs), so `place_mandatory_and_pref` and
       `active_run` resolve here and need no exemption.
    4. Rust string literals in those files.
    5. File stems under tm/, tm-core/ and kernel/ (target/ and .lake/ pruned).
       `cargo test --test cli_latency` names a FILE, and tm/tests/cli_latency.rs
       is where that name is declared; so are the snapshot stems the README
       quotes and the corpus documents.

A citation resolves if its LAST dotted segment is in any of the five.

THE ALLOW-LIST IS MATCHED ON THE WHOLE SPAN, not on the last segment, and the
two rules are deliberately different.  `energy.sort_by_key` and `out.sort_by`
each need their own entry; an entry `sort_by` exempts nothing.  That is the
safe direction -- an exemption cannot silence the same method on a different
receiver -- but it is not guessable, and the W-19 merge lost a cycle to it.

THE ALLOW-LIST IS THE REST, AND IT IS EXACT NAMES, NEVER PATTERNS.  A regex
that silenced a class -- "anything ending _min", "anything the sentence calls a
fork function" -- would make this check quietly useless, because the next stale
citation would land inside the silenced class.  Every exemption is a literal
name, in citations-allow.txt, under a heading that says what the category is.
The file has two syntaxes -- `name` (uncounted) and `N name` (at most N
occurrences across everything swept) -- and four commented sections:

    1. VOCABULARY, uncounted.  A real referent this kernel does not declare: a
       Lean core lemma, a chrono/serde/std item, a fork function, a config key.
    2. LIVE STALE CITATIONS found and NOT repaired, counted.  Declared as
       defects rather than laundered as exemptions; README gap 832 owes them.
    3. ADJUDICATED DEAD names, counted.  Opened at W-19: the sentence citing
       each one says it was refuted, renamed, retired, superseded or deleted.
       This check cannot read "refuted"; a human did, and that roster is here.
    4. GRANDFATHERED, counted.  A README baseline nobody has opened, so that
       this check could land as a RATCHET on new prose instead of a demand
       that an append-only ledger be rewritten.  README gap 833.

Counting is what makes 2, 3 and 4 safe: old prose keeps working, and a NEW
sentence that reaches for one of those names has to say so in a diff.  To cite
one once more, the honest moves are: open it, and either move it up to
VOCABULARY with a reason, or fix the sentence.  Bumping N without looking is
how this gets useless a second way.

WHAT THIS CANNOT SEE (README gap 831).  The first two bullets were guesses
until W-19's repair step MEASURED them; both numbers are re-takeable with the
resolver in this file and nothing else.
  * camelCase, MEASURED.  `loadPlan`, `readPlanFacts` and every field spelled in
    camel are not swept at all, so a stale `def` citation is invisible to it.
    The sweep is snake_case because that is the shape of a theorem name here and
    because D39 scoped it that way.  Reading camel too, over exactly this file
    set: 10,226 citations / 2,660 distinct / 1,120 unresolved (297 distinct) in
    the Lean files, and 16,962 / 3,785 / 2,356 (515 distinct) in README.md.
    That is why it is not merely a matter of widening the regex -- the top of
    that list is `decide` (x170 in Lean, x303 in the README), `rfl`, `Nat`,
    `Bool`, `sorry`, `lake`, hypothesis names (`hnopast` x20) and commit shas.
    A camelCase span is not distinguishable from tactic, type and prose
    vocabulary the way a snake_case one is, and an allow-list of 812 distinct
    names is the check being written twice.  Two REAL defects hid in there and
    both are named in README gap 880: `emitRefused` (Boundary.lean, a constant
    that never existed, present tense, repaired at W-19's repair step) and
    `eligibleAt` (x16 in Lean as `Planner.eligibleAt`, x26 in README.md), which
    is not stale but PROSPECTIVE and is owned by README gap 809.
  * The namespace.  Resolution is on the LAST dotted segment, so
    `Tm.Look.foo_bar` resolves against a `Tm.Cap.foo_bar` that still exists.
    A theorem moved between namespaces is invisible to it.
  * A name that is also a Rust name.  A deleted Lean theorem whose name is also
    a Rust fn or a JSON key still resolves, by source 3 or 4.
  * Fenced code blocks in the README.  They are skipped: they are pasted
    terminal output and past `check.sh` runs, a RECORD of what a command
    printed at a commit that has gone, and a check that demanded they resolve
    against today's tree would be demanding that the ledger be rewritten.  A
    stale citation inside a fence escapes.  (Measured at W-19: sweeping them
    too adds 2 unresolved names, both in quoted Lean output.)
  * Anything not in backticks.  A sentence that names a theorem in plain prose
    is not swept.  That is also the CONVENTION for a dead name (see
    citations-allow.txt's header): a sentence recording that something was
    refuted, renamed or deleted spells it without backticks, so it needs no
    exemption and a later sentence citing it as live still fails.
  * EVERY FILE OUTSIDE THE THREE SWEPT LOCATIONS -- AGENTS.md included.  D39
    scoped this check to the Lean library and kernel/README.md, so the PROCESS
    AUTHORITY is outside its own gate, and so is kernel/design/**, tm-spec-v1.md
    and PLAN-lean-kernel.md.  Measured at W-19's repair step by running this
    file's own resolver, same five declaration sets and same allow-list, over
    each of them: AGENTS.md 440 citations / 308 distinct / 3 distinct
    unresolved; kernel/design/** 1,855 / 687 / 144; tm-spec-v1.md 26 / 20 / 0;
    PLAN-lean-kernel.md 83 / 65 / 9.  AGENTS.md really did hold one
    (a_file_splits_into_the_lines_it_was_joined_from, repaired at W-19's repair
    step, live theorem `…_char`), which is the class D39 exists to end, one file
    outside its scope.  The design docs are NOT that class and must not be swept
    on these numbers: they are prospective specifications whose unresolved names
    are work to do -- `mkStateDay?` and `refuses_an_inverted_window` sit in the
    same table column as `refuses_a_day_past_9999` and are equally undeclared,
    because the column is headed "bound, constructor, rejection theorem" and the
    RuntimeIn that crosses today has none of those fields yet.  Widening the
    scope is an OWNER decision (D39 wrote the scope), not a repair step's.
    README gap 881.
  * The allow-list itself.  At the W-19 MERGE it holds 78 uncounted VOCABULARY
    names and 250 counted ones, and only 90 of the counted ones have been opened
    by anybody (sections 2 and 3); the 160 in section 4 are a seeded baseline and
    may hide stale citations nobody has found.  README gap 833.
  * ITS OWN HEADER.  The four numbers in the paragraph above are prose, not
    backticked identifiers, so this check cannot resolve them -- and all four
    were wrong at the commit that introduced this file (74/254/93/161 written
    against a file that held 75/250/90/160).  The merge repaired them; do not
    quote them, RE-MEASURE.  The success line this script prints on every
    check.sh run says the first two -- `78 vocabulary, 250 counted` -- so the
    gate carries the measurement and this comment carries only the reading.
    README gap 871.
"""

import re
import sys
import os
import glob
import collections

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

LEAN_FILES = sorted(glob.glob(os.path.join(HERE, "TmKernel", "TmKernel", "*.lean"))) + \
             sorted(glob.glob(os.path.join(HERE, "TmKernel", "*.lean")))
README = os.path.join(HERE, "README.md")
RUST_DIRS = ["tm/src", "tm-core/src", "tm/tests", "tm-core/tests",
             "kernel/tm-kernel-ffi/src", "kernel/tm-kernel-ffi/tests",
             "kernel/tm-kernel-ffi/examples"]

LEAN_KW = r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|example|opaque|axiom)"
LEAN_DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*"
    r"(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+|partial[ \t]+|unsafe[ \t]+)*"
    + LEAN_KW + r"[ \t]+([^\s(){}\[\]:]+)", re.M)
LEAN_BLOCK = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+)*(structure|inductive)\b")
LEAN_FIELD = re.compile(r"^[ \t]+([A-Za-z_][A-Za-z0-9_']*)[ \t]*:[^=]")
LEAN_CTOR = re.compile(r"^[ \t]*\|[ \t]*([A-Za-z_][A-Za-z0-9_']*)")
RUST_DECL = re.compile(r"\b(?:fn|struct|enum|const|static|type|trait|mod|union)[ \t]+([A-Za-z_][A-Za-z0-9_]*)")
RUST_FIELD = re.compile(r"^[ \t]*(?:pub(?:\([^)]*\))?[ \t]+)?([a-z_][a-z0-9_]*)[ \t]*:[ \t]*[^=]", re.M)
STRING_LIT = re.compile(r'"([A-Za-z_][A-Za-z0-9_]*)"')

SPAN = re.compile(r"`([^`\n]+)`")
CITED = re.compile(r"^[A-Za-z][A-Za-z0-9_'?!]*(?:\.[A-Za-z0-9_'?!]+)*$")


def read(path):
    with open(path, encoding="utf-8", errors="replace") as handle:
        return handle.read()


def declared():
    """The four declaration sets, as one set of short names."""
    names = set()
    for path in LEAN_FILES:
        text = read(path)
        for m in LEAN_DECL.finditer(text):
            names.add(m.group(1).split(".")[-1])
        names.update(STRING_LIT.findall(text))
        block = None
        for line in text.split("\n"):
            head = LEAN_BLOCK.match(line)
            if head:
                block = head.group(1)
                continue
            if block is None:
                continue
            if line[:1] not in ("", " ", "\t", "|"):
                block = None
            elif block == "structure":
                field = LEAN_FIELD.match(line)
                if field:
                    names.add(field.group(1))
            else:
                ctor = LEAN_CTOR.match(line)
                if ctor:
                    names.add(ctor.group(1))
    for rel in RUST_DIRS:
        for path in sorted(glob.glob(os.path.join(ROOT, rel, "**", "*.rs"), recursive=True)):
            text = read(path)
            names.update(RUST_DECL.findall(text))
            names.update(RUST_FIELD.findall(text))
            names.update(STRING_LIT.findall(text))
    for rel in ("tm", "tm-core", "kernel"):
        for base, dirs, files in os.walk(os.path.join(ROOT, rel)):
            dirs[:] = [d for d in dirs if d not in ("target", ".lake", ".git")]
            for name in files:
                names.add(os.path.splitext(name)[0])
    return names


def cited():
    """Every backticked snake_case citation, with count and first location."""
    hits = collections.Counter()
    where = {}
    for path in LEAN_FILES + [README]:
        fenced = path.endswith(".md")
        inside = False
        for n, line in enumerate(read(path).split("\n"), 1):
            if fenced and line.lstrip().startswith("```"):
                inside = not inside
                continue
            if inside:
                continue
            for m in SPAN.finditer(line):
                name = m.group(1).strip()
                if "_" in name and CITED.match(name):
                    hits[name] += 1
                    where.setdefault(name, "%s:%d" % (os.path.relpath(path, HERE), n))
    return hits, where


def allow_list(path):
    """VOCABULARY names and GRANDFATHERED name -> cap, from the allow-list."""
    vocabulary, capped = set(), {}
    for line in read(path).split("\n"):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) == 2 and parts[0].isdigit():
            capped[parts[1]] = int(parts[0])
        elif len(parts) == 1:
            vocabulary.add(parts[0])
        else:
            print("citations.py: bad allow-list line: %s" % line)
            return None, None
    return vocabulary, capped


def main():
    allow_path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "citations-allow.txt")
    vocabulary, capped = allow_list(allow_path)
    if vocabulary is None:
        return 2
    names = declared()
    hits, where = cited()

    bad, used = [], set()
    for name, count in sorted(hits.items()):
        if name.split(".")[-1] in names:
            continue
        if name in vocabulary:
            used.add(name)
            continue
        if name in capped:
            used.add(name)
            if count <= capped[name]:
                continue
            bad.append((name, where[name], "%d citations, %d allowed" % (count, capped[name])))
            continue
        bad.append((name, where[name], "resolves to nothing"))

    stale = (vocabulary | set(capped)) - used
    if bad:
        print("%d unresolved:" % len(bad))
        for name, loc, why in bad:
            print("  %s  %s  (%s)" % (loc, name, why))
        return 1
    print("%d citations, %d resolved, %d allowed (%d vocabulary, %d counted), "
          "%d allow entries unused"
          % (sum(hits.values()), sum(hits.values()) - sum(hits[n] for n in used),
             sum(hits[n] for n in used), len(vocabulary), len(capped), len(stale)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
