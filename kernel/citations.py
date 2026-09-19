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
    AGENTS.md                         the process authority (D41, W-20)

whose content is a dotted identifier that is EITHER snake_case (an underscore
anywhere -- the shape this kernel's theorem names have) OR camelCase (a
lowercase letter immediately followed by an uppercase one, anywhere in the span
-- the shape its `def`s, fields and constructors have).  D41 widened it; D39
swept snake_case only, and `is_citation` is the whole of the predicate.

WHY THAT IS THE CAMEL TEST, and not "has a capital in it".  The population
inside the camel blind spot was measured at W-19 (gap 880) and is mostly tactic,
type and prose vocabulary: `decide` (x170 in the Lean, x303 in the README),
`rfl`, `Nat`, `Bool`, `sorry`, `lake`, hypothesis names (`hnopast` x20) and
commit shas.  NOT ONE of those has a lower-to-upper transition -- they are
single-case runs, capitalised words, or lowercase hex -- so the transition test
excludes the whole of that noise without an allow-list entry for any of it.
Measured over this file set: 11,247 snake citations (3,964 distinct) and 11,383
camel-only ones (2,591 distinct).

WHAT IT RESOLVES AGAINST.  SEVEN declaration sets, in this order.  None of them
is prose: every one is a place where the name is *declared*, so resolving
against it cannot launder one stale sentence with another.

    1. Lean declarations -- theorem/lemma/def/abbrev/structure/inductive/
       instance/class/example/opaque/axiom in the files above, plus the fields
       of a `structure`, the constructors of an `inductive` (EVERY `| name` on
       the line, not only the first -- that bug hid `oneBlock`, `overWall`,
       `overBreak`, `energyFilter` and `windDown`, all five real constructors of
       `PlanCheck.CheckName`, which is declared on one line), and the segments
       of every `namespace` (`Tm.LogStamp` is declared by `namespace LogStamp`).
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
    6. THE CHECKERS' OWN PYTHON (W-20).  `def`s, `class`es and module-level
       ALL_CAPS constants in `kernel/*.py` -- 53 names, of which 46 are not
       declared anywhere else.  `citations.py`'s and `mutate.py`'s own headers
       and the README blocks about them cite `LEAN_CTOR`, `core_declared` and
       `new_or_changed`, which are declarations of this repository in exactly
       the sense a Rust `fn` is.  The W-20 block's first run failed on those
       three, which is how this set was found.  It carries source 3's risk in
       miniature: seven of the 53 (`read`, `run`, `build`, `main`, `digest`,
       `README`, `SPAN`) are generic, though all seven are already declared
       elsewhere, and none of the 53 collides with an allow-list entry.
       Its own blind spot: a `.py` file outside kernel/ is not read, and this
       set's names are not swept as PROSE either -- a stale citation inside
       citations.py's own docstring is invisible to citations.py.
    7. THE PINNED LEAN TOOLCHAIN'S OWN SOURCES (D41, W-20), read out of
       `~/.elan/toolchains/<the pin>/src/lean` -- the pin comes from
       `kernel/TmKernel/lean-toolchain` and AGENTS R8 forbids moving it.  38,538
       distinct short names.  CONSULTED ONLY FOR A CITATION WITH NO UNDERSCORE:
       19,449 of those names are snake_case (`map_append`, `succ_le`), and
       letting them resolve a deleted kernel THEOREM would be a real weakening
       of the half of this check that already works.  A missing source tree is a
       hard error, never a silently smaller declaration set.
       Its price and its yield are both small and both measured: +0.21 s of
       check 8's 0.49 s, and it resolves 299 citations / 64 distinct names that
       would otherwise each need an allow-list entry (`List.mapTR`, `zipIdx`,
       `filterMap`, `mergeSort`, `mapM`, `DecidableEq`, `sorryAx`, `findIdx?`).

A citation resolves if its LAST dotted segment is in any of the seven.

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

WHAT THIS CANNOT SEE.  Re-measured at W-20 with the resolver in this file and
nothing else; do not quote these, RE-MEASURE.
  * THE NAMESPACE, and this is the largest one.  Resolution is on the LAST
    dotted segment, so `Tm.Look.foo_bar` resolves against a `Tm.Cap.foo_bar`
    that still exists, and a theorem MOVED between namespaces is invisible.
    Measured at W-20 over the kernel's 7,783 distinct declared short names:
    115 of them are declared under MORE THAN ONE full name -- `wf` under 28
    (`Tm.Cal.Instant.wf` … `Tm.Planner.Seg.wf`), `empty` under 15, `go` under
    14, `name` under 12 -- so for those 115 a citation can resolve against a
    declaration that is not the one the sentence means.  W-19's repair step hit
    exactly this and fixed it in the KERNEL rather than in the checker: a new
    `Planner.locOk` was byte-distinct from `Cmd.locOk` and shared its short
    name, and gap 878 renamed it `groupLocOk` so that no citation of either can
    resolve against the other.  TURNING FULL-NAME RESOLUTION ON IS NOT A SMALL
    CHANGE and is why it is not done here: prose abbreviates (`Look.budgetOf`
    for `Tm.Look.budgetOf`, `Log.charsLe` x35 for a declaration this file's own
    best-effort namespace tracker reads as `charsLe`), so it has to be a SUFFIX
    match, and a best-effort tracker -- `namespace`/`section`/`end`, which Lean
    lets you nest, name and unname -- still reports 267 distinct dotted
    citations (735 in all) that match no full name it believes in.  Every one of
    those 267 would have to be adjudicated before the stricter rule could be
    turned on, and a tracker that is wrong about a namespace fails a citation
    that is right.  README gap 933.
  * A name that is also a Rust name, a JSON key, a Python name in kernel/*.py
    or a Lean core name.  A deleted Lean theorem whose short name is any of
    those still resolves, by source 3, 4, 6 or 7.
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
    exemption and a later sentence citing it as live still fails.  W-20's own
    repair of `eligibleAt` and `emitRefused` is 51 applications of it.
  * A span that is not one identifier.  `planOk Planner.eligibleAt` at
    README.md:28120 contains a space, so `CITED` refuses it and the sweep never
    sees the dead name inside it.  There are 19,779 such spans (7,157 distinct) -- backticked code
    fragments, commands and phrases, of which this is one.
  * kernel/design/**, tm-spec-v1.md and PLAN-lean-kernel.md.  D41 scoped the
    widening to AGENTS.md and DECLINED the design: measured at W-19,
    kernel/design/** holds 144 unresolved names, and they are not this class --
    the design is a prospective specification whose unresolved names are work to
    do (`mkStateDay?` and refuses_an_inverted_window sit in a column headed
    "bound, constructor, rejection theorem" for a record that has no such field
    yet).  tm-spec-v1.md 26 citations / 20 distinct / 0 unresolved;
    PLAN-lean-kernel.md 83 / 65 / 9.
  * RUST.  Not one of the six sets is read as PROSE for Rust: a stale citation
    inside a `///` doc comment in tm/src is not swept at all, because only the
    four file sets above are swept.  Check 9 has the same edge (README gap 936).
  * The allow-list itself.  At W-20 it holds 107 uncounted VOCABULARY names and
    352 counted ones.  Sections 4 and 8 are SEEDED BASELINES nobody has opened
    -- 160 snake (gap 833) and 50 camel (gap 934) -- and may hide stale
    citations.  The other 142 counted entries were opened by a human once.
  * ITS OWN HEADER.  The numbers in this comment are prose, not backticked
    identifiers, so this check cannot resolve them -- and all four of the
    numbers the W-19 version of this paragraph carried were wrong at the commit
    that introduced it (74/254/93/161 against a file holding 75/250/90/160), and
    the ledger's own account of this file's size was wrong a second time (gap
    882).  The success line this script prints on every check.sh run says the
    two that matter -- `107 vocabulary, 352 counted` -- so the gate carries the
    measurement and this comment carries only the reading.  README gap 871.
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
AGENTS = os.path.join(ROOT, "AGENTS.md")
TOOLCHAIN = os.path.join(HERE, "TmKernel", "lean-toolchain")
RUST_DIRS = ["tm/src", "tm-core/src", "tm/tests", "tm-core/tests",
             "kernel/tm-kernel-ffi/src", "kernel/tm-kernel-ffi/tests",
             "kernel/tm-kernel-ffi/examples"]

LEAN_KW = r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|example|opaque|axiom)"
LEAN_DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*"
    r"(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+|partial[ \t]+|unsafe[ \t]+)*"
    + LEAN_KW + r"[ \t]+([^\s(){}\[\]:]+)", re.M)
LEAN_NS = re.compile(r"^[ \t]*namespace[ \t]+([A-Za-z_][A-Za-z0-9_.']*)", re.M)
LEAN_BLOCK = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+)*(structure|inductive)\b")
LEAN_FIELD = re.compile(r"^[ \t]+([A-Za-z_][A-Za-z0-9_']*)[ \t]*:[^=]")
LEAN_CTOR = re.compile(r"\|[ \t]*([A-Za-z_][A-Za-z0-9_']*)")
RUST_DECL = re.compile(r"\b(?:fn|struct|enum|const|static|type|trait|mod|union)[ \t]+([A-Za-z_][A-Za-z0-9_]*)")
RUST_FIELD = re.compile(r"^[ \t]*(?:pub(?:\([^)]*\))?[ \t]+)?([a-z_][a-z0-9_]*)[ \t]*:[ \t]*[^=]", re.M)
STRING_LIT = re.compile(r'"([A-Za-z_][A-Za-z0-9_]*)"')
# Source 7: the checkers' own Python.  `def f(` / `class C(` / `class C:` and
# module-level ALL_CAPS constants.  The `[(:]` is load-bearing: without it the
# word `class` inside totality.py's own docstring declared a constant named
# `this`.
PY_DECL = re.compile(r"^(?:def|class)[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]*[(:]"
                     r"|^([A-Z][A-Z0-9_]*)[ \t]*=", re.M)

SPAN = re.compile(r"`([^`\n]+)`")
CITED = re.compile(r"^[A-Za-z][A-Za-z0-9_'?!]*(?:\.[A-Za-z0-9_'?!]+)*$")
CAMEL = re.compile(r"[a-z][A-Z]")


def is_citation(name):
    """A backticked span this check sweeps: snake_case, or camelCase (D41).

    `decide`, `rfl`, `Nat`, `sorry`, `lake`, a hypothesis name (`hnopast`) and a
    commit sha are all lowercase-or-capitalised runs with no lower-to-upper
    transition, so they are NOT camelCase and are not swept.  That transition is
    the whole discriminator; see the header.
    """
    return bool(CITED.match(name)) and ("_" in name or CAMEL.search(name) is not None)


def read(path):
    with open(path, encoding="utf-8", errors="replace") as handle:
        return handle.read()


def core_declared():
    """Source 6 (D41): the PINNED Lean toolchain's own library declarations.

    `kernel/TmKernel/lean-toolchain` pins `leanprover/lean4:v4.33.1` (AGENTS R8
    forbids moving it), and elan unpacks that toolchain's sources at
    `~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean`.  Those files are a
    DECLARATION set in exactly the sense sources 1-5 are: `List.mapTR`,
    `List.zipIdx`, `Nat.toFloat`, `DecidableEq` and `sorryAx` are declared there
    and nowhere in this repository.

    It is consulted ONLY for a citation with no underscore, so the snake_case
    half of this check is byte-for-byte what it was before D41: core declares
    10,360 snake_case short names (`map_append`, `succ_le`) and letting those
    resolve a kernel theorem name would be a real weakening.  See the header.

    A missing toolchain source tree is a HARD ERROR, never a silent loss of a
    declaration set."""
    with open(TOOLCHAIN, encoding="utf-8") as handle:
        pin = handle.read().strip()
    if ":" not in pin:
        raise SystemExit("citations.py: unreadable lean-toolchain: %s" % pin)
    channel, version = pin.split(":", 1)
    src = os.path.expanduser(os.path.join(
        "~/.elan/toolchains", channel.replace("/", "--") + "---" + version, "src", "lean"))
    paths = glob.glob(os.path.join(src, "**", "*.lean"), recursive=True)
    if not paths:
        raise SystemExit("citations.py: no toolchain sources under %s "
                         "(source 6 of 6 would be silently empty)" % src)
    names = set()
    for path in paths:
        for m in LEAN_DECL.finditer(read(path)):
            names.add(m.group(1).split(".")[-1])
    return names


def declared():
    """The four declaration sets, as one set of short names."""
    names = set()
    for path in LEAN_FILES:
        text = read(path)
        for m in LEAN_DECL.finditer(text):
            names.add(m.group(1).split(".")[-1])
        for m in LEAN_NS.finditer(text):
            names.update(m.group(1).split("."))
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
                names.update(LEAN_CTOR.findall(line))
    for rel in RUST_DIRS:
        for path in sorted(glob.glob(os.path.join(ROOT, rel, "**", "*.rs"), recursive=True)):
            text = read(path)
            names.update(RUST_DECL.findall(text))
            names.update(RUST_FIELD.findall(text))
            names.update(STRING_LIT.findall(text))
    for path in sorted(glob.glob(os.path.join(HERE, "*.py"))):
        for m in PY_DECL.finditer(read(path)):
            names.add(m.group(1) or m.group(2))
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
    for path in LEAN_FILES + [README, AGENTS]:
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
                if is_citation(name):
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
    core = core_declared()
    hits, where = cited()

    bad, used = [], set()
    for name, count in sorted(hits.items()):
        last = name.split(".")[-1]
        if last in names:
            continue
        if "_" not in name and last in core:
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
