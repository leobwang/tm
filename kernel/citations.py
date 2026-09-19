#!/usr/bin/env python3
"""check.sh's check 8 (D39): resolve the identifiers the prose CITES.

Five consecutive runs of the stage-6 campaign shipped a stale prose citation --
a doc comment or a README line naming a theorem that had been deleted or
renamed -- and every one was found by hand by an independent auditor, because
no check in check.sh reads a doc comment.  Check 3 reads `#print axioms` lines
and says so in its own comment; check 4 reads `/- CHEAT` headers.  Nothing read
the sentences.  That is README gap 779, and this is the check that ends it.

WHAT IS SWEPT.  Every backticked span -- on one line, or wrapped across two
(`wrapped`) -- of

    kernel/TmKernel/**/*.lean         the library AND the package root, and
                                      RECURSIVELY (the W-21 repair step: a
                                      module in a SUBDIRECTORY was invisible
                                      here, in totality.py and in mutate.py at
                                      once, while check.sh line 204 already
                                      said `TmKernel/**.lean`)
    kernel/README.md                  the ledger
    AGENTS.md                         the process authority (D41, W-20)
    kernel/check.sh, kernel/*.py,     the gate's own prose (W-20 repair step;
    kernel/mutations.txt              `CHECKERS`, and why the allow-list is not)

whose content is an identifier that is ANY OF THREE THINGS: snake_case (an
underscore anywhere -- the shape this kernel's theorem names have), camelCase (a
lowercase letter OR A DIGIT immediately followed by an uppercase one, anywhere
in the span -- the shape its `def`s, fields and constructors have), or QUALIFIED
(two or more dotted segments with a capitalised head -- the shape a declaration
has at a use site in another namespace).  D39 swept snake_case only; D41 added
camelCase; the W-21 repair step added the digit and the dotted test, and
`is_citation` is the whole of the predicate.

WHY THAT IS THE CAMEL TEST, and not "has a capital in it".  The population
inside the camel blind spot was measured at W-19 (gap 880) and is mostly tactic,
type and prose vocabulary: `decide` (x170 in the Lean, x303 in the README),
`rfl`, `Nat`, `Bool`, `sorry`, `lake`, hypothesis names (`hnopast` x20) and
commit shas.  NOT ONE of those has a case transition -- they are single-case
runs, capitalised words, or lowercase hex -- so the transition test excludes the
whole of that noise without an allow-list entry for any of it.  Measured at the
W-21 repair step over the whole identifier-shaped population: sweeping EVERY
span `CITED` accepts would put 370 distinct names / 1,767 citations in front of
an adjudicator, almost all of it that noise.

AND WHY THE OTHER TWO WERE ADDED, both driven.  `[a-z][A-Z]` does not match a
capital with a DIGIT in front of it, so gap22Parent and day0Wf were unswept --
gap22Parent was renamed childFoldB3 at stage 4 final step 3, is declared
nowhere since, and stood backticked at six live sites with this check green.
And a name with neither an underscore nor a transition was unswept altogether:
`Arith.ramp`, `Cap.edf`, `Look.energize`, `Look.bucket`, `Cal.Instant.wf`,
`Cand.enters` and `Ckpt.wf` are declarations of this kernel, and 4,848
citations / 600 distinct dotted spans were dropped.  DRIVEN: renaming the live
`def ramp` at Arith.lean:988 left eleven backticked `Arith.ramp` citations and
this file exited 0 with byte-identical counts; it now reports `Arith.ramp`
unresolved.  The dotted test costs THREE adjudications in all -- `JSON.stringify`
and `Subtype.val`, which are real referents this kernel does not declare, and
day0Wf, which is an older removal counted beside badDay0.

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
each need their own entry; an entry spelled sort_by exempts nothing.  That is the
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
       A COUNTED CAP IS EXACT SINCE THE W-21 REPAIR STEP: more citations than
       the cap fails, and so does FEWER, naming the number to tighten to.  Slack
       opened by a falling count is the same free exemption as a bumped cap and
       opens without anybody editing the allow-list.
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
    dotted segment, so a citation Tm.Look.foo_bar resolves against a Tm.Cap.foo_bar
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
  * A DOTTED SPAN WITH A LOWERCASE HEAD.  `QUAL` requires a capitalised first
    segment, because every namespace in this kernel is capitalised and a
    lowercase head is a projection on a variable (`a.val`, `q.val`, `x.2`), a
    filename (`mutate.py`, `mutations.txt`, `genlog80.py`) or a `set_option`
    key (`trace.compiler.ir.result`).  Measured at the W-21 repair step: of the
    18 dotted spans that would otherwise be unresolved, 15 are exactly those
    three shapes and none names a declaration.  A kernel definition spelled
    through a lowercase head would be missed, and there are none today.
  * LEAN CORE'S STRUCTURE FIELDS AND CONSTRUCTORS.  Source 7 reads the
    toolchain's `LEAN_DECL` lines only, so `Subtype.val` -- a field, not a
    `def` -- does not resolve against core and needs a VOCABULARY entry, where
    `List.mapTR` does not.  Widening source 7 the way source 1 is widened is a
    scope decision nobody has taken; the population is one name today.
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
    repair of eligibleAt and emitRefused is 51 applications of it, and the W-20
    repair step's last 19 + 2 are the rest.
  * A span that is not one identifier.  A backticked span containing a SPACE is
    refused by `CITED`, and the dead name inside it is never seen: `planOk
    Planner.eligibleAt` at README.md:28120 was exactly that and is repaired.
    There are 19,779 such spans (7,157 distinct) -- backticked code fragments,
    commands and phrases.  A span containing `::` is refused the same way and is
    a DIFFERENT population, measured at the W-20 repair step: 1,574 citations
    (505 distinct) are otherwise identifier-shaped, and 67 distinct / 111
    citations have a last segment declared nowhere this file reads.  Almost all
    are Rust `std`, chrono, serde or ENUM VARIANTS, which `RUST_DECL` does not
    capture (`u32::MAX` x11, `EditError::Ambiguous` x4) -- but at least one was
    an in-repo rename the ledger itself recorded, tm_kernel_ffi::trace_kind,
    repaired here.  Turning `::` on costs 67 adjudications and is a scope
    decision, not a repair; README gap 989.
  * A SPAN WRAPPED MID-WORD.  A span wrapped over TWO lines is swept -- see
    `wrapped` -- and so is one wrapped over more, since the W-21 repair step;
    joining it is what found two
    theorem names W-20 track P had renamed away from, in the paragraph claiming
    check 8 caught its stale citations.  The join requires the break to fall at
    an `_` or a `.`; a break that ate a SPACE joins two tokens into a word that
    resolves to nothing, which would fail the gate on a correct sentence.
    Measured over the swept files: 48 spans wrap, 43 at an underscore or dot
    and all 43 real names, 5 at an eaten space and all 5 spurious.  The carry
    survives exactly one line boundary and is dropped at a fence.
  * kernel/design/**, tm-spec-v1.md and PLAN-lean-kernel.md.  D41 scoped the
    widening to AGENTS.md and DECLINED the design: measured at W-19,
    kernel/design/** holds 144 unresolved names, and they are not this class --
    the design is a prospective specification whose unresolved names are work to
    do (mkStateDay? and refuses_an_inverted_window sit in a column headed
    "bound, constructor, rejection theorem" for a record that has no such field
    yet).  tm-spec-v1.md 26 citations / 20 distinct / 0 unresolved;
    PLAN-lean-kernel.md 83 / 65 / 9.
  * RUST.  Not one of the seven sets is read as PROSE for Rust: a stale citation
    inside a `///` doc comment in tm/src is not swept at all.  Check 9 has the
    same edge (README gap 936).  kernel/check.sh, kernel/mutations.txt and
    kernel/*.py ARE swept as prose since the W-20 repair step, which is where
    check.sh's own specification of D41's widening was found citing a
    backticked emitRefused; citations-allow.txt is not, and `CHECKERS` says
    why.
  * The allow-list itself.  At W-20 it holds 110 uncounted VOCABULARY names and
    352 counted ones.  Sections 4 and 8 are SEEDED BASELINES nobody has opened
    -- 160 snake (gap 833) and 50 camel (gap 934) -- and may hide stale
    citations.  The other 142 counted entries were opened by a human once.
  * ITS OWN HEADER.  The numbers in this comment are prose, not backticked
    identifiers, so this check cannot resolve them -- and all four of the
    numbers the W-19 version of this paragraph carried were wrong at the commit
    that introduced it (74/254/93/161 against a file holding 75/250/90/160), and
    the ledger's own account of this file's size was wrong a second time (gap
    882).  It was wrong a THIRD time, and this paragraph is where: it read
    `107 vocabulary` from `b1544fb` while the file it shipped with, three
    commits later at `ea57452`, holds 110 -- found at the W-20 land step, by
    reading the success line beside the sentence claiming to quote it.  The
    success line this script prints on every check.sh run says the two that
    matter -- `110 vocabulary, 352 counted` -- so the gate carries the
    measurement and this comment carries only the reading.  README gap 871.
"""

import re
import sys
import os
import glob
import collections

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

# RECURSIVELY, `.lake`/`target`/`.git` pruned -- the W-21 repair step's, and
# one of three enumerations that disagreed with `check.sh` line 204's
# `TmKernel/**.lean`.  A library module in a SUBDIRECTORY was invisible here,
# in `totality.py` and in `mutate.py` at once, while `mutate.py`'s own
# `touched()` asked git with a recursive pathspec: driven before the repair, a
# `TmKernel/TmKernel/Sub/Probe.lean` holding a backticked Look.zzz_no_such_thing
# left this file's counts BYTE-IDENTICAL and rc 0.  One glob and not two,
# because the recursive one subsumes `TmKernel/*.lean` and a path reached twice
# would have its every citation counted twice.
PRUNE = {".lake", "target", ".git"}
LEAN_FILES = sorted(
    path for path in glob.glob(os.path.join(HERE, "TmKernel", "**", "*.lean"),
                               recursive=True)
    if not PRUNE & set(path.split(os.sep)))
README = os.path.join(HERE, "README.md")
AGENTS = os.path.join(ROOT, "AGENTS.md")
# The gate's OWN files, swept as PROSE at the W-20 repair step.  They were the
# last unswept prose in kernel/, and check.sh line 215 -- the sentence that
# specifies D41's camelCase widening -- carried a backticked emitRefused, which
# is the dead name that widening exists because of.  kernel/*.py is already a
# DECLARATION source (source 7); reading the same files as prose is a different
# question and was not being asked.
#
# citations-allow.txt IS DELIBERATELY NOT HERE, and the reason is mechanical:
# an allow-list entry's own comment has to spell the name it exempts, so
# sweeping this file charges every COUNTED entry one extra citation against its
# own cap.  Measured at the repair step: 16 counted entries went over by
# exactly one, every one of them because the allow-list quotes itself, and none
# of the 16 was a defect.  The one real defect in that file -- a
# register_builtin_error core does not declare -- was found by running this
# file's resolver over it by hand, and repaired; doing that by hand is what the
# file gets instead of the sweep.
CHECKERS = [os.path.join(HERE, "check.sh"),
            os.path.join(HERE, "mutations.txt")] + \
           sorted(glob.glob(os.path.join(HERE, "*.py")))
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
# A lower-to-upper transition, OR A DIGIT-TO-UPPER ONE (the W-21 repair step).
# `[a-z][A-Z]` alone does not match gap22Parent or day0Wf: the character in
# front of the capital is a digit, so both were unswept, and gap22Parent --
# renamed childFoldB3 at stage 4 final step 3 and declared nowhere since --
# was backticked at six live sites with this check green.  A digit in front of
# a capital is still a compound word; none of the noise the header measures
# (`decide`, `rfl`, `Nat`, `sorry`, `lake`, `hnopast`, a commit sha) has one,
# because a sha is lowercase hex and the rest are single-case runs.
CAMEL = re.compile(r"[a-z0-9][A-Z]")
# A QUALIFIED name: two or more dotted segments whose FIRST is capitalised.
# That is how every declaration of this kernel is spelled at a use site
# (`Arith.ramp`, `Cap.edf`, `Look.bucket`, `Cal.Instant.wf`, `Ckpt.wf`), and
# none of those has an underscore or a case transition, so the two tests above
# dropped the whole population.  Measured at the W-21 repair step over the
# swept files: 4,848 citations / 600 distinct dotted spans were dropped, and
# sweeping the ones with a capitalised head costs THREE adjudications.
QUAL = re.compile(r"^[A-Z][A-Za-z0-9_'?!]*(?:\.[A-Za-z0-9_'?!]+)+$")
# A span may be at most 200 characters long before it is not a name any more;
# a longer carry is prose that happens to sit between two backticks.
WRAP_MAX = 200


def is_citation(name):
    """A span this check sweeps: snake_case, camelCase (D41), or QUALIFIED.

    `decide`, `rfl`, `Nat`, `sorry`, `lake`, a hypothesis name (`hnopast`) and a
    commit sha are all lowercase-or-capitalised runs with no case transition and
    no dot, so they are none of the three and are not swept.

    THE THIRD TEST IS THE W-21 REPAIR STEP'S, and it is what makes a name with
    neither an underscore nor a transition visible: `Arith.ramp`, `Cap.edf`,
    `Look.bucket`, `Ckpt.wf` are declarations of this kernel and every one was
    dropped.  It is the DOT, with a capitalised head, that carries it -- prose
    does not write `Look.bucket` by accident, and a dotted span with a LOWERCASE
    head is a projection on a variable (`a.val`, `x.2`), a filename
    (`mutate.py`, `mutations.txt`) or a `set_option` key
    (`trace.compiler.ir.result`), never a kernel name, because every namespace
    in this kernel is capitalised.  Measured: of the 18 dotted spans that would
    otherwise be unresolved, 15 are exactly those three shapes and none is a
    declaration.  That is the blind spot this test keeps; see the header.
    """
    return bool(CITED.match(name)) and (
        "_" in name or CAMEL.search(name) is not None or QUAL.match(name) is not None)


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


def wrapped(prefix, suffix):
    """The name a span that WRAPPED spells, or None.

    A long identifier hard-wrapped inside backticks is invisible to `SPAN`,
    which cannot cross a newline, so it is not counted, not resolved and not
    exempted -- check 8 reported GREEN on two theorem names W-20 track P had
    renamed away from, in the paragraph claiming check 8 caught its stale
    citations.  This is the join, and it is deliberately narrow.

    THE WRAP MUST BE AT AN UNDERSCORE OR A DOT -- the prefix ends with one or
    the suffix begins with one.  Without that test the join is wrong in the
    other direction: a span holding TWO tokens that wrapped at the space
    between them (`deriving` / `DecidableEq`, `import` / `Lean.Data.Json`,
    `Option` / `ActiveBlock`) joins into a camelCase word that resolves to
    nothing, and the gate fails on a sentence that is correct.  Measured over
    the swept files at the repair step: 48 spans wrap, 43 of them at an
    underscore or a dot and all 43 real names, 5 of them at an eaten space and
    all 5 spurious.  NOT SEEN: an identifier wrapped mid-word with no
    underscore at the break (`assign` / `Fold`).

    A SPAN WRAPPED OVER MORE THAN TWO LINES is swept since the W-21 repair
    step: a line with no backtick at all, inside an open span, is the MIDDLE of
    the wrap and `cited` adds it to the carry.  EVERY boundary is held to the
    same `_`-or-`.` test, not only the last, so a middle line that ate a space
    drops the carry exactly as a two-line join at a space is refused.  Measured
    when it landed: +2 citations over the swept files, both resolving, 0 new
    unresolved names -- and a planted Planner.w21_no_such_thing_at_all broken
    over three lines is reported, where before it was invisible."""
    suffix = suffix.lstrip()
    if not prefix or not suffix:
        return None
    if prefix[-1] not in "_." and suffix[0] not in "_.":
        return None
    name = (prefix + suffix).strip()
    return name if len(name) <= WRAP_MAX and is_citation(name) else None


def cited():
    """Every backticked snake_case citation, with count and first location."""
    hits = collections.Counter()
    where = {}
    for path in LEAN_FILES + [README, AGENTS] + CHECKERS:
        fenced = path.endswith(".md")
        inside = False
        # The carry is the tail of a span left OPEN at the end of a line.  It
        # survives exactly one line boundary and is dropped at a fence, at a
        # line holding ``` and at a line with no backtick at all, because
        # backtick parity inside this repository's prose is only reliable
        # line-locally -- which is why the per-line sweep below is UNCHANGED
        # and this runs beside it rather than replacing it.
        carry = None
        for n, line in enumerate(read(path).split("\n"), 1):
            if fenced and line.lstrip().startswith("```"):
                inside = not inside
                carry = None
                continue
            if inside or "```" in line:
                carry = None
                continue
            # A SPAN WRAPPED OVER MORE THAN TWO LINES.  A line with no backtick
            # at all, inside an open span, is the MIDDLE of the wrap: the carry
            # takes it and keeps going.  Bounded by `WRAP_MAX`, and `is_citation`
            # still has to accept the join, so an unterminated stray backtick
            # swallows at most 200 characters and resolves to nothing rather
            # than to something.  README gap 989's third item.
            if carry is not None and "`" not in line:
                tail = line.strip()
                joined = carry + tail
                carry = (joined
                         if tail and len(joined) <= WRAP_MAX
                         and (carry[-1:] in ("_", ".") or tail[0] in "_.")
                         else None)
                continue
            for m in SPAN.finditer(line):
                name = m.group(1).strip()
                if is_citation(name):
                    hits[name] += 1
                    where.setdefault(name, "%s:%d" % (os.path.relpath(path, HERE), n))
            parts = line.split("`")
            if carry is not None and len(parts) > 1:
                name = wrapped(carry, parts[0])
                if name is not None:
                    hits[name] += 1
                    where.setdefault(name, "%s:%d"
                                     % (os.path.relpath(path, HERE), n - 1))
                parts = parts[1:]
            carry = None
            if len(parts) >= 2 and len(parts) % 2 == 0 \
               and len(parts[-1]) <= WRAP_MAX:
                carry = parts[-1]
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

    # A COUNTED ENTRY WHOSE CAP EXCEEDS ITS LIVE COUNT IS SLACK, AND SLACK FAILS.
    # The cap is a ratchet: it exists so that a NEW sentence reaching for an
    # exempted name lands in a diff.  A cap of 17 against 15 live citations is
    # two free citations nobody adjudicated -- the same hole as bumping N
    # without looking, reached from the other side, and reached WITHOUT touching
    # this file: it opens by itself the moment prose that cited the name is
    # deleted or un-backticked.  Measured at the W-21 repair step, which is
    # where an auditor found it: 3 of 348 counted entries carried slack, 6
    # citations in all, and two of the three had opened that very run.
    #
    # The cost is declared: an edit that REMOVES a counted citation now fails
    # this check until the cap is tightened.  That is the ratchet working -- the
    # tightening is one line and the message names the number -- and the
    # alternative is a cap that only ever ratchets in the direction that costs
    # nothing.
    for name, cap in sorted(capped.items()):
        live = hits.get(name, 0)
        if live < cap:
            bad.append((name, where.get(name, "citations-allow.txt"),
                        "%d allowed, %d live -- tighten the cap to %d"
                        % (cap, live, live)))
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
