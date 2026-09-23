#!/usr/bin/env python3
"""check.sh's check 8 (D39): resolve the identifiers the prose CITES.

Five consecutive runs of the stage-6 campaign shipped a stale prose citation --
a doc comment or a README line naming a theorem that had been deleted or
renamed -- and every one was found by hand by an independent auditor, because
no check in check.sh reads a doc comment.  Check 3 reads `#print axioms` lines
and says so in its own comment; check 4 reads `/- CHEAT` headers.  Nothing read
the sentences.  That is README gap 779, and this is the check that ends it.

WHAT IS SWEPT -- AND SINCE W-27 THE DEFAULT POINTS THE OTHER WAY.  Every
backticked span, on one line or wrapped across two (`wrapped`), of EVERY FILE OF
THIS REPOSITORY except the ones `EXCLUDED` names with a reason.  The population
is `git ls-files` plus `--others --exclude-standard`; the residue -- a file that
is neither swept nor excluded -- must be EMPTY, and a file whose extension has
no reader FAILS this check by name.  `EXCLUDED`'s own comment is where that rule
is argued; it is the answer to README gap 1525, and every hole below is an
instance of the default having pointed the other way.

    .lean     `LEAN_FILES`, the library AND the package root, RECURSIVELY (the
              W-21 repair step: a module in a SUBDIRECTORY was invisible here,
              in totality.py and in mutate.py at once).  A tracked `.lean` this
              walk does not reach is a named failure since W-27.
    .rs       `RUST_FILES`, THE RUST COMMENTS (W-24, README gap 1313 item 3).
              `//!`, `///`, `//` and `/* */` only -- `rust_prose` is the exact
              complement of `rust_code`, so what the one blanks the other reads
              and no byte of either file is read as both code and prose.  String
              and char CONTENTS are blanked in both: a "fn foo" literal declares
              nothing and cites nothing.  A tracked `.rs` the walk does not
              reach is a named failure too.
    .c        `C_FILES`, read with the same scanner: C's comment grammar is a
              SUBSET of Rust's.  The FFI shim, R9's own 66 lines (W-27).
    .md .txt  raw text.  The ledger, AGENTS.md (D41, W-20), the gate's own prose
    .sh .py   (the W-20 repair step), `mutations.txt` and `parity.txt` (W-25),
    .toml     and since W-27 the repository ROOT README.md, `tm/DORMANT.md`, the
              six cargo/lake manifests and the oracle's shell scripts.

whose content is an identifier that is ANY OF FOUR THINGS: snake_case (an
underscore anywhere -- the shape this kernel's theorem names have), camelCase (a
lowercase letter OR A DIGIT immediately followed by an uppercase one, anywhere
in the span -- the shape its `def`s, fields and constructors have), QUALIFIED
(two or more dotted segments with a capitalised head -- the shape a declaration
has at a use site in another namespace), or `::`-SPELLED (the shape a Rust path
has, W-27).  D39 swept snake_case only; D41 added camelCase; the W-21 repair
step added the digit and the dotted test; W-27 added `::`, and `is_citation` is
the whole of the predicate.

THE `::` TEST HAS NO HEAD-CASE RULE and the dotted one does, deliberately.  A
dotted span with a lowercase head is a projection (`a.val`), a filename
(`mutate.py`) or a `set_option` key, never a kernel name.  A `::` span with a
lowercase head is a MODULE path -- `fs::read_to_string`, `serde_json::Map` --
and is exactly as much a name as `Ctx::replay_of`.  Measured at W-27 over the
swept files: 3,116 citations, 1,025 distinct, of which 121 distinct resolved to
nothing; 62 of those are this repository's own enum variants (`rust_variants`),
49 are library or fork names now in the allow-list, and TEN WERE LIVE STALE
CITATIONS -- Log::to_jsonl, out::ErrorDoc (the live type is `out::ErrorOut`),
emit::now_rows, tui_common::app_with, Replay::events_named, Replay::events_for,
DayReplay::wake_to_arrival_min, two renamed test names, and SegKind::NoSuchKind,
which is the W-24 ledger's own record of this hole going green on the gate it
documented.

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
    3. Rust declarations -- fn/struct/enum/const/static/type/trait/mod/union,
       struct fields AND FUNCTION PARAMETERS -- in every `.rs` file of the
       repository (`RUST_FILES`).  ENUM VARIANTS are source 3's too but are kept
       in `rust_variants` and consulted only for a `::` span; see below.
       The FORK's planner is in-tree (tm-core/src/planner.rs), so
       `place_mandatory_and_pref` and `active_run` resolve here and need no
       exemption.
       PARAMETERS ARRIVED WITH THE RUST PROSE SWEEP (W-24), and they arrived
       because of it: a doc comment naming the parameter of the very `fn` it is
       attached to is CORRECT prose, and eleven of the forty-one names the
       sweep first reported were exactly that (min_ci, new_text, flight_re,
       hours_since, is_last, mark_current, min_min, model_weights, own_round,
       palette_len, new_lines).  A parameter is declared by a signature, which
       is code and not prose, so it belongs in this source by the rule at the
       head of this list.  Its price is +119 distinct short names on a base of
       14,227, and it is the whole of the widening: `let` bindings were
       MEASURED and DECLINED at the same step -- +896 names for 2 more
       resolutions, a large laundering surface bought for nothing.  ghost_y and
       max_energy, the two `let`s cited from prose, are allow-list entries
       instead.
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

A citation resolves if its LAST segment -- under `.` OR `::` -- is in any of
the seven.  There is an EIGHTH set and it is not consulted for every citation:
`rust_variants`, this repository's Rust enum variants, is read only for a span
holding `::`, the way source 7 is read only for a span with no underscore.  Gap
1410 declined the variants at W-24 on the right number (+219 short names, each
able to launder a stale citation of any Lean constructor sharing it); scoping
them to `::` spans pays 0 of that and resolves 62 citations.

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
    commands and phrases.  A span containing `::` WAS refused the same way, for
    four runs after the W-20 repair step measured it and two after gap 1410
    named it; that is README gap 989 and it is CLOSED at W-27.  What the old
    measurement got wrong is worth keeping: it priced the widening at "67
    adjudications" over a 1,574-citation population, and the real numbers on the
    tree it landed against are 3,116 citations and 121 unresolved, because the
    W-24 Rust-prose sweep had since tripled the prose being read.  RE-MEASURE,
    do not quote.
  * WHAT THE `::` SWEEP STILL CANNOT SEE, and it is the namespace blind spot
    above wearing Rust's clothes: resolution is on the LAST segment, so
    Ctx::replay_of -- deleted at `2b26be3`, backticked at 63 sites, and no
    method of `Ctx`, which declares only `replay_with` -- RESOLVES, against five
    free `fn replay_of` test helpers in `tm/tests`.  Measured at W-27: a
    prototype that resolves the owner-and-member PAIR against `impl`, `enum` and
    `mod` bodies reports 59 distinct / 313 citations, and hand-checking the top
    rows shows most of them are the PROTOTYPE's errors, not the prose's -- an
    `impl` with a lifetime parameter reads its owner as the lifetime, and
    `Event`'s 26 variants come out of a macro no static parse expands.  A
    resolver that is wrong about an owner fails a sentence that is right, which
    is why gap 933 declined the same move on the Lean side.  README gap 1731.
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
    yet).  They are three `EXCLUDED` entries since W-27, which is the same
    decline said where a reader can see it and where a stale one fails.
    RE-MEASURED there: tm-spec-v1.md is 35 citations / 28 distinct / 0
    unresolved and would cost nothing today; PLAN-lean-kernel.md is 134 / 100 /
    8.  Reversing an owner's scope decision is the owner's to do, so neither was
    swept and both numbers are on the record instead.
  * RUST PROSE IS SWEPT SINCE W-24 and this bullet is its record.  It read, for
    four runs: "not one of the seven sets is read as PROSE for Rust; a stale
    citation inside a `///` doc comment in tm/src is not swept at all".  Turning
    it on cost 30 adjudications, not the 162 the W-23 measurement predicted --
    that number came from a WIDER span predicate than `is_citation`, and under
    this file's own predicate the population is 2,371 citations / 1,182 distinct
    / 86 distinct unresolved (153 occurrences), 44 of them already exempt.
    Its yield on the tree it landed against was EIGHT live stale citations:
    sectionOf (a Plan.lean definition that has never existed; the name is
    liveHeading), q6b_separations and day_separations (rustdoc intra-doc links
    to nothing), energy_mae and energy_bias (backticked inside the sentence
    saying they were invented), calendar_date and entry_json (past-tense
    removals still in backticks) and HotFlag (a class name beside the live
    variant `Overdue`).  WHAT IT STILL CANNOT SEE: a `let` binding cited from
    prose needs an allow-list entry (measured and declined above); and a
    `#[doc = "..."]` attribute is a string literal and is blanked.

    THE FOURTH BULLET HERE USED TO BE THE DIRECTORY LIST, and it under-reported
    itself exactly the way check 3's roster grep did: it named tm/build.rs,
    kernel/tm-kernel-ffi/build.rs and "a future crate" as the unswept cases,
    while tm/examples -- two compiled `--example` targets of a crate whose src
    and tests ARE swept -- was none of the three and was unswept (README gap
    1418).  `RUST_FILES` is `leanfiles.rust_files(ROOT)` since the W-24 repair
    step, the SAME property-based walk and prune rule the Lean side has used
    since W-22, so there is no list to be missing from: a .rs file anywhere in
    the repository outside a dot-directory or a CACHEDIR.TAG'd build directory
    is swept.  What REPLACES the bullet is that walk's own blind spot, stated
    in `leanfiles.rust_files`: an undeclared build directory is walked and its
    generated .rs read as a source.  Check 9 still has the old edge on the Lean
    side (README gap 936).
    kernel/check.sh, kernel/mutations.txt and
    kernel/*.py ARE swept as prose since the W-20 repair step, which is where
    check.sh's own specification of D41's widening was found citing a
    backticked emitRefused; citations-allow.txt is not, and its `EXCLUDED`
    entry says why.
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

import leanfiles

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

# RECURSIVELY, build directories pruned -- `leanfiles.lean_files`, which is where
# this walk went at the W-22 repair step.  It was the W-21 repair step's, and one
# of three enumerations that disagreed with `check.sh` line 204's
# `TmKernel/**.lean`.  A library module in a SUBDIRECTORY was invisible here,
# in `totality.py` and in `mutate.py` at once, while `mutate.py`'s own
# `touched()` asked git with a recursive pathspec: driven before the repair, a
# `TmKernel/TmKernel/Sub/Probe.lean` holding a backticked Look.zzz_no_such_thing
# left this file's counts BYTE-IDENTICAL and rc 0.  One walk and not two,
# because the recursive one subsumes `TmKernel/*.lean` and a path reached twice
# would have its every citation counted twice.
#
# AND THE PRUNE LIST WAS THE NEXT HOLE, repaired at W-22: the three walks shared
# the hard-coded name `target`, which is a legal Lean module path component, so a
# module under `kernel/TmKernel/TmKernel/target/` was invisible here, in
# `totality.py` and in `mutate.py` at once.  Driven: it left this file at
# 28699/27174/1525/0, byte-identical again.  `leanfiles.is_build_dir` prunes on a
# property a build directory has, never on a name.
LEAN_FILES = [str(p) for p in leanfiles.lean_files(os.path.join(HERE, "TmKernel"))]
# **THE EIGHTH LEVEL OF THE ENUMERATION HOLE, AND THE RULE THAT ENDS THE CLASS**
# (README gap 1525, answered at W-27).
#
# SEVEN times this campaign a checker has been found not to read something it
# claimed to read, and each fix made a list longer: the Lean walk (W-21), the
# prune list (W-22), check 3's roster grep (W-22), the library ROOT module
# (W-23, gap 1314), `tm/examples` (W-24, gap 1418), `kernel/parity.txt` (W-25,
# gap 1525) and, here, the `::`-spelled path `is_citation` refused.  Gap 1525
# asked for the property that tells a checker's data file from
# `citations-allow.txt` and concluded there is none.  **There is none, and that
# is not the question.**  The question is which way round the DEFAULT points.
#
#   An enumeration a new file must be ADDED to in order to be COVERED is
#   unsound: the file that is missing from it is silent, and nobody is told.
#   An enumeration a new file must be ADDED to in order to be EXEMPT is sound:
#   the file that is missing from it is SWEPT, and if it should not have been,
#   the gate fails loudly on the next run and a human writes one line.
#
# All seven holes are the first shape.  So the enumeration is inverted here: the
# repository's own list of its files -- `git ls-files`, plus `--others
# --exclude-standard` so a file added and not yet committed counts, because
# acceptance runs BEFORE the commit -- is the population, `EXCLUDED` below is the
# only list, and the residue must be EMPTY.  A file whose extension has no reader
# and no exclusion FAILS this check by name.  `parity.txt` could not have been
# missed under this rule; nor can the ninth one.
#
# WHAT IT COSTS, declared and not hidden.  Every new KIND of file needs a line --
# an exclusion with a reason, or a reader.  A new `.md`, `.rs`, `.lean`, `.py`,
# `.txt`, `.toml`, `.sh` or `.c` needs nothing, because those already have
# readers.  And the gate now depends on `git`; a repository `git ls-files` cannot
# read is a HARD ERROR here, never a silently smaller population, the way a
# missing toolchain source tree is in `core_declared`.
#
# AND IT RECONCILES THE TWO PROPERTY-BASED WALKS AGAINST GIT.  `LEAN_FILES` and
# `RUST_FILES` are filesystem walks (they must be: a new module is swept before
# it is added, which `git ls-files` alone cannot do).  A tracked `.lean` or `.rs`
# the walk did not reach is the W-21/W-22/W-23 class exactly, and it is now a
# named failure rather than a silence.
#
# WHAT WENT IN WHEN THE DEFAULT FLIPPED, all measured first: the repository ROOT
# `README.md` (47 citations, ONE unresolved -- `core.hooksPath`, a git config
# key), `tm/DORMANT.md` (3, none), `kernel/tm-kernel-ffi/shim.c` (2, none -- R9's
# own 66 lines, and the first C in this sweep), the six `Cargo.toml`/`lakefile.toml`
# manifests (3, none; the root one carries D22's `raw_value` and `float_roundtrip`
# paragraph) and the oracle's two `.sh` scripts (1, none).  One adjudication for
# six files and two whole file types.
EXCLUDED = (
    # (pattern, why).  THREE FORMS AND NO GLOB LANGUAGE, so that reading an
    # entry cannot be wrong about what it covers: a pattern ending in `/` is a
    # directory PREFIX, one beginning with `*` is a basename SUFFIX (a KIND of
    # file), and anything else is an EXACT repository-relative path.
    ("kernel/corpus/", "stage 2's fixture DOCUMENTS -- a user's plan tree, not "
                       "prose about this repository, and AGENTS forbids touching them"),
    ("kernel/design/", "D41 DECLINED the design: 144 unresolved names that are a "
                       "prospective specification's work to do (re-measured at W-27: "
                       "8 tracked files)"),
    ("tm-spec-v1.md", "D41's decline.  RE-MEASURED at W-27 and it would cost NOTHING "
                      "today: 35 citations, 28 distinct, 0 unresolved.  Left out because "
                      "reversing an owner's scope decision is the owner's to do"),
    ("PLAN-lean-kernel.md", "D41's decline.  Re-measured at W-27: 134 citations, 100 "
                            "distinct, 8 unresolved"),
    ("kernel/citations-allow.txt", "an allow-list entry's comment has to SPELL the name "
                                   "it exempts, so sweeping this file charges every "
                                   "COUNTED entry one extra citation against its own cap "
                                   "-- measured at the W-20 repair step: 16 entries went "
                                   "over by exactly one and none was a defect.  It gets "
                                   "read by hand instead"),
    (".claude/", "the agent harness's own directory, pruned by the same leading-dot "
                 "property `leanfiles.is_build_dir` uses.  Measured: API-NOTES.md is "
                 "265 citations, 6 unresolved"),
    ("tm/templates/", "the documents `tm init` writes into a NEW tree: fixture text, "
                      "the same class as corpus/"),
    ("tm/tests/fixtures/", "recorded input and output, the same class as a fenced block"),
    ("tm-core/tests/fixtures/", "recorded input and output"),
    ("*.snap", "an insta SNAPSHOT is a RECORD of what a command printed at a commit that "
              "has gone; demanding it resolve against today's tree is demanding a "
              "re-bless, which AGENTS forbids"),
    ("*.proptest-regressions", "D46's seed lines.  Data, and not one byte of prose"),
    ("*Cargo.lock", "cargo resolver output -- three of them, one per workspace root"),
    ("kernel/TmKernel/lake-manifest.json", "lake resolver output"),
    ("kernel/TmKernel/lean-toolchain", "the R8 pin, one line, no prose"),
    ("*.gitignore", "no prose"),
)

# extension -> which reader.  `rust` is `rust_prose`; `lean` and `plain` are the
# raw text.  `.c` reads with the Rust scanner because C's comment grammar is a
# SUBSET of Rust's (`//` and `/* */`, and Rust's nesting rule only ever ends a
# comment later, never earlier), so no byte of a `.c` file is read as code.
READERS = {".lean": "lean", ".rs": "rust", ".c": "rust", ".md": "plain",
           ".txt": "plain", ".sh": "plain", ".py": "plain", ".toml": "plain"}


def tracked():
    """Every file of this repository, by the repository's own account.

    Tracked, plus added-but-not-committed (`--others --exclude-standard`),
    because acceptance runs BEFORE the commit and a checker data file added in
    the same step as the sentence that cites it is exactly the W-25 case.
    """
    import subprocess
    out = []
    for args in (["ls-files", "-z"], ["ls-files", "-z", "--others", "--exclude-standard"]):
        r = subprocess.run(["git"] + args, cwd=ROOT, capture_output=True, text=True)
        if r.returncode != 0:
            raise SystemExit("citations.py: `git %s` failed in %s -- the file "
                             "population would be silently smaller" % (args[0], ROOT))
        out += [p for p in r.stdout.split("\0") if p]
    return sorted(set(out))


def excluded_by(rel):
    """The index of the EXCLUDED entry that covers `rel`, or None."""
    for i, (pat, _why) in enumerate(EXCLUDED):
        if pat.endswith("/"):
            if rel.startswith(pat):
                return i
        elif pat.startswith("*"):
            if rel.endswith(pat[1:]):
                return i
        elif rel == pat:
            return i
    return None


def partition():
    """(plain paths, C paths, unaccounted, unused exclusions, counts).

    The residue rule: a repository file that is neither swept nor excluded is
    UNACCOUNTED and fails the check.  An EXCLUDED entry that covers nothing is
    stale and fails it too, by the same ratchet the counted allow-list uses.
    """
    lean = {os.path.relpath(p, ROOT) for p in LEAN_FILES}
    rust = {os.path.relpath(p, ROOT) for p in RUST_FILES}
    plain, cfiles, unaccounted, used = [], [], [], set()
    for rel in tracked():
        i = excluded_by(rel)
        if i is not None:
            used.add(i)
            continue
        kind = READERS.get(os.path.splitext(rel)[1])
        if kind == "lean":
            if rel not in lean:
                unaccounted.append((rel, "tracked .lean the LEAN_FILES walk did not reach"))
            continue
        if kind == "rust" and rel.endswith(".rs"):
            if rel not in rust:
                unaccounted.append((rel, "tracked .rs the RUST_FILES walk did not reach"))
            continue
        if kind == "rust":
            cfiles.append(os.path.join(ROOT, rel))
        elif kind == "plain":
            plain.append(os.path.join(ROOT, rel))
        else:
            unaccounted.append((rel, "no reader for this extension and no exclusion"))
    unused = [EXCLUDED[i][0] for i in range(len(EXCLUDED)) if i not in used]
    return sorted(plain), sorted(cfiles), unaccounted, unused


TOOLCHAIN = os.path.join(HERE, "TmKernel", "lean-toolchain")
# THE RUST SOURCES, BY THE SAME PROPERTY-BASED WALK THE LEAN USES.  This was a
# hard-coded list of seven directory names until README gap 1418 -- the exact
# shape leanfiles.py's own header says cannot work -- and `tm/examples` was not
# on it: two compiled `--example` targets of the `tm` crate whose `src` and
# `tests` ARE swept, holding 17 backticked spans of live prose about
# `kernel_log::ReplayCache`, and check 8 was GREEN on a plant in either of them.
# The list's blind-spot sentence named only `tm/build.rs`,
# `kernel/tm-kernel-ffi/build.rs` and "a future crate", so it could not see it.
# The walk now starts at the repository ROOT and prunes by property, which
# closes all three of those named holes as well.
RUST_FILES = [str(p) for p in leanfiles.rust_files(ROOT)]

# The partition above needs both walks, so it is taken here.
# Four separate bindings and not one tuple unpack, so that each is a source-6
# declaration: `PY_DECL` reads `NAME =` at a line head and a tuple target is
# not one, which left this file's own prose citing an undeclared `C_FILES`.
_PARTITION = partition()
PLAIN_FILES = _PARTITION[0]
C_FILES = _PARTITION[1]
UNACCOUNTED = _PARTITION[2]
UNUSED_EXCLUSIONS = _PARTITION[3]

# A Rust FUNCTION PARAMETER, read out of `rust_code` so a comment cannot
# declare one.  `(name:` or `, name:`, with `mut` allowed -- deliberately the
# same shape as `RUST_FIELD`, which is why the two share the laundering risk
# already declared in the header rather than adding a new one.  Source 3.
RUST_PARAM = re.compile(r"(?:^|[(,]\s*)(?:mut\s+)?([a-z_][A-Za-z0-9_]*)\s*:", re.M)

LEAN_KW = r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|example|opaque|axiom)"
LEAN_DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*"
    r"(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+|partial[ \t]+|unsafe[ \t]+)*"
    + LEAN_KW + r"[ \t]+([^\s(){}\[\]:]+)", re.M)
LEAN_NS = re.compile(r"^[ \t]*namespace[ \t]+([A-Za-z_][A-Za-z0-9_.']*)", re.M)
LEAN_BLOCK = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+)*(structure|inductive)\b")
LEAN_FIELD = re.compile(r"^[ \t]+([A-Za-z_][A-Za-z0-9_']*)[ \t]*:[^=]")
LEAN_CTOR = re.compile(r"\|[ \t]*([A-Za-z_][A-Za-z0-9_']*)")
RAW_OPEN = re.compile(r'b?r#*"')
RUST_DECL = re.compile(r"\b(?:fn|struct|enum|const|static|type|trait|mod|union)[ \t]+([A-Za-z_][A-Za-z0-9_]*)")
RUST_FIELD = re.compile(r"^[ \t]*(?:pub(?:\([^)]*\))?[ \t]+)?([a-z_][a-z0-9_]*)[ \t]*:[ \t]*[^=]", re.M)
# A RUST ENUM VARIANT (source 3, W-27), and it is source 1's `LEAN_CTOR` seen in
# the other language: an `inductive`'s constructors are a declaration set there
# and an `enum`'s variants are one here.  Turning `::` on without this would put
# 62 distinct names in front of an adjudicator that are declarations of this
# repository -- `Event::Arrive`, `StoreError::Conflict`, `SegKind::WindDown` --
# and the allow-list is for names this kernel does NOT declare.
#
# WHY IT IS NOT READ OUT OF THE `enum` BLOCK, which is where it looks like it
# should live: `tm-core/src/log.rs` declares `Event` inside a macro, so its 26
# variants exist only at that macro's CALL site and no brace-matched `enum` body
# holds them.  The shape read instead is a CAPITALISED
# word at the head of a line in `rust_code`, followed by `,` `{` `(` `=>` or a
# single `=`.  That is a variant DECLARATION (`Arrive,`, `Arrive { .. }`,
# `Arrive => "arrive" {`) or a match arm / struct literal naming one, and the
# second is as good as the first by this file's own rule: a match arm is CODE,
# not prose, and it only compiles because the variant exists.  It is not the
# whole story -- a variant declared and used NOWHERE at a line head is still
# missed -- and that is the blind spot, not a name list.
RUST_VARIANT = re.compile(r"^[ \t]*([A-Z][A-Za-z0-9_]*)[ \t]*(?:,|\{|\(|=>|=[^=])", re.M)
STRING_LIT = re.compile(r'"([A-Za-z_][A-Za-z0-9_]*)"')
# Source 7: the checkers' own Python.  `def f(` / `class C(` / `class C:` and
# module-level ALL_CAPS constants.  The `[(:]` is load-bearing: without it the
# word `class` inside totality.py's own docstring declared a constant named
# `this`.
PY_DECL = re.compile(r"^(?:def|class)[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]*[(:]"
                     r"|^([A-Z][A-Z0-9_]*)[ \t]*=", re.M)

SPAN = re.compile(r"`([^`\n]+)`")
# `::` IS A SEPARATOR HERE SINCE W-27, and it is the SEVENTH enumeration hole
# (README gap 989, open since the W-20 repair step).  A span holding `::` was
# not citation-shaped at all -- refused by this pattern the way a span holding a
# SPACE is -- so `Ctx::replay_of`, `Event::Arrive` and `u32::MAX` were three of
# 3,116 citations (1,025 distinct) that no rule in this file ever looked at.
CITED = re.compile(r"^[A-Za-z][A-Za-z0-9_'?!]*(?:(?:\.|::)[A-Za-z0-9_'?!]+)*$")
# The LAST segment of a citation, under either separator.
SEG = re.compile(r"\.|::")
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
        "_" in name or CAMEL.search(name) is not None
        or QUAL.match(name) is not None or "::" in name)


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
    return _core_scan()[0]


def core_namespaces():
    """Source 6's NAMESPACES, read ONLY as the OWNER of a qualified citation.

    `core_declared` reads the toolchain's `LEAN_DECL` lines, which is every
    `def`/`theorem`/`structure`/... and no `namespace` -- so `Classical` was
    declared nowhere, `Classical.choice` resolved on `choice` alone, and 16
    citations of Lean's own choice axiom would have had to be exempted by hand
    the moment the owner test below reached the dotted spans.  Source 1 has
    always read `namespace` for THIS repository (`Tm.LogStamp` is declared by
    `namespace LogStamp`); this is the same rule applied to the toolchain, and
    it is the set the owner test needs, because an owner is a namespace far more
    often than it is a declaration.

    IT IS OWNER-ONLY, and that is the whole of its scope discipline -- the same
    one source 7 uses (consulted only for a citation with no underscore) and
    `rust_variants` uses (only for a `::` span).  920 namespace names, 378 of
    them not already in `core_declared`; as a LAST-segment set those 378 could
    each launder a deleted kernel constant that shared the name, and as an OWNER
    set they can launder nothing at all -- an owner never resolves a citation by
    itself, it only stops one from failing on its owner."""
    return _core_scan()[1]


# (decls, namespaces), read once.  Two consumers, one 0.2 s walk of the pinned
# toolchain's sources: `core_declared` and `core_namespaces` above.
_CORE_SCAN = []


def _core_scan():
    if _CORE_SCAN:
        return _CORE_SCAN[0]
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
    names, spaces = set(), set()
    for path in paths:
        text = read(path)
        for m in LEAN_DECL.finditer(text):
            names.add(m.group(1).split(".")[-1])
        for m in LEAN_NS.finditer(text):
            spaces.update(m.group(1).split("."))
    _CORE_SCAN.append((names, spaces))
    return _CORE_SCAN[0]


def lean_code(text):
    """`text` with every `/- ... -/` block's INSIDE blanked, lines preserved.

    **PROSE DOES NOT DECLARE** (README gap 1312).  `LEAN_DECL` allows leading
    whitespace, so an indented `def f` inside a doc comment declared `f` and a
    citation to a deleted definition resolved to the sentence that described
    its deletion.  DRIVEN: a `/-! ... def w23_probe_renderer ... -/` block
    appended to `Emit.lean` made w23_probe_renderer resolve from the README,
    exit 0.  Comment depth only; `--` line comments are left alone, because a
    `--` in Lean is also a prefix of `---` rules and the declarations it could
    launder are already covered by the block rule.
    """
    out, depth = [], 0
    for line in text.split("\n"):
        opens, closes = line.count("/-"), line.count("-/")
        out.append(line if depth == 0 and opens == 0 else "")
        depth = max(depth + opens - closes, 0)
    return "\n".join(out)


def rust_split(text):
    """ONE walk, BOTH halves: `(code, prose)`, lines preserved in each.

    `rust_code` and `rust_prose` were two scanners of one grammar, and AGENTS
    5.3 is what happened next: `rust_code` grew a CHAR-LITERAL rule -- a `'`
    that opens no literal is a lifetime or a loop label and is ordinary code
    (one_padder.rs's `is_char_literal`, README gap 1201) -- and `rust_prose`,
    written in the same commit, did not.  It opened a quote span at every `'`
    and blanked everything to the next apostrophe, COMMENTS INCLUDED, so a
    `&'static str` anywhere in a file swallowed the prose behind it.  Driven at
    the W-24 repair step, in a scratch copy: two plants three lines apart at
    tm-core/src/emit.rs, with `fn w24_lifetime_probe(x: &'static str)` between
    them, and only the FIRST was reported -- check 8 green on a needle it was
    built to see.  README gap 1416.

    So there is one scanner now and the two functions below select from it.
    The docstrings' claim -- "the exact complement", "every byte of a `.rs`
    file is read by exactly one of the two" -- is a property of this walk
    rather than of two walks agreeing, and a rule added to either half cannot
    be added to only one.  The claim is still not "every byte is READ": a
    string's CONTENTS are deliberately in neither half (a string that is
    exactly an identifier declares it, `STRING_LIT`, and that runs over the raw
    text); what the partition covers is which side of the code/comment line
    each byte falls on.
    """
    def blank(chunk):
        return "".join("\n" if c == "\n" else " " for c in chunk)

    code, prose = [], []
    i, n, depth = 0, len(text), 0
    while i < n:
        c = text[i]
        if depth:
            # `/* */` NESTS in Rust, unlike C.
            if text.startswith("*/", i):
                depth, i = depth - 1, i + 2
                prose.append("  ")
            elif text.startswith("/*", i):
                depth, i = depth + 1, i + 2
                prose.append("  ")
            else:
                code.append("\n" if c == "\n" else " ")
                prose.append(c)
                i += 1
            continue
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            run = text[i:j]
            # The `//`, `///` and `//!` markers are blanked too, so a swept
            # line is ordinary prose and the wrap carry cannot pick a marker
            # up as part of a name.
            k = 2
            while k < len(run) and run[k] in "/!":
                k += 1
            code.append(" " * len(run))
            prose.append(" " * k + run[k:])
            i = j
            continue
        if text.startswith("/*", i):
            depth, i = 1, i + 2
            code.append("  ")
            prose.append("  ")
            continue
        # A RAW string: `r"..."`, `br##"..."##`.  Its body has no escapes, so
        # the terminator is the quote followed by as many `#` as opened it.
        raw = RAW_OPEN.match(text, i)
        if raw:
            close = '"' + "#" * raw.group(0).count("#")
            j = text.find(close, raw.end())
            j = n if j < 0 else j + len(close)
            code.append(raw.group(0)[:-1] + '"' + blank(text[raw.end():j]))
            prose.append(blank(text[i:j]))
            i = j
            continue
        if c == '"' or (c == "b" and text.startswith('b"', i)):
            k = i + (2 if c == "b" else 1)
            if c == "b":
                code.append("b")
            j = k
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            code.append('"' + blank(text[k:j]) + ('"' if j < n else ""))
            stop = min(j + 1, n)
            prose.append(blank(text[i:stop]))
            i = stop
            continue
        # A CHAR literal, which may hold a quote: `'"'`.  A `'` that is not one
        # is a lifetime or a loop label and is ordinary code (one_padder.rs's
        # `is_char_literal`, README gap 1201, in Python).  BOTH halves get this
        # rule because there is only one of it; that is gap 1416's whole fix.
        if c == "'" or (c == "b" and text.startswith("b'", i)):
            k = i + (2 if c == "b" else 1)
            if k < n and text[k] == "\\":
                j = text.find("'", k + 2)
            elif k + 1 < n and text[k + 1] == "'":
                j = k + 1
            else:
                j = -1
            if j >= 0:
                code.append(text[i:k] + blank(text[k:j]) + "'")
                prose.append(blank(text[i:j + 1]))
                i = j + 1
                continue
        code.append(c)
        prose.append("\n" if c == "\n" else " ")
        i += 1
    return "".join(code), "".join(prose)


# ONE SPLIT PER FILE.  `rust_split` is a character-at-a-time Python scanner and
# every `.rs` file goes through it three times -- `declared` wants the code half,
# `rust_variants` wants it again, `cited` wants the prose half -- which is 2/3 of
# this file's added cost for nothing.  Keyed on the TEXT, so a caller that
# synthesises a string (the tests in this file's own plants) still gets the right
# answer and the cache cannot go stale against a file read twice.
_SPLIT = {}


def rust_split_cached(text):
    """`rust_split(text)`, remembered."""
    got = _SPLIT.get(text)
    if got is None:
        got = _SPLIT[text] = rust_split(text)
    return got


def rust_prose(text):
    """The COMMENT half of `rust_split`: comment text only, lines preserved.

    `rust_code` keeps the code and blanks comments; this keeps the comments and
    blanks everything else, INCLUDING the `//`, `///`, `//!` and `/* */`
    markers themselves.  Every byte of a `.rs` file falls on exactly one side
    of that line, which is what makes "prose does not declare" (gap 1312) and
    "prose is cited from" (gap 1313 item 3) the same partition seen from its
    two sides -- and since gap 1416 it is ONE walk that draws the line, so the
    two sides cannot disagree about where it is.
    """
    return rust_split_cached(text)[1]


def rust_code(text):
    """The CODE half of `rust_split`: `//` and `/* */` comments and string/char
    CONTENTS blanked.

    **PROSE DOES NOT DECLARE** (README gap 1312).  `RUST_DECL` has no anchor
    and ran over whole file text, so `// The old fn foo is gone.` declared
    `foo`, and so did the literal `"fn foo"` in a guard that greps for it.
    Both were LIVE: seg_title, deleted at W-23, resolved only from
    `tm/tests/one_renderer.rs`'s needle string and `tm/tests/one_padder.rs`'s
    prose about a plant that was removed before the commit.

    `STRING_LIT` still runs over the RAW text, because a bare `"name"` string
    is a declared source of its own (the wire keys) and not a laundering path:
    it matches a string that is exactly an identifier, never one with a `fn`
    in front of it.

    Lines are preserved so nothing else in this file has to care.
    """
    return rust_split_cached(text)[0]


def declared():
    """The four declaration sets, as one set of short names."""
    names = set()
    for path in LEAN_FILES:
        text = read(path)
        for m in LEAN_DECL.finditer(lean_code(text)):
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
    for path in RUST_FILES:
            text = read(path)
            code = rust_code(text)
            names.update(RUST_DECL.findall(code))
            names.update(RUST_FIELD.findall(code))
            names.update(RUST_PARAM.findall(code))
            names.update(STRING_LIT.findall(text))
    for path in sorted(glob.glob(os.path.join(HERE, "*.py"))):
        for m in PY_DECL.finditer(read(path)):
            names.add(m.group(1) or m.group(2))
    # SOURCE 5 IS `tracked()`, THE SAME POPULATION THE RESIDUE RULE USES (the
    # W-28 repair step).  It was a walk of THREE DIRECTORY NAMES, written out --
    # `tm`, `tm-core`, `kernel` -- which is the shape `leanfiles.py`'s header
    # says cannot work, and the repository ROOT was not on it: `AGENTS.md`,
    # `PLAN-lean-kernel.md`, `tm-spec-v1.md` and `.claude/API-NOTES.md` were
    # files this repository holds whose stems it did not declare.  That cost
    # nothing while a citation resolved on its last segment -- `AGENTS.md`
    # resolved because `md` is a declared name -- and it is the difference
    # between a green check and 72 hand-written exemptions once the owner test
    # below reaches a dotted span.  Measured at the repair step: the walk gave
    # 470 stems and git gives 472; the only two it loses are `__pycache__`
    # bytecode stems (`citations.cpython-312`, `leanfiles.cpython-312`), which
    # are derived output and were never declarations of anything.
    for rel in tracked():
        names.add(os.path.splitext(os.path.basename(rel))[0])
    return names


def rust_variants():
    """Source 3's variant half, CONSULTED ONLY FOR A `::`-SPELLED CITATION.

    Gap 1410 declined this widening at W-24 on exactly the right number: +219
    short names that, resolved on the LAST segment like everything else, would
    each launder a stale citation of any Lean constructor or `def` sharing the
    name -- `All`, `Any`, `Add`, `Bool`, `Body`, `Active`, `Blocked`, `Dates`.
    That cost is real and it is not paid here, because these names are kept OUT
    of `declared()` and consulted only when the span holds `::`.  A variant is
    cited under its enum, never bare; a bare `Blocked` still resolves against nothing
    but the seven sets.  It is the same discipline source 7 uses -- the
    toolchain is consulted only for a citation with no underscore -- and it is
    why turning `::` on costs 0 new laundering on the 34,000 citations that were
    already swept.

    Re-measured at W-27 under this file's own span rule: 481 variant-shaped
    names, 224 of them declared nowhere else, and they resolve 62 of the 121
    `::` citations that would otherwise each need an allow-list entry."""
    names = set()
    for path in RUST_FILES:
        names.update(RUST_VARIANT.findall(rust_code(read(path))))
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
    sources = [(p, read(p)) for p in LEAN_FILES + PLAIN_FILES]
    # THE RUST COMMENTS (W-24).  Read through `rust_prose`, the complement of
    # the `rust_code` that `declared()` reads, so neither half of a `.rs` file
    # can stand in for the other.  `C_FILES` -- the FFI shim, W-27 -- reads the
    # same way and for the same reason.
    for p in RUST_FILES + C_FILES:
        sources.append((p, rust_prose(read(p))))
    for path, text in sources:
        fenced = path.endswith(".md")
        inside = False
        # The carry is the tail of a span left OPEN at the end of a line.  It
        # survives exactly one line boundary and is dropped at a fence, at a
        # line holding ``` and at a line with no backtick at all, because
        # backtick parity inside this repository's prose is only reliable
        # line-locally -- which is why the per-line sweep below is UNCHANGED
        # and this runs beside it rather than replacing it.
        carry = None
        for n, line in enumerate(text.split("\n"), 1):
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


def owner_resolves(segs, names, core, spaces, variants):
    """Does the OWNER of a QUALIFIED path exist, and not only its last segment?

    W-27 turned the :: spans on (README gap 989) and resolved them on the LAST
    SEGMENT ALONE.  So a path whose owner does not exist went green: plant
    "ZzzNoSuchEnum" + "::Done" and "Quux" + "::All" in `mutations.txt` of a
    git-initialised clone of HEAD and check 8 stayed rc=0 with the counts merely
    two higher, while a plain owner-less name planted beside them was named at
    once.  `Done` is one of 14,828 declared names and `All` is a
    `tm-core` one, so neither owner ever had to be real.

    AND IT WAS SCOPED TO `::` AND THAT WAS THE SAME HOLE ONE SEPARATOR OVER (the
    W-28 repair step, README gap 933).  `::` is how RUST spells a path and `.`
    is how LEAN spells one; a rule that holds for one separator and not the
    other is not a property, it is a list with two entries.  DRIVEN in a
    git-initialised clone of HEAD, one line appended to `mutations.txt`: this
    file at W-27 NAMED the `::`-spelled ZzzNoSuchOwner path and was SILENT on
    the dotted one, and on Zzz.ramp beside it.  The dotted half
    was the larger one -- 9,127 citations over 1,983 dotted names with a
    capitalised head, and 824 more over 192 with a lowercase one -- and it was
    at its worst on FILENAMES, because `rs`, `md`, `lean`, `snap`, `a`, `toml`
    and `sh` are all declared names of this repository: every one of this tree's
    `somename.rs` citations resolved on its EXTENSION.  It now resolves because
    the FILE exists (`declared()`'s source 5, which is `tracked()` since the
    same step), and the one LIVE FIND of the widening is a test file the
    README's arithmetic still counts and the tree has not held since 2b26be3
    (log_narrowed_facts.rs, deleted with the log switch, un-backticked here so
    that a sentence recording a dead name does not revive it).

    THE PROPERTY: a qualified citation resolves only if its last segment
    resolves AND some EARLIER segment names something declared.  One rule for
    both separators, and nothing to add to it for a third.

    AND IT WAS NOT THE VARIANT RULE THAT DID IT, which is why this is a
    separate test rather than a tighter `rust_variants`.  The allow-list's
    sentence about that set -- "scoped to :: spans, so it launders nothing" --
    is true of the SCOPE; the laundering was the first rule, `last in names`,
    and the second, `last in core`.  All three are now subject to this.

    Every segment but the last is tried, not just `segs[-2]`, because a test is
    owned through a module chain (`cli::ctx::tests::every_scope_is_..`) whose
    inner segments are not declared names, and because a Lean projection chain
    (`sj.val.kind.isWork`) is owned through its FIELDS: ONE real owner in the
    path is the claim, and a stale rename breaks it.

    THE OWNER SET IS WIDER THAN THE LEAF SET, on purpose and in the only
    direction that is safe.  `core_namespaces` is read here and nowhere else,
    because an owner is a namespace (`Classical.choice`) far more often than it
    is a declaration; an owner cannot resolve a citation by itself, so widening
    it cannot launder a leaf.

    WHAT IT CANNOT SEE: the PAIRING.  `SegKind::Done` and `PErr::Done` resolve
    alike once both names exist somewhere -- this file has no type checker, and
    README gap 1731 stays open for that half.  And a RECEIVER is not an owner:
    `self.blocks_done` names a field of a fork struct through a binder this
    file cannot resolve, so the unresolvable class FAILS and is adjudicated by
    name in `citations-allow.txt` rather than passing silently.  Four foreign
    paths went from silently-resolved to named by the `::` half and are in that
    file where every other library and fork name is: two Rust `std`, one chrono,
    one fork; the dotted half added ten more, eight of them files that do not
    exist.
    """
    return any(seg in names or seg in core or seg in spaces or seg in variants
               for seg in segs[:-1])


def main():
    allow_path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "citations-allow.txt")
    vocabulary, capped = allow_list(allow_path)
    if vocabulary is None:
        return 2
    # THE RESIDUE RULE (the eighth level).  A repository file that is neither
    # swept nor excluded, and an exclusion that covers nothing, are both
    # failures -- the first is the enumeration hole this campaign has found
    # seven times, the second is the counted allow-list's stale-entry ratchet
    # applied to files.
    if UNACCOUNTED or UNUSED_EXCLUSIONS:
        print("%d unaccounted file(s), %d exclusion(s) covering nothing:"
              % (len(UNACCOUNTED), len(UNUSED_EXCLUSIONS)))
        for rel, why in UNACCOUNTED[:20]:
            print("  %s  (%s)" % (rel, why))
        for pat in UNUSED_EXCLUSIONS:
            print("  %s  (excluded, but no file of this repository matches it)" % pat)
        return 1
    names = declared()
    core = core_declared()
    spaces = core_namespaces()
    variants = rust_variants()
    hits, where = cited()

    bad, used = [], set()
    for name, count in sorted(hits.items()):
        segs = SEG.split(name)
        last = segs[-1]
        ok = (
            last in names
            or ("_" not in name and last in core)
            or ("::" in name and last in variants)
        )
        # THE OWNER TEST, FOR EITHER SEPARATOR (W-28).  It was `"::" in name`,
        # which made it a rule about a SPELLING rather than about a path.
        if ok and len(segs) > 1 and not owner_resolves(segs, names, core, spaces, variants):
            ok = False
        if ok:
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
          "%d allow entries unused, %d files swept, %d excluded by %d rule(s)"
          % (sum(hits.values()), sum(hits.values()) - sum(hits[n] for n in used),
             sum(hits[n] for n in used), len(vocabulary), len(capped), len(stale),
             len(LEAN_FILES) + len(PLAIN_FILES) + len(RUST_FILES) + len(C_FILES),
             len(tracked()) - len(LEAN_FILES) - len(PLAIN_FILES) - len(RUST_FILES)
             - len(C_FILES), len(EXCLUDED)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
