#!/usr/bin/env python3
"""Two names for ONE definition: the §5.3 sweep, as a GATE.

AGENTS §5.3 is the rule this kernel is named after -- two definitions of one
concept is the bug -- and track A has swept for it by hand at several steps.
W-29's audit found the cost of hand-sweeping: the run reported *"seventeen
groups, all seventeen accounted for"*, and **five character-identical `def`
pairs were in none of them**, each pair joined by a `@[csimp]` proved by a bare
`rfl`.  W-29 wrote this file so that the number could be re-measured instead of
believed, and left it a SWEEP: it printed thirty groups, exited 0, and said a
gate would need an exemption LIST.

IT DOES NOT (W-30 track A, README gap 2017 closed).  It needs a KEY and TWO
properties, each checked on every run rather than asserted, and what is left
over is the finding.

WHAT IT IS.  Every `def` of the library, keyed on its SIGNATURE and its BODY --
the body normalised to its non-space characters WITH its string literals, which
is the half W-29's key threw away.  The signature is in the key rather than in
an exemption, because two functions of DIFFERENT types that share an expression
are not a duplicate and never were: `obsLe (a b : EnergyObs)` and `obsLineLe
(a b : Obs)` are both `decide (a.line <= b.line)` and neither can be written in
terms of the other.  A group of more than one name under one key is two
definitions of one concept unless one of these holds:

  E2 COMPILED   the compiler emits DIFFERENT code for them AND A CALLER RUNS
                ONE OF THEM.  A `@[csimp]` lemma rewrites the callees of every
                definition compiled AFTER it, so the twin declared below the
                lemma gets the fast callee and the original keeps the slow one;
                the pair is then a SPEC and the body the export actually runs,
                and deleting either would change what runs or what is proved.

                **AND THE SECOND HALF OF THAT SENTENCE WAS NEVER CHECKED**
                (W-30 repair, README gap 2126).  This file said "deleting the
                copy would silently deoptimise the original" and offered
                `Tm.edf` and its twin as the driven example.  The bytes refute
                it: rooted at `tm_kernel_call` (`PlanWire.lean:1198`) over
                `.lake/build/ir/**/*.c`, 2,092 of 11,949 emitted functions are
                reachable and NEITHER `Tm.edf` nor its twin is among them --
                each symbol occurs
                three times in the emitted tree -- a prototype, a body and a
                `___boxed` wrapper, and no call site.  There was no
                deoptimisation to fear because there was no call.  So the
                exemption is now the WHOLE sentence: the bytes differ, and the
                export REACHES at least one of them.  `Tm.planWf`/`planWfFast`,
                `Tm.Seal.daysIn`/`daysInT` and `daysFrom`/`daysFromT` each pass
                it -- in all three the FAST twin is reached and the original is
                the spec it is proved equal to.  edfFast and edfGrantsFast
                answered nothing, and the W-30 repair DELETED them with their
                two `rfl` `@[csimp]` lemmas rather than exempt them.

                This is W-28's lesson in both directions: a claim about a
                definition's SHAPE pins nothing about its BYTES, and a claim
                about its BYTES pins nothing about whether anything CALLS it.

                **THE WALK MOVED TO `callgraph.py` AT W-31**, where check 12
                reads the same graph and check 8 the same symbol inventory,
                and two of this file's three readings of it were WRONG: the C
                symbol was `name.replace(".", "_")` where the toolchain doubles
                an underscore and escapes a `?` (gap 2140), and the qualified
                name came from a line walk that could not see a `private def`
                (gap 2141).  Neither misfired here -- no twin group has a member
                whose name carries punctuation, and an unfound symbol reads as
                "unemitted", which is reported rather than exempted -- and both
                would have been silent one gate over.
  E3 VALUE      the definition takes NO ARGUMENTS AND IS NOT A FUNCTION, so its
                body is a value and not a rule.  Nullary was a SPELLING until
                the W-30 repair (README gap 2128) -- "the signature begins with
                `:`" -- under which `def f : A -> B := fun ..` is a rule wearing
                a value's spelling.  The property is now three tests: no binder
                group, no top-level `->` or `→` in the declared type, and a body
                that is not a `fun`.  All 11 groups E3 answers here are `Nat` or
                `Region` constants and none moves, so the widening costs
                nothing and the rule is no longer about where a `:` stands.  `maxCands : Nat := 1024` and `maxBatch : Nat := 16`
                are two bounds that happen to share a number; `closeW35` and
                `staleW35` are one `Region` under two FIXTURE ROLES, in two
                witness families a hundred lines apart, each family naming its
                own (`staleNow`, `staleW24`, `staleW35`, `staleW37`, ...).
                §5.3 bans two definitions of one CONCEPT, and a named value is
                not one: `mutate.py` draws the same line under the name LITERAL,
                for the same reason, one gate over.  README gap 1956 had already
                adjudicated `closeW35`/`staleW35` exactly this way and this is
                that adjudication mechanised instead of repeated.

A group that neither answers FAILS this check by name.  That is the gate W-29
said would need an exemption list: it needs a sharper key and two properties,
and no list at all.

WHAT IT CANNOT SEE, and the list matters because the hand sweep's own declared
blind spot is where four of the five csimp pairs hid:

  * a duplicate that reaches its own auxiliary BY NAME -- `Tm.reserveOut` calls
    `Tm.availUntil` and `Tm.reserveOutFast` calls `Tm.availUntilFast`, so the
    bodies differ in one identifier and this file reports the AUXILIARIES as the
    twins and not the callers.  It is still named, one level down.  (The
    example this bullet used to give was edf and its twin, which the W-30 repair
    deleted: nothing called either.)
  * a duplicate whose bodies differ by a `let` hoist or an argument order
    (`Tm.sitesInRange` / `sitesInRangeFast` hoists `let n := p.docs.length`) --
    NOT character-identical, and a `@[csimp]`-proved-by-`rfl` grep alone is not
    the rule either.
  * a MONOMORPHIC COPY of a polymorphic definition.  `Replay.ciSum (m : KMap Id
    Nat)` and `Replay.vsum (m : KMap κ Nat)` are both `(m.map Prod.snd).sum` and
    the first is the second at `κ := Id` -- a real §5.3 duplicate that the KEY
    separates, because a signature comparison cannot tell an instance of a type
    from an unrelated one.  README gap 2093 carries it; `vsum` is declared 137 lines
    BELOW `ciSum`'s only caller, so consuming it is a move and not a rename.
  * a NULLARY duplicate that IS one concept -- one bound, or one default,
    written twice under two names -- is exempt by E3 and this gate cannot see
    it.  That is the price of the fixture roles E3 exists for, it is paid on 11
    of the 17 groups here, and README gap 2094 carries it.
  * a `def` whose declaration this key cannot SPLIT into a signature and a
    body.  Lean's `declVal` is `:= <term>`, match arms, or a `where` structure
    instance; this reads the first two, which is 3,044 of the library's 3,044
    `def`s (2,644 `:=` and 400 arms).  AND THE SPLIT IS TAKEN AT BRACKET DEPTH
    ZERO since W-33 (`decl_sep`): it was a flat regex for the first `:=`, and
    `PlannerWit.pCand`'s binder `(h : Look.PlanFacts.wf { planFacts pm l with
    splittable := sp } = true)` holds one, so its signature ended inside its
    own binder and its body began `sp } = true) : Look.Cand ..`.  Four `def`s
    were keyed on garbage -- consistently, so the exact key never misfired on
    them, and the second key below could not have been built on it.  A third form is not skipped -- it is
    COUNTED and the run FAILS, because the hole this closes was exactly a silent
    `continue` (W-30 repair, README gap 2127: 400 `def`s were dropped by `if not
    sep: continue` and the summary printed "2644 def bodies" with no residue, so
    nothing said the population was short by 13%).  Swept under the widened key
    the 400 add no group: the count is 16 before and after.
  * a duplicate spelled as a `theorem`, an `abbrev` or an `instance`.  `def` is
    the population this run's finding is about; widening it is the next step's.
    README gap 1956's other ELEVEN groups are all `theorem`s in `Line.lean` --
    one `by decide` fact proved twice under a rule_ and a row_ name -- and
    they are outside this population by construction, not by accident.
  * a duplicate across the Rust and the Lean sides.
  * E2 answers with the EMITTED code, so it can only answer for a definition the
    compiler emits.  A definition with no `lp_TmKernel_*` function in the module
    it was declared in is UNEMITTED, and unemitted is not an exemption: the
    group is reported, which is the loud direction.

USAGE: `twins.py [--audit] [<dir> ...]` (default: the library).  It exits 1 on
a group no property answers, under either key, and on a stale or unneeded
sentence in `twins-exempt.txt`; `--audit` prints every generalisation group
with the verdict that answered it, which is how a sentence is written.  The emitted C it reads is `lake build`'s own output under
`.lake/build/ir`, so check.sh runs it after check 1 and a missing IR tree is a
hard error rather than a silent pass.

THE SECOND KEY (W-33 track A, README gap 2418).  The key above is EXACT, so a
definition that is another's body with a LITERAL turned into a PARAMETER is
never a twin under it.  W-32's repair found four such definitions in one
module, written independently -- `PlannerWit.pCand`, `pCandDue`, `pCandSmall`
and `bCand` -- with this check green at 14 groups and 0 UNANSWERED: a LIST where
the rule is a CLASS, the thirteenth counted instance, inside the gate named
after §5.3.

  THE PROPERTY.  Two `def`s are in one GENERALISATION GROUP when their result
  types and their bodies are identical once every PARAMETER and every LITERAL
  is a hole.  A parameter is a name the signature binds, erased where it heads
  a token (`r.text.toList` is `_.text.toList`).  A literal is a token that
  denotes a value by itself -- a numeral, a string, a character -- or a
  CONSTRUCTOR applied to holes: `none`, `some _`, `.any`, `true`, an anonymous
  constructor `⟨_, _⟩`, a list `[_, _]`, a tuple `(_, _)`, a parenthesised
  hole, or a structure instance whose every field is a hole.  A constructor is
  a name an `inductive` or a `structure` DECLARES, in this library or in the
  pinned toolchain's `Init` tree (`leanfiles.constructors`, the one scanner
  check 8 also reads), matched on its last segment with the arity the
  declaration gives it -- the qualified declaration's when the name is written
  qualified, else the smallest declared, nullary winning -- so `SegKind.block`
  is a hole and `SegKind.batch _` is a hole and `SegKind.batch x` is not.  A
  constructor in a PATTERN, between `|` and `=>`, is structure and stays.  A
  TACTIC PROOF is a hole too -- a `by` block, to the first `,` or unmatched
  closer at its depth -- because by proof irrelevance it carries no value, so
  `⟨0, by decide⟩` is the literal `0 : Fin 6` (W-34, gap 2577); and a name
  followed by `:=` -- a structure field, a named argument -- is structure,
  never a parameter, whatever the signature binds (W-34, gap 2605).  A body
  that collapses to ONE hole is keyed by the constructor it applies: the same
  collapse with the outermost application kept -- `⟨_, _⟩`, `.obj _`,
  `{ live := _ , .. }` -- and, if even that is one hole (a bare parameter or
  literal: the identity and constant functions), by that hole.  Until W-34
  such a body was NOT KEYED ("a hole carries no rule"), which is how
  `ofNatOver (n d : Nat) : Q := ⟨n, d⟩` beside `Arith.util (need avail : Nat)
  : Q := ⟨need, avail⟩` -- two names for one definition -- passed.

  THE KEY IS COARSER THAN THE RELATION IT GATES, on purpose.  Every pair of
  definitions one of which is the other at a closed value shares it; so do
  some pairs that merely share a shape.  The first direction is the gate.  The
  second is what the properties and the sentences below adjudicate, and the
  cost was measured before the key was chosen: collapsing EVERY all-hole
  application (a global head over holes) formed 87 groups against this key's
  number, and grouped `_ . _` five ways and `_ . isSome` four ways across
  unrelated modules -- a parenthesisation, not a concept.

  A generalisation group that is one exact-key group is that group's, above.
  Every other one is answered by exactly one of, in this order:

  E3 VALUE      per MEMBER now: a nullary non-function member is a fixture
                role (the rule above, unchanged) and drops out.  A group with
                fewer than two RULE members left is answered -- `posOfNat`
                beside three named `Pos` constants is one rule and three
                roles.  EXCEPT A ROLE THAT RE-SPELLS ITS RULE (W-34, gap 2577):
                in a group E5 does not answer, a value whose body IS a rule
                member's with every parameter bound to a closed term
                (`respells`: each parameter one balanced run, consistently; a
                proof hole any run) could have been written `rule a b ..`, and
                FAILS as FIXTURE unless a sentence answers it -- as does a
                test that does not decide within its step budget.  E3's own
                rule hid it: `noonClock : Clock := ⟨43200 % 86400 / 60, by
                omega⟩` beside `Emit.clockOfLocal` was one rule and one role.
  ALPHA         two rule members identical once parameters are NUMBERED --
                the same binder types, the same body, the same literals, and
                only the names differ -- are two names for one definition and
                FAIL, unless E2 above answers them (the compiler emits
                different code and the export reaches one).  This is the
                exact key's own declared blind spot ("an argument order")
                mechanised.
  E5 WRAPPER    the erased body is ONE application -- a single head and holes
                and nothing else: `_ / _`, `Cal.toDay _`, `_.reverse` -- so
                each member is a NAME for that head at fixed arguments, and
                the head is one definition already.  `weekOrdinal n := n / 7`
                and `dateOfT t := t / 86400` are two names for division.
                IN EVERY SPELLING since W-34 (gap 2577): an anonymous
                constructor, a tuple, a list literal, a structure instance or
                update over holes is ONE application of ONE constructor --
                `⟨n, 1⟩` IS `Q.mk n 1`, which this rung answered while it
                refused the other spelling -- and a body that is holes alone
                has no head left to be two definitions of.  So `Arith.ofNat`
                and `Arith.util` are two names for `Q.mk` at fixed arguments;
                ALPHA, above, is what still fails a renamed twin of either.
  E4 WIRE-NAMED the rule members are identical once parameters are numbered
                and differ ONLY in the keys they spell: string and character
                literals, and nullary constructors of a `WIRE_KEY_TYPES` type
                (`Tm.Field.Key`, the line grammar's field key -- `.floor`,
                `.cap`, `.est`) AT A POSITION LEAN RESOLVES TO THAT TYPE: an
                explicit argument of a library `def` whose parameter there is
                typed by it, or the type named qualified (`wire_positions`,
                W-34, gap 2601).  A string literal in this
                kernel is a wire key, a field key or a refusal tag, declared
                by the literal that spells it (check 8's source 2), and a
                definition that spells one is that key's single point of
                definition.  UNTIL THE W-33 REPAIR this sentence said "string
                literals" while the comparand read EVERY nullary constructor
                and every character as a name, so a sibling over `SegKind`
                (`.rest` for `.windDown`) was answered here (gap 2562); four
                of the seven E4 groups are answered on `Key` constructors,
                and they still are.  The three refusal emitters that differ only in
                the key they spell are the pair W-29's string-blind key
                wrongly merged, and this is that adjudication as a property.
  A SENTENCE    `twins-exempt.txt`.  Every remaining group is named there --
                ALL its members, so a fifth member joining an adjudged group
                is a new group with no sentence -- with a verdict that begins
                either `ONE CONCEPT`, a true generalisation, naming the
                definition that should carry the rest, DATED, with an EXIT;
                or `NOT ONE CONCEPT`, DATED, with the sentence that says why.
                W-27's shape: an enumeration you join to be EXEMPT, not to be
                COVERED.  A group with no sentence FAILS; a sentence whose
                group the key does not form FAILS as STALE; a sentence for a
                group a property answers FAILS as one nothing needs; a
                verdict that was ONE CONCEPT at HEAD cannot be rewritten NOT
                ONE CONCEPT -- the debt leaves when the group does, which is
                D46's rule about withdrawal applied here; and a NOT ONE
                CONCEPT verdict the file did not hold at HEAD FAILS (W-33
                repair, gap 2563) -- growth is a ONE CONCEPT debt with an
                EXIT or it is code, so a renamed or widened NOT ONE group is
                re-earned in code too.  A ONE CONCEPT verdict that says
                CARRIED BY `X` is counted carried, not owed, and FAILS unless
                every member's body is one application headed by `X`.

  THE FOUR BLIND SPOTS THE W-33 REPAIR DECLARED HERE ARE CLOSED (W-34 track A,
  README gap 2577), each by a property above and each DRIVEN in a clone --
  rc=0 under the W-33 script and rc=1 under this one, the control rc=0 before
  and after -- with the plant in README's W-34 track A block: a ONE-HOLE body
  is keyed (`ofNatOver (n d : Nat) : Q := ⟨n, d⟩` beside `util` fails ALPHA); a
  `by` block is a hole
  (`⟨l % 86400 / 60, h⟩` beside `⟨l % 86400 / 60, by omega⟩` forms and is
  unanswered); a FIXTURE that re-spells its rule fails (`noonClock : Clock :=
  ⟨43200 % 86400 / 60, by omega⟩`); and a
  short name shared with the field key is a name only where Lean resolves it
  to `Tm.Field.Key` (a `.floor` sibling over a planted type, and a `.machine`
  one over the replay's `Key`,
  each answered WIRE-NAMED before and unanswered now).  The last bullet's
  premise was FALSE when written: `Key` named TWO types, and `.floor`,
  `.cap`, `.est` and fourteen more -- seventeen of its eighteen -- are
  `EditVal`'s constructors too, and six are `CandKey`'s.  The
  limitHistAt example the W-33 bullet gave FORMS now and is answered E5 --
  two names for `dayTake` -- which is that rung's own verdict on
  `weekOrdinal`/`dateOfT`.

  WHAT THE SECOND KEY CANNOT SEE, declared:
  * a MANY-FIELD RECORD re-spelt at DIFFERENT literals inside a one-hole
    body.  Such a body is keyed by its OUTERMOST constructor only and E5
    answers one constructor applied at fixed arguments, so two builders of
    one thirteen-field `Look.Cand` that fix different flags are two names for
    `Prod.mk` here unless they are ALPHA twins or one re-spells the other
    (W3).  The key does not decide how much of a record is a "default"; a
    skeleton key that kept the inner constructors would, and it was not
    taken because nothing measured says where its line is.  Gap 2574's
    instances were folded in CODE (`PlannerWit.oneCand`).
  * W3 asks a VALUE against the RULES of its own group, and only of a group
    E5 does not answer: a value re-spelling a wrapper rule is E5's two names
    for its head, and a rule re-spelling another rule is ALPHA's or E4's.
  * W4 resolves `.c` through a library `def`'s EXPLICIT parameter only: `.c`
    passed to a parameter or a local, placed in a list, a match arm, a
    structure field, or compared with `==`, is not a name -- the loud
    direction, one group E4 does not answer.  `open` is not read either.
  * a `by` block runs to the first `,` or unmatched closer, so inside a
    structure instance written with NEWLINE-separated fields it swallows the
    fields after it: the key is COARSER there -- one more group to answer,
    never one fewer.
  * a generalisation across a DELTA step or a structure ETA.  `bCand` builds
    its facts as `wfPlanFacts pm l h` and `pCand` as `⟨{ planFacts pm l with
    splittable := sp }, h⟩` -- one value under two spellings -- so gap 2417's
    family is TWO groups here, {bCand, pCandSmall} and {cCand, pCand,
    pCandDue}, and one definition in the kernel.  Both are adjudged ONE
    CONCEPT and owed to gap 2417; the bridge between them is a proof, not a
    key, and is written in the sentences.  SINCE THE W-33 LAND STEP the
    carrier exists (`PlannerWit.oneCand`, track G) and the two groups STILL
    FORM: each member is one application of `oneCand` whose facts argument
    names a global (`planFacts`), so it is neither a hole nor E5's one
    application over holes.  README gap 2550; since the W-33 repair the two
    sentences say CARRIED BY `PlannerWit.oneCand`, the gate checks every
    member is headed by it, and the summary counts them carried, not owed.
  * a closed term that is not a literal -- `Diagnostics.empty`, `planFacts 10
    .any` -- turned into a parameter.  A global name is not a hole, for the
    measured reason above.
  * a renamed BODY-LOCAL binder (`fun`, `let`, a pattern variable).  The exact
    key shares this blind spot.
  * a constructor whose short name several declarations share at different
    arities, written bare or in dot form (`.ok` is 1 in `Except` and 2
    elsewhere in `Init`): the smallest arity is taken, and a run of holes
    shorter than it does not collapse.  A definition that SHARES a
    constructor's short name (`Capped.nil`, a `def`) collapses too, which is
    the loud direction -- one more group to answer, never one fewer.
  * a monomorphic instance of a polymorphic type: `ciSum (m : KMap Id Nat)`
    and `vsum (m : KMap κ Nat)` are FORMED here, because binder types are not
    in this key, and carried as a ONE CONCEPT sentence -- the loud direction
    the exact key could not take (README gap 2093).  No "the types differ"
    property was added, because that pair is exactly where it would lie.
  * `abbrev`, `instance`, `theorem`: the population is `def`, as above.
"""
import collections
import hashlib
import pathlib
import re
import subprocess
import sys

import callgraph
import leanfiles
import ratchet

# A `def`'s name, as a keyword TOKEN (`leanfiles.THEOREM`'s discipline).
DEF = re.compile(r"(?<![\w'?!.«])def[ \t\r\n]+([^\s(){}:]+)")
# Where a command begins again: `leanfiles.NEXT_COMMAND`, one spelling.
NEXT_COMMAND = leanfiles.NEXT_COMMAND
# A body that IS a value (`mutate.py`'s LITERAL, same rule and same reason).
LITERAL = re.compile(r"^(?:fun[ \t][^=]*=>[ \t]*)?"
                     r"(true|false|True|False|[0-9]+|\"[^\"]*\"|'.')$")
# One emitted function: its header, then its brace-balanced body.
EMITTED = re.compile(r"(?m)^LEAN_EXPORT[^\n(]*\b(?:l|lp_TmKernel)_(\w+)\([^\n]*\{")
# THE WALK ITSELF IS `callgraph.py` AND NOT THIS FILE'S (W-31 track A).  It was
# written here for E2 and check 12 needs the same graph; two copies of one walk
# would be §5.3's defect inside the two gates that exist to catch it, so the
# root, the population, the edges and the C symbol a Lean name mangles to are
# one module now, and this file is one of its three readers.
# A top-level arrow in a declared TYPE, so that E3's "takes no arguments" is a
# property of the type and not of where the `:` stands.
ARROW = re.compile(r"->|→")
# The code generator's own variable NAMING AND NUMBERING -- a C local is the
# source parameter's name between v_ and a counter -- which says nothing about
# what the function does.  It kept the name until W-33, when the ALPHA rung
# below compared `closeTo (g now)` with `targetContaining (g closedDay)` --
# one body under two parameter names -- and E2 answered "the emitted C differs"
# about the local named after now against the one named after closedDay.  The
# exact key could never meet that case, because two identical bodies name
# their parameters identically.
CVAR = re.compile(r"\bv_[A-Za-z0-9_]*?_\d+_")
# A HOISTED CLOSED TERM, as any of the spellings the code generator gives it:
# the constant itself, its `_value`/`_value_aux_<k>` static data, its `_once`
# cell, its `_init_` function, and a `___boxed__const__<k>` scalar.  Group 1 is
# the constant the family belongs to (W-43 repair, README gap 4500).
CLOSED = re.compile(r"\b(?:_init_)?((?:l|lp_TmKernel)_\w*?___closed__\d+(?:___boxed__const__\d+)?)"
                    r"(?:_value_aux_\d+|_value|_once)?\b")
# Brackets, for the depth-zero split and for the second key's collapse.
OPENERS, CLOSERS = "([{⟨⦃", ")]}⟩⦄"
# The second key's sentences (W-33): every generalisation group no property
# answers, adjudged by name.
EXEMPT_FILE = pathlib.Path(__file__).resolve().parent / "twins-exempt.txt"
ISO_DATE = re.compile(r"\b20\d\d-[01]\d-[0-3]\d\b")
VERDICT = re.compile(r"^(NOT ONE CONCEPT|ONE CONCEPT)\b")
# A ONE CONCEPT debt whose carrier has LANDED says so, and the claim is CHECKED
# (W-33 repair, README gap 2550): every member's body must be one application
# headed by the named carrier, a `def` of the library.  The summary then counts
# the group CARRIED, not OWED -- it said "9 one concept owed" while two of the
# nine were gap 2417's family, paid by `PlannerWit.oneCand` (reuse critic).
CARRIED = re.compile(r"CARRIED BY `([A-Za-z_][A-Za-z0-9_.']*)`")
SUBSCRIPTS = frozenset("₀₁₂₃₄₅₆₇₈₉"
                       "ₐₑₒₓₔₕₖₗₘₙₚₛₜ")

# One `def`, as both keys read it.  `sig`/`body`/`lits` are the EXACT key's
# (whitespace stripped, string contents blanked, the literals' text beside);
# `params` are the names the signature binds, in order; the three token lists
# are the raw signature, body and result type for the second key.  `full` is
# the name `lean` gives it -- POSITIONALLY, the k-th `def` of its file against
# the k-th of `leanfiles.qualified_names` (W-34 track A, README gap 2604).
Def = collections.namedtuple("Def", "path name sig body lits params sigtoks bodytoks restoks lineno full")


def literals(src, stripped, start, stop):
    """The ORIGINAL text of every string literal in `stripped[start:stop]`.

    `leanfiles.strip_comments` blanks a string's CONTENT and keeps its quotes,
    and it is offset-preserving, so the quote positions it leaves index straight
    back into the source.  W-29's key was the stripped body alone, which made
    `refusalJson`, `rowRefusalJson` and `plannerRefusalJson` -- three emitters
    that differ ONLY in the wire key they spell -- one body, and the same for
    every witness fixture in `Boundary.lean`."""
    out, i = [], start
    while True:
        a = stripped.find('"', i)
        if a < 0 or a >= stop:
            return out
        b = stripped.find('"', a + 1)
        if b < 0 or b >= stop:
            return out
        out.append(src[a + 1:b])
        i = b + 1


def decl_sep(chunk):
    """Offset of the separator between a `def`'s signature and its body.

    The first `:=`, or the first arm bar `|` that is not `||`, at BRACKET
    DEPTH ZERO -- a `:=` inside a binder's type (`(h : wf { f with x := v }
    = true)`) is the binder's, not the declaration's.  Character literals are
    stepped over whole, because `'('` is one.  `None` when neither occurs,
    which `main` counts and fails on."""
    depth, i, n = 0, 0, len(chunk)
    while i < n:
        c = chunk[i]
        if c == "'":
            m = leanfiles.CHAR_LIT.match(chunk, i)
            if m:
                i = m.end()
                continue
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth <= 0:
            if c == ":" and chunk.startswith(":=", i):
                return i
            if c == "|" and chunk[i - 1:i] != "|" and chunk[i + 1:i + 2] != "|":
                return i
        i += 1
    return None


def _ident_start(c):
    return (c.isalpha() and c not in "λΠΣ") or c in "_«"


def _ident_char(c):
    return c.isalnum() or c in "_'!?" or c in SUBSCRIPTS


def _read_ident(text, i):
    """The end of the (dotted) identifier that starts at `i`."""
    n = len(text)
    j = i + (1 if text[i] == "." else 0)
    while True:
        if j < n and text[j] == "«":
            k = text.find("»", j)
            j = n if k < 0 else k + 1
        else:
            while j < n and _ident_char(text[j]):
                j += 1
        if j + 1 < n and text[j] == "." and _ident_start(text[j + 1]):
            j += 1
            continue
        return j


def tokens(text):
    """Lean surface tokens: `(kind, text)` with kind STR, CHR, NUM, ID, PROJ or SYM.

    An ID is a dotted identifier (`Cal.instantOf`, `r.text.toList`) or a
    dot-constructor (`.any`, when the dot follows nothing an identifier or a
    closing bracket could be); a PROJ is `.1`; every other non-space character
    is its own SYM, so `:=` is two tokens on both sides of every comparison."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
            continue
        if c == '"':
            j = text.find('"', i + 1)
            j = n - 1 if j < 0 else j
            out.append(("STR", text[i:j + 1]))
            i = j + 1
            continue
        if c == "'":
            m = leanfiles.CHAR_LIT.match(text, i)
            if m:
                out.append(("CHR", m.group(0)))
                i = m.end()
                continue
        if c.isdigit():
            j = i + 1
            while j < n and text[j].isalnum():
                j += 1
            out.append(("NUM", text[i:j]))
            i = j
            continue
        if c == "." and i + 1 < n and text[i + 1].isdigit() and i > 0 and not text[i - 1].isspace():
            j = i + 1
            while j < n and text[j].isdigit():
                j += 1
            out.append(("PROJ", text[i:j]))
            i = j
            continue
        prev = text[i - 1] if i > 0 else " "
        if _ident_start(c) or (c == "." and i + 1 < n and _ident_start(text[i + 1])
                               and not (_ident_char(prev) or prev in CLOSERS
                                        or prev in "»\"'")):
            j = _read_ident(text, i)
            out.append(("ID", text[i:j]))
            i = j
            continue
        out.append(("SYM", c))
        i += 1
    return out


def binders(sig):
    """`(parameter names in order, result type text)` of a signature.

    A binder group is `(x y : T)`, `{a : T}`, `[inst : C]` or `⦃..⦄` at depth
    zero; its names are what stands before its first `:`; `[C a]` binds none.
    The result type is what follows the first depth-zero `:` after the groups,
    and is empty when the declaration writes none."""
    params, i, n, depth, result = [], 0, len(sig), 0, ""
    while i < n:
        c = sig[i]
        if depth == 0 and c in "({[⦃":
            close = CLOSERS[OPENERS.index(c)]
            d, j = 0, i
            while j < n:
                if sig[j] in OPENERS:
                    d += 1
                elif sig[j] in CLOSERS:
                    d -= 1
                    if d == 0:
                        break
                j += 1
            group = sig[i + 1:j]
            if ":" in group:
                head = group.split(":", 1)[0]
            else:
                head = "" if c == "[" else group
            for t in head.split():
                if t and _ident_start(t[0]):
                    params.append(t)
            i = j + 1
            continue
        if depth == 0 and c == ":":
            result = sig[i + 1:]
            break
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        i += 1
    return params, result


def bodies(path, src, code, fulls=None):
    """A `Def` for every `def` declared in `path`, whose source is `src` and
    whose comment-stripped code is `code` -- stripped ONCE by the caller, which
    reads the constructors off the same text.  `fulls` is the file's qualified
    names in declaration order, which `main` has checked agree with this scan.

    A `def` this cannot split yields a body of `None`, which `main` COUNTS and
    fails on.  It used to `continue`, and 400 of the library's 3,044 `def`s --
    every one spelled with match arms rather than `:=` -- were keyed by nothing
    while the summary line said "2644 def bodies" (W-30 repair, gap 2127)."""
    for k, m in enumerate(DEF.finditer(code)):
        stop = NEXT_COMMAND.search(code, m.end())
        end = stop.start() if stop else len(code)
        chunk = code[m.end():end]
        lineno = code.count("\n", 0, m.start()) + 1
        full = fulls[k] if fulls is not None and k < len(fulls) else m.group(1)
        at = decl_sep(chunk)
        if at is None:
            yield Def(path, m.group(1), "".join(chunk.split()), None, (), [], [], [], [], lineno,
                      full)
            continue
        # The separator stays with the BODY: it is what tells `:= e` from the
        # arms `| p => e`, and two definitions written the two ways are not one.
        sig_raw, body_raw = chunk[:at], chunk[at:]
        params, result = binders(sig_raw)
        yield Def(path, m.group(1), "".join(sig_raw.split()), "".join(body_raw.split()),
                  tuple(literals(src, code, m.end() + at, end)), params,
                  tokens(sig_raw), tokens(body_raw), tokens(result), lineno, full)


def emitted(path, name):
    """The normalised BODY of `name`'s emitted C, or None if it is not emitted.

    `path` is the .lean module; the code generator writes its C beside the build
    at `.lake/build/ir/<pkg>/<Module>.c`.  The body is taken brace-balanced from
    the header, so the function's own NAME -- which always differs -- is not part
    of what is compared, and the generator's variable numbering is normalised
    away for the same reason."""
    ir = callgraph.ir_root(path)
    mangled = callgraph.mangle(name)
    for c in sorted(ir.rglob(pathlib.Path(path).stem + ".c")):
        text = c.read_text(errors="replace")
        for m in EMITTED.finditer(text):
            if m.group(1) != mangled:
                continue
            i, depth = m.end() - 1, 0
            while i < len(text):
                if text[i] == "{":
                    depth += 1
                elif text[i] == "}":
                    depth -= 1
                    if depth == 0:
                        body = text[m.end():i]
                        # **AND A HOISTED CONSTANT IS NAMED AFTER ITS PARENT**,
                        # which made E2 exempt a REAL duplicate on its first run
                        # (W-30).  A ___closed__0 constant carrying each of the
                        # two definitions' own names was the ONLY symbol
                        # separating two byte-identical bodies, so the
                        # property answered "the emitted code differs" about a
                        # difference that is the function's own name.  The
                        # function's mangled name is normalised to SELF, which
                        # is the only name in a body that cannot be evidence.
                        body = closed_resolved(ir, body)
                        body = body.replace(mangled, "SELF")
                        return "".join(CVAR.sub("v_", body).split())
                i += 1
    return None


# **A HOISTED CLOSED TERM IS COMPARED BY WHAT IT IS, NOT BY WHOSE NAME IT
# CARRIES** (W-43 repair, README gap 4500).  The code generator shares one
# closed term among every definition of a MODULE that needs it, and names the
# shared constant after the FIRST definition that hoisted it -- so `Log.chronoYear`
# in `Line.c` reads lp_TmKernel_Tm_serializeItem___closed__0 (an empty
# array), while a character-identical copy of it in another module hoists its
# own and reads `..._SELF___closed__0`.  SELF above normalised only the
# definition's OWN name; a constant named after ANOTHER parent still read as
# "the emitted C differs", so E2 answered "COMPILED" about two names for one
# definition (the W-43 auditor's plant: plantChronoYear in MidnightCut.lean,
# accepted).  Every reference to a closed constant is replaced by a digest of
# its DEFINITION -- its static data or its `_init_` body, normalised the same
# way, its own references resolved first -- so two bodies differ here only
# where the terms they compute differ.  A constant whose definition the IR
# does not hold is kept by name: the loud direction, as everywhere in this file.
_CLOSED_DEFS = {}


def closed_defs(ir):
    """Every closed constant's DEFINITION text in the IR tree `ir`, by the
    constant it belongs to: its `_init_` body and its static data (`_value`,
    `_value_aux_<k>`), in file order."""
    key = str(ir)
    if key in _CLOSED_DEFS:
        return _CLOSED_DEFS[key]
    out = collections.defaultdict(list)
    init = re.compile(r"(?m)^static lean_object\* _init_(\w+)\(void\)\{")
    data = re.compile(r"(?m)^static const \w+ (\w+?)(?:_value_aux_\d+|_value) = ")
    for c in sorted(ir.rglob("*.c")):
        text = c.read_text(errors="replace")
        for m in init.finditer(text):
            i, depth = m.end() - 1, 0
            while i < len(text):
                if text[i] == "{":
                    depth += 1
                elif text[i] == "}":
                    depth -= 1
                    if depth == 0:
                        break
                i += 1
            out[m.group(1)].append(text[m.end():i])
        for m in data.finditer(text):
            end = text.find(";\n", m.end())
            out[m.group(1)].append(text[m.end():end if end >= 0 else len(text)])
    _CLOSED_DEFS[key] = (out, {})
    return _CLOSED_DEFS[key]


def closed_digest(ir, name, stack=()):
    """A digest of the closed constant `name`'s definition, its own closed
    references resolved first and its own name normalised; `None` when the IR
    holds no definition of it."""
    defs, memo = closed_defs(ir)
    if name in memo:
        return memo[name]
    if name not in defs or name in stack:
        return None
    own = re.compile(r"(?<!\w)(?:_init_)?" + re.escape(name) + r"(?:_value_aux_\d+|_value|_once)?\b")
    text = own.sub("SELFC", "\n".join(defs[name]))
    text = closed_resolved(ir, text, stack + (name,))
    digest = hashlib.sha1("".join(CVAR.sub("v_", text).split()).encode()).hexdigest()[:16]
    memo[name] = digest
    return digest


def closed_resolved(ir, text, stack=()):
    """`text` with every reference to a closed constant replaced by the digest
    of its definition (a constant with none is kept by name)."""
    def sub(m):
        d = closed_digest(ir, m.group(1), stack)
        return m.group(0) if d is None else "CLOSED_" + d
    return CLOSED.sub(sub, text)


def qualify_all(path, code, found):
    """The qualified name of every `def` of `path`, in declaration order.

    THE SCANNER IS `leanfiles.qualified_names`, check 3's (W-31 track A).  This
    was a line walk of its own that required `def` to be the FIRST WORD of its
    line, so the three `private def`s of `Plan.lean` and the two `@[reducible]
    def`s beside them fell through it and came back qualified by the namespace
    stack AT END OF FILE -- a name no declaration has, whose C symbol is
    therefore absent, which E2 reads as "unemitted" and reports.  The loud
    direction, and wrong.

    **AND THE TABLE WAS KEYED ON THE WRITTEN NAME, first occurrence winning**
    (W-34 track A, README gap 2604), which is `mutate.py`'s gap 1422 inside
    this file: SIX `def`s of the library share a written name with an earlier
    one in the same file -- `Line.lean`'s `setEst` is `Tm.setEst` at line 532
    and `Tm.Field.setEst` at 3817, and `readTz`, `readStep`, `keyOf`, `get`
    and `alter` are the same shape -- and each second one was REPORTED under
    the first one's name, its C symbol read for E2 and its namespace used for
    name resolution.  E4's group read `Tm.setEst` where the member was
    `Tm.Field.setEst`.  The two scanners are now joined by POSITION, and a
    disagreement about which `def`s a file declares is a hard error rather
    than a guess: `found` is this file's own scan, and it must name the same
    `def`s in the same order."""
    pairs, _leftover = leanfiles.qualified_names(path, "def", code=code)
    if [w for w, _ in pairs] != found:
        raise SystemExit("twins.py: %s -- the def scanner and `leanfiles.qualified_names` "
                         "disagree about which `def`s this file declares, so no member "
                         "could be named positionally" % path)
    return [f for _, f in pairs]


def namespace_of(full):
    """`Tm.Field` for `Tm.Field.viewMin`."""
    return full.rsplit(".", 1)[0] if "." in full else ""


def resolve(name, ns, table):
    """What `name`, written inside namespace `ns`, names in `table` -- Lean's
    innermost-first lookup, without `open` (a name only an `open` reaches is
    unresolved, which every reader of this treats as the loud direction)."""
    parts = ns.split(".") if ns else []
    for k in range(len(parts), -1, -1):
        cand = ".".join(parts[:k] + [name])
        if cand in table:
            return cand
    return None


def is_value(sig, body):
    """E3: nullary AND not a function -- a property of the type (gap 2128)."""
    return not sig or (sig.startswith(":") and not ARROW.search(sig)
                       and not body.lstrip(":=").startswith("fun"))


def compiled_apart(group):
    """E2's sentence for `group`, or None: the emitted C differs AND the export
    reaches one of them (gap 2126).  Without `live` this said "the copy is what
    the callers run" about a pair with no caller."""
    seen, live = {}, []
    for d in group:
        q = d.full
        seen["%s:%s" % (d.path, d.full)] = emitted(d.path, q)
        if callgraph.symbol(q) in callgraph.reachable(callgraph.ir_root(d.path))[0]:
            live.append(d.name)
    if None in seen.values():
        return None  # unemitted is not an exemption
    if len(set(seen.values())) > 1 and live:
        return ("E2 COMPILED -- the emitted C differs (%s) and `tm_kernel_call` "
                "reaches %s, so the copy is what the callers run"
                % (", ".join("%s %d chars" % (k.rsplit("/", 1)[-1], len(v))
                             for k, v in sorted(seen.items())), ", ".join(sorted(live))))
    return None


def explain(group):
    """Which property answers for an EXACT-key group, or None if none does.

    The signature is part of the KEY, so a group here already agrees on it and
    there is no "the types differ" exemption to apply."""
    # E3 IS A PROPERTY OF THE TYPE, NOT OF WHERE THE `:` STANDS (gap 2128): no
    # binder group, no arrow in the declared type, and a body that is not a
    # `fun`.  `def f : A -> B := fun ..` used to be read as "a named value".
    if is_value(group[0].sig, group[0].body):
        return ("E3 VALUE    -- nullary: `%s` is a value, and two names for one "
                "value are two roles" % group[0].body[:40])
    return compiled_apart(group)


# ---- the second key -------------------------------------------------------

def constructor_sets(codes):
    """The constructors the library declares and the ones Prelude declares,
    kept APART: `((lib_short, lib_qual), (core_short, core_qual))`.  A short
    name asks the library first and Prelude only if the library declares no
    constructor of that name, so `JVal.str`'s arity is the library's and not
    `Lean.Name.str`'s.  `codes` is the library's comment-stripped text, one
    string per module, stripped once by `main`."""
    lib_s, lib_q = {}, {}
    for code in codes:
        s, q = leanfiles.constructors(code, stripped=False)
        for k, v in s.items():
            lib_s.setdefault(k, set()).update(v)
        for k, v in q.items():
            lib_q.setdefault(k, set()).update(v)
    return (lib_s, lib_q), leanfiles.core_constructors()


def ctor_arity(t, ctors):
    """The explicit arity a constructor token collapses with, or None if `t`
    names no constructor.

    A dot spelling (`.any`) and a bare one (`none`) ask the short name; a
    qualified one (`SegKind.block`, Option's some) asks the declaration of the
    type it names, then the short name.  A dotted token whose FIRST segment is
    lowercase is a projection chain on a variable (`o.day`, `r.text.toList`)
    and never a constructor, whatever its last segment is called -- `day` is a
    `DocKind` and `o.day` is a field.  Of several declared arities the
    smallest is taken, nullary winning, so `SegKind.block` before two sibling
    holes collapses alone."""
    (lib_s, lib_q), (core_s, core_q) = ctors
    if t.startswith("."):
        short = t[1:]
        ar = lib_s.get(short) or core_s.get(short)
    else:
        segs = t.split(".")
        if len(segs) >= 2 and not segs[0][:1].isupper():
            return None
        ar = None
        if len(segs) >= 2:
            ar = lib_q.get((segs[-2], segs[-1])) or core_q.get((segs[-2], segs[-1]))
        if not ar:
            ar = lib_s.get(segs[-1]) or core_s.get(segs[-1])
    if not ar:
        return None
    return 0 if 0 in ar else min(ar)


# (type short name, constructor) for every `structure` or `class` the library
# declares -- a structure has one constructor, so its constructor is what an
# anonymous `⟨..⟩` spells.  Filled once by `main` from `leanfiles.constructors`,
# the one scanner of that concept.  Keyed by the STRUCTURE, not by "a type with
# one constructor": `Arith.Q` is a structure and `Replay.Q` an inductive of
# eighteen, and a table merged by short type name made `Q.mk` look ambiguous
# and left the plant it exists for unkeyed (measured on the first try of this
# repair).  An inductive with one constructor is not read, which errs toward
# keying spellings apart -- the pre-repair behaviour -- never toward a false
# group.
SINGLE = set()
# The constructor tables `main` computes, for the kept keys `alpha_key` builds
# without them (`anon_spelling` needs an arity).
CTORS = []


def single_ctor(t):
    segs = t.split(".")
    return len(segs) >= 2 and (segs[-2], segs[-1]) in SINGLE


def _is_name(t):
    return bool(t) and (t[0].isalpha() or t[0] in ".«")


def collapse(out, ctors, protect=False):
    """Constructor applications over holes become holes, to a fixpoint.

    Not inside a PATTERN (between an arm's `|` and its `=>`), where a
    constructor is structure.  `(_)`, `(_, _)`, `[_]`, `[]`, `⟨_, _⟩` and a
    structure instance or update whose parts are all holes collapse as the
    anonymous constructors they are.

    With `protect`, an application that would span the WHOLE expression after
    `:=` is kept, so a body that is one constructor over holes keeps that
    constructor -- `gen_key`'s key for a one-hole body (W-34, gap 2577)."""
    out = list(out)
    changed = True
    while changed:
        changed = False
        res, i, n, pat = [], 0, len(out), False
        while i < n:
            t = out[i]
            if t == "|":
                pat = True
            elif t == "=" and i + 1 < n and out[i + 1] == ">":
                pat = False
            if not pat:
                if t in ("(", "[", "⟨"):
                    close = {"(": ")", "[": "]", "⟨": "⟩"}[t]
                    j = i + 1
                    while j < n and out[j] in ("_", ","):
                        j += 1
                    if j < n and out[j] == close and (t == "[" or "_" in out[i + 1:j]) \
                            and not (protect and i == 2 and j == n - 1):
                        res.append("_")
                        i = j + 1
                        changed = True
                        continue
                if t == "{":
                    j, ok = i + 1, True
                    while j < n and out[j] != "}":
                        u = out[j]
                        if u in ("_", ",", "with", ":", "=") or \
                                (out[j + 1:j + 3] == [":", "="] and _is_name(u)):
                            j += 1
                            continue
                        ok = False
                        break
                    if ok and j < n and j > i + 1 and not (protect and i == 2 and j == n - 1):
                        res.append("_")
                        i = j + 1
                        changed = True
                        continue
                # A FIELD NAME -- an identifier followed by `:=` -- is structure,
                # not a value, whatever constructor shares its spelling.
                if _is_name(t) and out[i + 1:i + 3] != [":", "="]:
                    ar = ctor_arity(t, ctors)
                    if ar is not None:
                        j = i + 1
                        while j < n and j - i - 1 < ar and out[j] == "_":
                            j += 1
                        if j - i - 1 == ar and not (protect and i == 2 and j == n):
                            res.append("_")
                            i = j
                            changed = True
                            continue
                        # THE KEPT APPLICATION IS SPELLED ONE WAY (W-34 repair,
                        # README gap 2733).  A single-constructor type's
                        # constructor over k holes IS the anonymous constructor
                        # `⟨_, .., _⟩` -- Lean elaborates the two to one term --
                        # and `protect` kept each in its own spelling, so
                        # `def v34Pair (x y : Nat) : Q := Q.mk x y` keyed apart
                        # from `Arith.util`'s `⟨need, avail⟩` and formed NO
                        # group (driven by W-34's verifier: rc=0, group count
                        # unchanged, `--audit` silent), while the same body
                        # spelled `⟨x, y⟩` failed ALPHA.  The property: a kept
                        # constructor of a type with one constructor is re-spelled
                        # anonymously, so the key does not read the spelling.
                        if (j - i - 1 == ar and ar >= 1 and protect and i == 2 and j == n
                                and single_ctor(t)):
                            res.extend(["⟨"] + ["_", ","] * (ar - 1) + ["_", "⟩"])
                            i = j
                            continue
            res.append(t)
            i += 1
        out = res
    return tuple(out)


# THE CONSTRUCTORS E4 READS AS NAMES (W-33 repair, README gap 2562).  E4's
# rule is "differ ONLY in the keys they spell", and a key is spelled two ways
# in this kernel: as a string or character literal on the wire, and as a
# constructor of the line grammar's field-key type, `Tm.Field.Key`
# (`Line.lean`), which `lookupKey`/`setKey` take and whose constructors ARE
# the `est:`, `min:` .. field names.  `normalise(names=True)` used to read
# EVERY nullary constructor as a name, so restSegLike -- `windDownSeg` with
# `.rest` for `.windDown`, a real generalisation over `SegKind` -- was answered
# WIRE-NAMED (driven by W-33's reuse critic in a clone).  This is W-27's shape:
# a type joins this tuple to have its constructors read as names; nothing else
# does.
#
# **THE TUPLE HELD A SHORT NAME, AND THE SHORT NAME WAS TWO TYPES** (W-34
# track A, README gap 2601).  It read `("Key",)`, matched against the last
# segment of the declaring type, and `Replay.lean` declares a second `inductive
# Key` -- the replay's record keys, `machine` and `global` among its nullary
# constructors -- so `.machine` was a "wire name" too.  And the header's claim
# that `Key`'s constructors "collide with no other type's today" was FALSE when
# written: seventeen of `Field.Key`'s eighteen constructors are `EditVal`'s as
# well, and six -- `.floor`, `.cap`, `.due`, `.window`, `.ci`, `.loc` -- are
# `CandKey`'s: FOUR of the seven E4 groups were answered on a short name two
# to five types declare (`.est` is `PlanKey`'s, `ReqCmd`'s and `TokKind`'s
# too).  The answer was right and the reason was not: the
# gate could not tell `Field.Key.floor` from `CandKey.floor`.  So the tuple
# holds the QUALIFIED type, and a dot constructor is a name only when LEAN'S
# OWN RULE resolves it there (`wire_positions`).
WIRE_KEY_TYPES = ("Tm.Field.Key",)

# The tables `wire_positions` resolves against, filled once by `main`: every
# library `def` by the name `lean` gives it, and every `inductive` likewise.
DEFS, TYPES = {}, set()
# Words that open a term rather than apply a function: an argument run stops
# at one of them.
TERM_WORDS = frozenset(("fun", "λ", "if", "then", "else", "match", "with", "let", "in",
                        "do", "return", "by", "have", "show", "from", "at"))


def explicit_types(sigtoks):
    """The declared type of each EXPLICIT parameter of a signature, in order --
    one entry per name of a `(x y : T)` group, as a token list."""
    out, i, n = [], 0, len(sigtoks)
    while i < n:
        kind, t = sigtoks[i]
        if kind == "SYM" and t in "({[⦃":
            depth, j = 0, i
            while j < n:
                if sigtoks[j][0] == "SYM" and sigtoks[j][1] in OPENERS:
                    depth += 1
                elif sigtoks[j][0] == "SYM" and sigtoks[j][1] in CLOSERS:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            group, colon, d0 = sigtoks[i + 1:j], None, 0
            for k, (kk, tt) in enumerate(group):
                if kk == "SYM" and tt in OPENERS:
                    d0 += 1
                elif kk == "SYM" and tt in CLOSERS:
                    d0 -= 1
                elif kk == "SYM" and tt == ":" and d0 == 0:
                    colon = k
                    break
            if t == "(" and colon is not None:
                out.extend(group[colon + 1:] for x in group[:colon] if x[0] == "ID")
            i = j + 1
            continue
        if kind == "SYM" and t == ":":
            break
        i += 1
    return out


def wire_positions(toks, d, ctors):
    """W4 (W-34 track A, README gap 2601): the indices of `toks` that NAME a
    field key -- a nullary constructor of a `WIRE_KEY_TYPES` type, found by
    the rule Lean itself uses for `.c`: the EXPECTED TYPE.

      * `.c` passed as the k-th explicit argument of a library `def` `f` is a
        name when `f`'s k-th explicit parameter is typed by a wire-key type
        that declares `c` nullary -- `lookupKey .floor r`, `setKey .dur (..) r`;
      * `T.c` written qualified is a name when `T` resolves, from the
        definition's own namespace, to a wire-key type declaring `c`.

    Anything else -- `.c` in a list, a match arm, a comparison, passed to a
    parameter or a local, a bare `c` -- is NOT a name: unresolved is the loud
    direction, a group E4 does not answer."""
    if ctors is None:
        return set()
    (_lib_s, lib_q), _core = ctors
    ns, out = namespace_of(d.full), set()
    for i, (kind, t) in enumerate(toks):
        if kind != "ID":
            continue
        ctor, typ = None, None
        if t.startswith(".") and "." not in t[1:]:
            ctor, j, args = t[1:], i - 1, 0
            while j >= 0:
                kk, tt = toks[j]
                if kk == "SYM" and tt in CLOSERS:
                    depth = 0
                    while j >= 0:
                        if toks[j][0] == "SYM" and toks[j][1] in CLOSERS:
                            depth += 1
                        elif toks[j][0] == "SYM" and toks[j][1] in OPENERS:
                            depth -= 1
                            if depth == 0:
                                break
                        j -= 1
                elif not (kk in ("NUM", "STR", "CHR", "PRF", "PROJ")
                          or (kk == "ID" and tt not in TERM_WORDS)):
                    break
                args += 1
                j -= 1
            head = toks[j + 1] if args else None
            if head is None or head[0] != "ID" or head[1].startswith(".") \
                    or head[1].split(".")[0] in d.params:
                continue
            f = resolve(head[1], ns, DEFS)
            types = explicit_types(DEFS[f].sigtoks) if f else []
            if len(types) < args:
                continue
            th = next((tt for kk, tt in types[args - 1] if kk == "ID"), None)
            typ = resolve(th, namespace_of(f), TYPES) if th else None
        elif "." in t and t[:1].isupper():
            segs = t.split(".")
            ctor, typ = segs[-1], resolve(".".join(segs[:-1]), ns, TYPES)
        if ctor and typ in WIRE_KEY_TYPES and \
                0 in lib_q.get((typ.rsplit(".", 1)[-1], ctor), ()):
            out.add(i)
    return out


def erase_proofs(toks):
    """A TACTIC PROOF IS A HOLE (W-34 track A, README gap 2577).

    The second key holes every literal because a literal is a VALUE that a
    parameter could have been; a proof is not even that -- by proof
    irrelevance it carries no value at all, so two bodies that differ in one
    are one body.  The W-33 repair declared the cost: `⟨0, by decide⟩`, a `Fin`
    literal, kept its `by decide` as two NAME tokens, so the anonymous
    constructor around it never collapsed and `limitHistAt (i : Fin 6) .. :=
    dayTake i h B` beside `limitHist .. := dayTake ⟨0, by decide⟩ h B` formed
    no group.  A `by` block is one PRF token now, in EVERY normalisation --
    the key, ALPHA's and E4's comparands -- and runs to the first `,` or
    unmatched closer at its own depth, or to the end of the body.  It may
    run past a newline-separated structure field, which makes the key
    COARSER: one more group to answer, never one fewer."""
    out, i, n = [], 0, len(toks)
    while i < n:
        if toks[i] == ("ID", "by"):
            depth, j = 0, i + 1
            while j < n:
                kk, tt = toks[j]
                if kk == "SYM" and tt in OPENERS:
                    depth += 1
                elif kk == "SYM" and tt in CLOSERS:
                    if depth == 0:
                        break
                    depth -= 1
                elif kk == "SYM" and tt == "," and depth == 0:
                    break
                j += 1
            out.append(("PRF", "_"))
            i = j
            continue
        out.append(toks[i])
        i += 1
    return out


def normalise(toks, params, keep, ctors=None, names=False, protect=False, wires=None):
    """N1 when `keep`: parameters NUMBERED and everything else kept -- the
    ALPHA comparand; with `names`, every token that NAMES rather than measures
    (a string, a character, a field-key constructor at a position `wires`
    holds) is one marker too -- the E4 comparand.  N2 otherwise: every
    parameter and literal a hole and constructors collapsed -- the second key
    itself.  In all three a tactic proof is a hole (`erase_proofs`), and a
    name followed by `:=` -- a structure field, a named argument -- is
    STRUCTURE, kept as written: `{ live := live }` holed the field name because
    the parameter shared its spelling (W-34, gap 2605)."""
    index = {}
    for k, p in enumerate(params):
        index.setdefault(p, k + 1)
    toks = erase_proofs(toks)
    out = []
    for pos, (kind, t) in enumerate(toks):
        if names and wires is not None and pos in wires:
            out.append("#")
        elif kind == "PRF":
            out.append("_")
        elif kind == "STR":
            out.append("#" if names else '""' if keep else "_")
        elif kind == "CHR":
            out.append("#" if names else t if keep else "_")
        elif kind == "NUM":
            out.append(t if keep else "_")
        elif kind == "ID" and toks[pos + 1:pos + 3] == [("SYM", ":"), ("SYM", "=")]:
            out.append(t)
        elif kind == "ID" and not t.startswith("."):
            head, dot, rest = t.partition(".")
            if head in index:
                out.append(("_%d" % index[head] if keep else "_") + (dot + rest if dot else ""))
            else:
                out.append(t)
        else:
            out.append(t)
    return tuple(anon_spelling(out, ctors)) if keep else collapse(out, ctors, protect)


def anon_spelling(out, ctors):
    """A body that IS one structure constructor applied to its k fields, spelled
    `S.mk a b`, re-spelled `⟨a, b⟩` -- Lean elaborates the two to one term.

    The kept keys (ALPHA's and E4's) read the spelling, so `def v34Pair (x y :
    Nat) : Q := Q.mk x y` beside `Arith.util (need avail : Nat) : Q := ⟨need,
    avail⟩` was not an ALPHA twin while the same body spelled `⟨x, y⟩` was
    (W-34's verifier; README gap 2733).  An argument is one token or one
    bracketed group, and a parenthesised argument loses its parentheses, as it
    does inside `⟨..⟩`.  Anything else -- a partial application, an argument
    that is itself an application -- is left as written, which keys apart."""
    out = list(out)
    ctors = ctors or (CTORS[0] if CTORS else None)
    if len(out) < 4 or out[:2] != [":", "="] or ctors is None:
        return out
    head = out[2]
    if not (_is_name(head) and single_ctor(head)):
        return out
    ar = ctor_arity(head, ctors)
    args, i, n = [], 3, len(out)
    while i < n:
        t = out[i]
        if t in OPENERS:
            depth, j = 0, i
            while j < n:
                if out[j] in OPENERS:
                    depth += 1
                elif out[j] in CLOSERS:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            if j >= n:
                return out
            grp = out[i:j + 1]
            args.append(grp[1:-1] if grp[0] == "(" else grp)
            i = j + 1
        elif t in CLOSERS or t in (",", ":", "=", "|"):
            return out
        else:
            args.append([t])
            i += 1
    if not ar or len(args) != ar:
        return out
    res = [":", "=", "⟨"]
    for k, a in enumerate(args):
        if k:
            res.append(",")
        res.extend(a)
    return res + ["⟩"]


ONE_HOLE = (":", "=", "_")


def gen_key(d, ctors):
    """The second key of `d`: its result type and body with every parameter,
    literal and proof a hole.

    **A BODY THAT IS ONE HOLE IS KEYED** (W-34 track A, README gap 2577).  It
    was not -- "a hole carries no rule" -- and the W-33 repair declared what
    that hid: 39 function `def`s whose body is a constructor over their
    parameters were in NO group, so `ofNatOver (n d : Nat) : Q := ⟨n, d⟩`
    beside `Arith.util (need avail : Nat) : Q := ⟨need, avail⟩` -- two names
    for one definition -- passed.  A body that collapses to one hole is keyed
    by the constructor it applies: collapsed to its fixpoint with the OUTERMOST
    application kept (`collapse(protect=True)`), `⟨_, _⟩`, `.obj _`,
    `{ live := _ , .. }`; a body that is one hole even then -- a parameter or
    a literal atom, the identity and the constant functions -- is keyed as
    that hole.  The ladder then answers them like any group: ALPHA fails a
    renamed twin, E5 answers one constructor applied at fixed arguments.

    AND "ONE HOLE" WAS A SLOPPY TEST: `all(t in ("_", ":", "="))` also held
    for `_ == _` (`==` is two `=` tokens) and for a run of holes whose head a
    nullary-arity constructor reading erased, and both were silently unkeyed.
    It is `ONE_HOLE` exactly now."""
    body = normalise(d.bodytoks, d.params, False, ctors)
    if body == ONE_HOLE:
        body = normalise(d.bodytoks, d.params, False, ctors, protect=True)
    return (normalise(d.restoks, d.params, False, ctors), body)


def alpha_key(d):
    """Identical modulo parameter NAMES: binder types, body and literals kept."""
    return (normalise(d.sigtoks, d.params, True), normalise(d.bodytoks, d.params, True))


def named_key(d, ctors):
    """E4's comparand: the BODY once parameters are numbered and every string,
    character and field-key constructor (`wire_positions`) is one marker.  The
    signature is not compared: a pair typed apart AND wire-named is still
    wire-named."""
    toks = erase_proofs(d.bodytoks)
    return normalise(toks, d.params, True, ctors, names=True,
                     wires=wire_positions(toks, d, ctors))


def is_wrapper(body):
    """E5: ONE APPLICATION over holes, in any of its spellings.

    `C _ ..` and `f _ ..` -- one head and holes -- were the whole of it until
    W-34, and the same term spelled `⟨_, _⟩` was not, so E5 answered
    `Q.mk n 1` and refused `⟨n, 1⟩`.  An anonymous constructor, a tuple, a list
    literal and a structure instance or update over holes are ONE application
    of ONE constructor, and a verdict about a term cannot depend on which of
    its spellings the source chose (W-34, gap 2577).  So is a body of holes
    alone: no head survived the erasure -- a parameter applied to parameters,
    or an applied constructor whose short name a nullary constructor also has
    (the arity blind spot below) -- and there is nothing there to be two
    definitions of."""
    if body[:2] != (":", "="):
        return False
    e = body[2:]
    if e and all(t == "_" for t in e):
        return True
    if len(e) >= 3 and (e[0], e[-1]) in (("⟨", "⟩"), ("(", ")"), ("[", "]")) \
            and all(t in ("_", ",") for t in e[1:-1]):
        return True
    if len(e) >= 3 and (e[0], e[-1]) == ("{", "}"):
        inner, k = list(e[1:-1]), 0
        while k < len(inner):
            if inner[k] in ("_", ",", "with"):
                k += 1
            elif inner[k + 1:k + 4] == [":", "=", "_"] and _is_name(inner[k]):
                k += 4
            else:
                return False
        return True
    rest = [t for t in e if t != "_"]
    holes = sum(1 for t in e if t == "_" or t.startswith("_."))
    return holes >= 1 and len(rest) == 1


def matches(pat, sub, env, budget):
    """Does token list `sub` match `pat`, each `_k` bound to one balanced run
    (consistently), a proof hole `_` matching any one balanced run?  `budget`
    is a one-element list of steps left; running out raises `Undecided`."""
    budget[0] -= 1
    if budget[0] < 0:
        raise Undecided()
    if not pat:
        return not sub
    p0 = pat[0]
    head, dot, rest = p0.partition(".")
    var = head[:1] == "_" and head[1:].isdigit()
    if var and dot:
        if not sub or not sub[0].endswith("." + rest):
            return False
        val = (sub[0][:-(len(rest) + 1)],)
        if env.get(head, val) != val:
            return False
        return matches(pat[1:], sub[1:], dict(env, **{head: val}), budget)
    if var and head in env:
        v = env[head]
        return tuple(sub[:len(v)]) == v and matches(pat[1:], sub[len(v):], env, budget)
    if var or p0 == "_":
        for k in range(1, len(sub) + 1):
            v = tuple(sub[:k])
            if not _balanced(v):
                continue
            if matches(pat[1:], sub[k:], dict(env, **{head: v}) if var else env, budget):
                return True
        return False
    if sub and sub[0] == "_":
        # A proof hole in the VALUE answers any one balanced run of the rule.
        for k in range(1, len(pat) + 1):
            if _balanced(pat[:k]) and matches(pat[k:], sub[1:], env, budget):
                return True
        return False
    return bool(sub) and sub[0] == p0 and matches(pat[1:], sub[1:], env, budget)


class Undecided(Exception):
    """The instance test ran out of its step budget -- reported, never passed."""


def _balanced(seq):
    """One term: brackets balanced, no comma at its own depth, and not
    beginning with a separator."""
    depth = 0
    for t in seq:
        if t in OPENERS:
            depth += 1
        elif t in CLOSERS:
            depth -= 1
            if depth < 0:
                return False
        elif t == "," and depth == 0:
            return False
    return depth == 0 and tuple(seq[:1]) not in ((":",), ("=",), ("|",))


def match_toks(d):
    """`d`'s body for the instance test: parameters numbered, proofs holed,
    every literal AS WRITTEN (N1 blanks a string; this must not)."""
    index = {p: k + 1 for k, p in reversed(list(enumerate(d.params)))}
    out = []
    for kind, t in erase_proofs(d.bodytoks):
        if kind == "PRF":
            out.append("_")
        elif kind == "ID" and not t.startswith(".") and t.partition(".")[0] in index:
            head, dot, rest = t.partition(".")
            out.append("_%d" % index[head] + (dot + rest if dot else ""))
        else:
            out.append(t)
    return out


def respells(rule, value):
    """W3 (W-34 track A, README gap 2577): is `value`'s body `rule`'s with
    every parameter bound to a closed term -- a fixture that could have been
    written `rule a b ..`?  True, False, or None when undecided."""
    try:
        return matches(match_toks(rule), match_toks(value), {}, [200000])
    except (Undecided, RecursionError):
        return None


def read_verdicts(path, text=None):
    """`(entries, complaints)`: `{frozenset(names): (verdict, lineno)}`.

    An entry is the group's members, space-separated, then ` -- ` and the
    verdict; a line beginning with whitespace continues the verdict above it;
    a `#` line is prose.  A verdict begins `ONE CONCEPT` or `NOT ONE
    CONCEPT`, carries an ISO date, and a ONE CONCEPT verdict names its EXIT."""
    entries, bad, cur = {}, [], None
    if text is None:
        if not path.exists():
            return entries, bad
        text = path.read_text()
    for lineno, raw in enumerate(text.splitlines(), 1):
        if not raw.strip():
            cur = None
            continue
        if raw.lstrip().startswith("#"):
            continue
        if raw[:1] in (" ", "\t"):
            if cur is None:
                bad.append("%s:%d  a continuation line under no entry" % (path.name, lineno))
            else:
                entries[cur] = (entries[cur][0] + " " + raw.strip(), entries[cur][1])
            continue
        names, sep, verdict = raw.partition(" -- ")
        key = frozenset(names.split())
        if not sep or len(key) < 2:
            bad.append("%s:%d  an entry is `<name> <name> .. -- <verdict>` and this "
                       "is `%s`" % (path.name, lineno, raw[:60]))
            cur = None
            continue
        if key in entries:
            bad.append("%s:%d  the group %s is adjudged twice"
                       % (path.name, lineno, " ".join(sorted(key))))
            cur = None
            continue
        entries[key] = (verdict.strip(), lineno)
        cur = key
    for key, (verdict, lineno) in entries.items():
        if not VERDICT.match(verdict):
            bad.append("%s:%d  a verdict begins `ONE CONCEPT` or `NOT ONE CONCEPT`; "
                       "this one begins `%s`" % (path.name, lineno, verdict[:30]))
        if not ISO_DATE.search(verdict):
            bad.append("%s:%d  the verdict carries no ISO date" % (path.name, lineno))
        if verdict.startswith("ONE CONCEPT") and "EXIT" not in verdict:
            bad.append("%s:%d  a ONE CONCEPT verdict names its EXIT -- what lands "
                       "the carrier and dissolves this group" % (path.name, lineno))
    return entries, bad


def committed_verdicts(path):
    """The sentences as `git` has them at HEAD: the text, `""` when the file is
    not at HEAD yet (its first landing), or None when git cannot say."""
    try:
        ls = subprocess.run(["git", "-C", str(path.parent), "ls-tree", "HEAD", "--", path.name],
                            capture_output=True, text=True, timeout=60)
        if ls.returncode != 0:
            return None
        if not ls.stdout.strip():
            return ""
        show = subprocess.run(["git", "-C", str(path.parent), "show", "HEAD:./" + path.name],
                              capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return None
    return show.stdout if show.returncode == 0 else None


def main(argv):
    audit = "--audit" in argv
    roots = [a for a in argv if not a.startswith("--")] or \
        [str(pathlib.Path(__file__).resolve().parent / "TmKernel")]
    files = set()
    for d in roots:
        files.update(leanfiles.lean_files(pathlib.Path(d)))
    files = sorted(files)
    # EACH FILE IS READ AND COMMENT-STRIPPED ONCE.  The stripper is a character
    # walk, and stripping the library twice -- once for the bodies and once for
    # the constructors -- was measured at +1.5 s on a 1.5 s check.
    texts = {p: pathlib.Path(p).read_text() for p in files}
    codes = {p: leanfiles.strip_comments(texts[p]) for p in files}
    ctors = constructor_sets([codes[p] for p in files])
    for p in files:
        leanfiles.constructors(codes[p], stripped=False, structures=SINGLE)
    CTORS.append(ctors)
    everything = []
    for p in files:
        fulls = qualify_all(p, codes[p], [m.group(1) for m in DEF.finditer(codes[p])])
        everything.extend(bodies(p, texts[p], codes[p], fulls))
        TYPES.update(f for _w, f in leanfiles.qualified_names(p, "inductive", code=codes[p])[0])
    # The library's own declaration of a name wins over a package-root file's
    # (`Negative.lean` and `Goals.lean` are swept and never compiled): name
    # resolution is about the code the export runs.
    for d in sorted(everything, key=lambda d: "/TmKernel/TmKernel/" not in str(d.path)):
        DEFS.setdefault(d.full, d)
    exact, gen, unsplit = collections.defaultdict(list), collections.defaultdict(list), []
    onehole = 0
    for d in everything:
        if d.body is None:
            unsplit.append((d.path, d.name))
        elif d.body:
            exact[(d.sig, d.body, d.lits)].append(d)
            k = gen_key(d, ctors)
            onehole += normalise(d.bodytoks, d.params, False, ctors) == ONE_HOLE
            gen[k].append(d)
    twins = {k: v for k, v in exact.items() if len(v) > 1}
    answered, bad = collections.Counter(), []
    for key in sorted(twins, key=lambda k: (-len(twins[k]), str(k))):
        why = explain(twins[key])
        if why is None:
            bad.append("TWIN: one signature, one body, and no property says why:\n"
                       "    signature %s := %s\n%s"
                       % (key[0] or "(none)", key[1][:60],
                          "\n".join("    %s:%s" % (d.path, d.name) for d in twins[key])))
        else:
            answered[why.split()[0]] += 1
    for path, name in unsplit:
        bad.append("UNSPLIT: `%s` in %s -- a `declVal` this key cannot split into a "
                   "signature and a body, so it is keyed by nothing" % (name, path))

    # THE SECOND KEY.  A group that is one exact-key group was answered above;
    # every other one climbs the ladder in the header, and what no rung
    # answers must have a sentence.
    entries, ebad = read_verdicts(EXEMPT_FILE)
    bad.extend(ebad)
    used, gen_answered, gen_lines = set(), collections.Counter(), []
    for key in sorted(gen, key=lambda k: (-len(gen[k]), str(k))):
        g = gen[key]
        if len(g) < 2 or len({(d.sig, d.body, d.lits) for d in g}) == 1:
            continue
        names = frozenset(d.full for d in g)
        rules = [d for d in g if not is_value(d.sig, d.body)]
        verdict, alpha_group, why = None, False, None
        # W3 (W-34 track A, gap 2577): E3 drops a value as a FIXTURE ROLE, and
        # "one rule and N roles" is answered -- which is where a fixture that
        # RE-SPELLS its rule hid: the value's body is the rule's with every
        # parameter bound to a closed term, so it could have been written
        # `rule a b ..`.  Asked of every value against every rule of a group
        # E5 does not answer; a match, or a test that does not decide, goes to
        # the sentence rung like any unanswered group.
        respelt = []
        if rules and not is_wrapper(key[1]):
            for v in (d for d in g if is_value(d.sig, d.body)):
                for r in rules:
                    got = respells(r, v)
                    if got is not False:
                        respelt.append((v, r, got))
                        break
        if respelt:
            why = "\n".join("    %s:%d  %s %s %s:%d  %s -- write it through its rule"
                            % (pathlib.Path(v.path).name, v.lineno, v.full,
                               "IS" if got else "MAY BE (undecided within the budget)",
                               pathlib.Path(r.path).name, r.lineno, r.full)
                            for v, r, got in respelt)
        elif len(rules) < 2 or len({(d.sig, d.body, d.lits) for d in rules}) == 1:
            verdict = "E3 VALUE"
        else:
            buckets = collections.defaultdict(list)
            for d in rules:
                buckets[(alpha_key(d), d.lits)].append(d)
            alpha_fail, alpha_ok = False, False
            for b in buckets.values():
                if len({(d.sig, d.body, d.lits) for d in b}) > 1:
                    if compiled_apart(b) is None:
                        alpha_fail = True
                        if names not in entries:
                            bad.append("ALPHA: two names for one definition once its "
                                       "parameters are renamed, and no property says why:\n%s"
                                       % "\n".join("    %s:%d  %s"
                                                    % (pathlib.Path(d.path).name, d.lineno,
                                                       d.full) for d in b))
                    else:
                        alpha_ok = True
            if alpha_fail:
                verdict = None
                alpha_group = True
            elif alpha_ok and len(buckets) == 1:
                verdict = "E2 COMPILED"
            elif is_wrapper(key[1]):
                verdict = "E5 WRAPPER"
            elif len({named_key(d, ctors) for d in rules}) == 1 and \
                    len({(normalise(d.bodytoks, d.params, True), d.lits) for d in rules}) > 1:
                # AND A NAME MUST ACTUALLY DIFFER.  Identical bodies over
                # different binder types (`obsLe`/`obsLineLe`, `ciSum`/`vsum`)
                # share the named key too, and nothing wire-named separates
                # them: they are typed apart, and that is a sentence's to say,
                # because it is where a property would lie (gap 2093).
                verdict = "E4 WIRE-NAMED"
        if verdict is None:
            e = entries.get(names)
            if e is None and why is not None:
                verdict = "UNANSWERED"
                bad.append("FIXTURE: a value that re-spells a rule of its group -- its body IS "
                           "the rule's at closed arguments -- and no sentence answers:\n%s"
                           % why)
            elif e is None:
                verdict = "UNANSWERED"
                bad.append("GENERALISATION: one result type, one body once every literal and "
                           "parameter is a hole, and no property or sentence answers:\n"
                           "    %s := %s\n%s\n    -- adjudge it in %s: ONE CONCEPT (name the "
                           "carrier, date it, name the EXIT) or NOT ONE CONCEPT (say why, "
                           "date it)"
                           % (" ".join(key[0]) or "(no result type)", " ".join(key[1])[:100],
                              "\n".join("    %s:%d  %s  (%d params)"
                                        % (pathlib.Path(d.path).name, d.lineno,
                                           d.full, len(d.params))
                                        for d in sorted(g, key=lambda d: (d.path, d.lineno))),
                              EXEMPT_FILE.name))
            else:
                used.add(names)
                verdict = "ONE CONCEPT" if e[0].startswith("ONE CONCEPT") else "NOT ONE CONCEPT"
                m = CARRIED.search(e[0])
                if m and verdict == "ONE CONCEPT":
                    carrier = m.group(1)
                    heads = []
                    for d in g:
                        toks = list(d.bodytoks)
                        k = next((i for i in range(len(toks) - 1)
                                  if toks[i][1] == ":" and toks[i + 1][1] == "="), None)
                        head = toks[k + 2][1] if k is not None and k + 2 < len(toks) \
                            and toks[k + 2][0] == "ID" else None
                        full = resolve(head, namespace_of(d.full), DEFS) if head else None
                        heads.append((d, head, full))
                    if all(full is not None and (full == carrier or full.endswith("." + carrier))
                           and d.full != full for d, _h, full in heads):
                        verdict = "ONE CONCEPT CARRIED"
                    else:
                        bad.append("CARRIED: %s:%d says the group is CARRIED BY `%s`, and %s -- "
                                   "a carried debt is one application of its carrier in every "
                                   "member, or it is owed" % (
                                       EXEMPT_FILE.name, e[1], carrier,
                                       ", ".join("`%s` is headed by `%s`" % (d.name, h or "(no name)")
                                                 for d, h, full in heads
                                                 if not (full and (full == carrier or
                                                                   full.endswith("." + carrier))))
                                       or "a member is its own carrier"))
                if alpha_group and not verdict.startswith("ONE CONCEPT"):
                    bad.append("ALPHA: %s:%d says NOT ONE CONCEPT of two names for one "
                               "definition -- a twin's only honest sentence is ONE CONCEPT "
                               "with an EXIT: %s" % (EXEMPT_FILE.name, e[1],
                                                     " ".join(sorted(names))))
        elif names in entries:
            used.add(names)
            bad.append("UNNEEDED: %s:%d adjudges a group %s already answers -- a sentence "
                       "nothing needs is deleted" % (EXEMPT_FILE.name, entries[names][1], verdict))
        gen_answered[verdict] += 1
        gen_lines.append("GENERALISATION [%s] %s := %s\n%s"
                         % (verdict, " ".join(key[0]) or "(no result type)", " ".join(key[1]),
                            "\n".join("    %s:%d  %s  (%d params)"
                                      % (pathlib.Path(d.path).name, d.lineno,
                                         d.full, len(d.params))
                                      for d in sorted(g, key=lambda d: (d.path, d.lineno)))))
    for names in sorted(set(entries) - used, key=lambda k: entries[k][1]):
        bad.append("STALE: %s:%d adjudges a group the second key does not form -- delete "
                   "it: %s" % (EXEMPT_FILE.name, entries[names][1], " ".join(sorted(names))))
    # THE RATCHET, against the sentences as COMMITTED.  A ONE CONCEPT verdict is
    # a declared debt with an exit; the only way it leaves is the group
    # dissolving, never a rewrite of the verdict.
    prev = committed_verdicts(EXEMPT_FILE)
    if prev is None:
        bad.append("RATCHET UNCHECKED: `git` could not say what %s holds at HEAD, so a ONE "
                   "CONCEPT verdict could have been rewritten NOT ONE CONCEPT unseen"
                   % EXEMPT_FILE.name)
    else:
        prev_entries, _ = read_verdicts(EXEMPT_FILE, prev)
        # AND THE FILE COULD GROW BY THE ONE VERDICT THAT NEVER LEAVES (W-33
        # repair, README gap 2563).  Its header said it "may only SHRINK" and
        # only the STALE direction was checked: driven by W-33's auditor in a
        # clone, `def spanPer (lo hi k : Nat) : Nat := (hi - lo) / k` beside
        # `Look.spanMinutes` plus one dated NOT ONE CONCEPT line gave rc=0 and
        # the summary moved 16 -> 17 adjudged, unflagged.  A ONE CONCEPT line is
        # a DEBT with an EXIT -- D51's shape for growth, a dated reason that
        # says what ends it -- and may be added.  A NOT ONE CONCEPT line has no
        # exit: it is a permanent exemption, and a permanent exemption the file
        # did not hold at HEAD is growth this file does not allow.  A group
        # whose two shapes are two concepts is answered in CODE -- one member
        # written through the other, or both through a carrier E5 then reads as
        # wrappers -- or put to the owner; never by a new sentence.
        for names in sorted(set(entries) - set(prev_entries), key=lambda k: entries[k][1]):
            if entries[names][0].startswith("NOT ONE CONCEPT"):
                bad.append("RATCHET: %s:%d is a NEW NOT ONE CONCEPT verdict -- this file "
                           "may only SHRINK, and the one verdict with no EXIT cannot be "
                           "added: answer the group in code (a carrier E5 reads as "
                           "wrappers) or adjudge it ONE CONCEPT with an EXIT: %s"
                           % (EXEMPT_FILE.name, entries[names][1], " ".join(sorted(names))))
        for names in set(entries) & set(prev_entries):
            if prev_entries[names][0].startswith("ONE CONCEPT") and \
                    entries[names][0].startswith("NOT ONE CONCEPT"):
                bad.append("RATCHET: %s:%d was ONE CONCEPT at HEAD and is NOT ONE CONCEPT now "
                           "-- a debt leaves when its group does, not when its sentence is "
                           "rewritten: %s" % (EXEMPT_FILE.name, entries[names][1],
                                              " ".join(sorted(names))))
    # And every COMMITTED step since `ratchet.BASE` (the W-41 repair, README gap
    # 4132): a NOT ONE CONCEPT verdict a commit added is growth HEAD can no longer see.
    def not_one(t):
        return {" ".join(sorted(k)) for k, (v, _l) in read_verdicts(EXEMPT_FILE, t)[0].items()
                if v.startswith("NOT ONE CONCEPT")}
    hist = ratchet.grown(EXEMPT_FILE, not_one)
    if hist is None:
        bad.append("RATCHET UNCHECKED: git cannot read %s's committed history (README gap 4132)"
                   % EXEMPT_FILE.name)
    else:
        bad.extend(hist)
    if audit:
        for line in gen_lines:
            print(line)
    for line in bad:
        print(line)
    reached, emits = callgraph.reachable(callgraph.ir_root(files[0]))
    # THE TWO "REACHABLE" COUNTS ANSWER DIFFERENT QUESTIONS (README gap 2252,
    # and the caption is W-31's repair of it).  This one is over EMITTED C
    # SYMBOLS -- every function the generator wrote, closures and
    # specialisations included, plus the globals it emits for nullary
    # definitions -- and check 12's is over the library's own `def`s and
    # `abbrev`s.  11,939 functions and 1,244 globals here; 2,926 definitions
    # there.  A brief read the first as the second once.
    print("%d file(s) swept, %d def bodies (%d unsplit), %d group(s) of two or "
          "more names (%d compiled, %d value), %d UNANSWERED; second key over all "
          "%d bodies (%d of them one hole, keyed by their constructor): %d "
          "generalisation group(s) (%d value, %d wrapper, %d wire-named, %d compiled, "
          "%d adjudged: %d one concept owed, %d carried, %d not one), %d UNANSWERED; "
          "%d of %d emitted "
          "C symbols (functions and globals) reachable from %s"
          % (len(files), sum(len(v) for v in exact.values()), len(unsplit),
             len(twins), answered["E2"], answered["E3"],
             sum(1 for b in bad if b.startswith(("TWIN", "UNSPLIT"))),
             sum(len(v) for v in gen.values()), onehole,
             sum(gen_answered.values()), gen_answered["E3 VALUE"], gen_answered["E5 WRAPPER"],
             gen_answered["E4 WIRE-NAMED"], gen_answered["E2 COMPILED"],
             gen_answered["ONE CONCEPT"] + gen_answered["ONE CONCEPT CARRIED"]
             + gen_answered["NOT ONE CONCEPT"],
             gen_answered["ONE CONCEPT"], gen_answered["ONE CONCEPT CARRIED"],
             gen_answered["NOT ONE CONCEPT"],
             sum(1 for b in bad if not b.startswith(("TWIN", "UNSPLIT"))),
             len(reached), len(emits), callgraph.EXPORT_ROOT))
    return 1 if bad or unsplit else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
