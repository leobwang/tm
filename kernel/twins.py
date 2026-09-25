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
    `def`s (2,644 `:=` and 400 arms).  A third form is not skipped -- it is
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

USAGE: `twins.py [<dir> ...]` (default: the library).  It exits 1 on a group no
property answers.  The emitted C it reads is `lake build`'s own output under
`.lake/build/ir`, so check.sh runs it after check 1 and a missing IR tree is a
hard error rather than a silent pass.
"""
import collections
import pathlib
import re
import sys

import callgraph
import leanfiles

# A `def`'s name, as a keyword TOKEN (`leanfiles.THEOREM`'s discipline).
DEF = re.compile(r"(?<![\w'?!.«])def[ \t\r\n]+([^\s(){}:]+)")
# Where a command begins again: a non-space character in column zero.
NEXT_COMMAND = re.compile(r"(?m)^\S")
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
# A separator between a `def`'s SIGNATURE and its BODY.  Lean's `declVal` is
# `:= <term>` or match arms (`| pat => ..`); a `|` that is `||` is Boolean or.
DECL_SEP = re.compile(r":=|(?<!\|)\|(?!\|)")
# A top-level arrow in a declared TYPE, so that E3's "takes no arguments" is a
# property of the type and not of where the `:` stands.
ARROW = re.compile(r"->|\u2192")
_QUALIFIED = {}
# The code generator's own variable numbering, which differs between
# any two functions and says nothing about what they do.
CVAR = re.compile(r"\bv_([A-Za-z0-9_]*?)_\d+_")


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


def bodies(path):
    """`(name, signature, body, literals)` for every `def` declared in `path`.

    A `def` this cannot split yields a body of `None`, which `main` COUNTS and
    fails on.  It used to `continue`, and 400 of the library's 3,044 `def`s --
    every one spelled with match arms rather than `:=` -- were keyed by nothing
    while the summary line said "2644 def bodies" (W-30 repair, gap 2127)."""
    src = pathlib.Path(path).read_text()
    code = leanfiles.strip_comments(src)
    for m in DEF.finditer(code):
        stop = NEXT_COMMAND.search(code, m.end())
        end = stop.start() if stop else len(code)
        chunk = code[m.end():end]
        sep = DECL_SEP.search(chunk)
        if sep is None:
            yield (m.group(1), "".join(chunk.split()), None, ())
            continue
        # The separator stays with the BODY: it is what tells `:= e` from the
        # arms `| p => e`, and two definitions written the two ways are not one.
        at = m.end() + sep.start()
        yield (m.group(1), "".join(chunk[:sep.start()].split()),
               "".join(chunk[sep.start():].split()),
               tuple(literals(src, code, at, end)))


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
                        body = body.replace(mangled, "SELF")
                        return "".join(CVAR.sub(r"v_\1_", body).split())
                i += 1
    return None


def qualified(path, name):
    """`name` under the namespace its file opens, which is what the C is keyed on.

    THE SCANNER IS `leanfiles.qualified_names`, check 3's (W-31 track A).  This
    was a line walk of its own that required `def` to be the FIRST WORD of its
    line, so the three `private def`s of `Plan.lean` and the two `@[reducible]
    def`s beside them fell through it and came back qualified by the namespace
    stack AT END OF FILE -- a name no declaration has, whose C symbol is
    therefore absent, which E2 reads as "unemitted" and reports.  The loud
    direction, and wrong."""
    key = str(path)
    if key not in _QUALIFIED:
        pairs, _leftover = leanfiles.qualified_names(path, "def")
        table = {}
        for written, full in pairs:
            table.setdefault(written, full)
        _QUALIFIED[key] = table
    return _QUALIFIED[key].get(name, name)


def explain(group):
    """Which property answers for this group, or None if none does.

    The signature is part of the KEY, so a group here already agrees on it and
    there is no "the types differ" exemption to apply."""
    body, sig = group[0][3], group[0][2]
    # E3 IS A PROPERTY OF THE TYPE, NOT OF WHERE THE `:` STANDS (gap 2128): no
    # binder group, no arrow in the declared type, and a body that is not a
    # `fun`.  `def f : A -> B := fun ..` used to be read as "a named value".
    if not sig or (sig.startswith(":") and not ARROW.search(sig)
                   and not body.lstrip(":=").startswith("fun")):
        return ("E3 VALUE    -- nullary: `%s` is a value, and two names for one "
                "value are two roles" % body[:40])
    seen, live = {}, []
    for path, name, _sig, _body, _lits in group:
        seen["%s:%s" % (path, name)] = emitted(path, qualified(path, name))
        if callgraph.symbol(qualified(path, name)) in callgraph.reachable(
                callgraph.ir_root(path))[0]:
            live.append(name)
    if None in seen.values():
        return None  # unemitted is not an exemption
    if len(set(seen.values())) > 1 and live:
        # AND THE EXPORT REACHES ONE OF THEM (gap 2126).  Without `live` this
        # said "the copy is what the callers run" about a pair with no caller.
        return ("E2 COMPILED -- the emitted C differs (%s) and `tm_kernel_call` "
                "reaches %s, so the copy is what the callers run"
                % (", ".join("%s %d chars" % (k.rsplit("/", 1)[-1], len(v))
                             for k, v in sorted(seen.items())), ", ".join(sorted(live))))
    return None


def main(argv):
    roots = argv or [str(pathlib.Path(__file__).resolve().parent / "TmKernel")]
    groups = collections.defaultdict(list)
    files = set()
    for d in roots:
        files.update(leanfiles.lean_files(pathlib.Path(d)))
    unsplit = []
    for p in sorted(files):
        for name, sig, body, lits in bodies(p):
            if body is None:
                unsplit.append((p, name))
            elif body:
                groups[(sig, body, lits)].append((p, name, sig, body, lits))
    twins = {k: v for k, v in groups.items() if len(v) > 1}
    answered, bad = collections.Counter(), []
    for key in sorted(twins, key=lambda k: (-len(twins[k]), str(k))):
        why = explain(twins[key])
        if why is None:
            bad.append((key, twins[key]))
        else:
            answered[why.split()[0]] += 1
    for key, group in bad:
        print("TWIN: one signature, one body, and no property says why:")
        print("    signature %s := %s" % (key[0] or "(none)", key[1][:60]))
        for path, name, _s, _b, _l in group:
            print("    %s:%s" % (path, name))
    for path, name in unsplit:
        print("UNSPLIT: `%s` in %s -- a `declVal` this key cannot split into a "
              "signature and a body, so it is keyed by nothing" % (name, path))
    reached, emits = callgraph.reachable(callgraph.ir_root(sorted(files)[0]))
    print("%d file(s) swept, %d def bodies (%d unsplit), %d group(s) of two or "
          "more names (%d compiled, %d value), %d UNANSWERED; %d of %d emitted "
          "C functions reachable from %s"
          % (len(files), sum(len(v) for v in groups.values()), len(unsplit),
             len(twins), answered["E2"], answered["E3"], len(bad),
             len(reached), len(emits), callgraph.EXPORT_ROOT))
    return 1 if bad or unsplit else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
