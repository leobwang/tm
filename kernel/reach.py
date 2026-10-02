#!/usr/bin/env python3
"""check.sh's check 12 (D51): a definition the compiler emits must be REACHED.

README gap 2130 is the layer nothing below the gate read.  Every other check in
this kernel reads the SOURCE or the THEOREM SET -- check 3 pins the axiom set,
check 8 pins a citation, check 9 pins a body against a constant, check 11 pins
uniqueness -- and the auditor who built the first call-graph walk put the
finding in one sentence: *a definition can be pinned by a theorem, unique,
audited and cited and still be called by nothing, and `Tm.remainingMin` is all
five*.  Three findings of this campaign live in that blind spot and every one
of them was found BY HAND: D50's `assignFold`, referenced seventeen times
inside its own module while reaching nothing; gap 501's `Recur.lean`; and
`Tree.lean` -- ten definitions and thirty-seven theorems -- which nobody had
found at all.

THE PROPERTY.  *A definition not used solely within proofs must be reachable
from `tm_kernel_call`.*  Mechanically: every `def` of the library for which the
code generator EMITS a C function must be reached by the walk from the export,
or be named in `reach-exempt.txt` under a section that says why.  The compiler
is what decides the antecedent and it decides it the only way that cannot be
talked round -- a definition it emits no code for is one nothing can call, and
a definition it DOES emit is code the program either runs or carries dead.

AND THE ROOT IS MEASURED NOW, NOT ASSUMED (W-32, README gap 2229).  The
sentence above was true and the walk that implemented it was rooted at an
ASSUMPTION: that everything `tm_kernel_call` can answer is something a caller
can ask for.  `tm_kernel_call` is a door, not a caller -- what comes through it
is a REQUEST whose top-level keys choose which section runs -- and W-31's track
P found the consequence by hand while pricing R3: `Planner.dayPlan`, §8.2's
whole day planner, is reached from this root and from NO shipped caller,
because `grep -rn '"planner"' tm/src` is empty.  So `sections.py` measures both
sides -- the kernel's own top-level sections, walked from the `@[export]`, and
the requests `tm/src` actually builds -- and a dispatcher for a section nothing
sends contributes only the callees of its absent arms.  289 definitions moved
from reachable to unreachable at that root: the `planner` section's 228, the
`plan` section's 53, and 8 the two share.  The number a gate prints is the
number it can defend, and 1,467 was not it.

WHY THAT ANTECEDENT AND NOT A SOURCE-SIDE ONE.  "Used solely within proofs"
reads like a question about references, and it was measured as one before this
file was written: of the 2,365 emitted `def`s of the FUNCTION-only population
this gate started with, 260 were referenced by at least one `theorem` and by no
`def` at all.  Exempting those 260 by that property
would have been the wrong rule TWICE OVER.  It swallows `Tm.edf` and
`Tm.edfGrants` -- §7's EDF grant machine, whose fast twins the W-30 repair
deleted as dead (gap 2126) and whose originals nothing has called since -- and
it cannot see `Tm.remainingMin`, which nine of `Tree.lean`'s ten definitions
reference from inside their own module, exactly as `assignFold` did.  A rule
that depends on who mentions a name is a rule the blind spot is defined by.  So
the antecedent is the compiler's, the exemptions are NAMED, and the reason each
one carries is readable and dated instead of inferred.

THE EXEMPTION FILE IS W-27'S SHAPE: AN ENUMERATION YOU JOIN TO BE EXEMPT, NOT
TO BE COVERED -- AND SINCE W-41 NOBODY JOINS IT (the campaign's D81 call on README
gap 3953; gap 4043): it is STRICTLY SHRINK-ONLY, as D51 says, so an entry or a
`CLASS` line the file did not hold at HEAD FAILS whatever section or heading it sits
under.  Until W-41 a new entry passed under a NEW section whose reason carried an
ISO date and an EXIT (gap 2259's rule, refined at W-32), the one exemption file of
seven that could grow without the owner; check 13's `fields.ratchet_file` was made
strict at W-40's repair and this is the same rule.  Growth is the owner's to grant,
in the commit that changes this script, never a heading.  `reach-exempt.txt` grandfathers the definitions that were
unreachable on 2026-09-25 -- 952 when the gate landed, 1,459 after the same
day's repair widened the population by the 524 `def`s and `abbrev`s the
compiler emits as a GLOBAL and not as a function (gaps 2257/2258), 1,748 after
W-32 rooted the walk where the binary enters (gap 2229), and 1,756 after W-32
track G's eight witness entries -- each under
a section naming its module, its reason and, where the section GREW the file,
its date; and it may only SHRINK: an entry that becomes reachable, stops being
emitted or stops existing FAILS this check and must be deleted, a
definition that becomes unreachable and is not in the file FAILS it too, and so
does an entry the committed file did not hold.  A
bare threshold -- "no more than N unreachable" -- would have been the
list-shaped answer this campaign has now got wrong eleven counted times, and
gap 2130 says so itself.

AND THE REASON IS NOT PROSE THIS SCRIPT ONLY PRINTS (W-32 repair, gaps
2410-2412).  A reason is what every entry under it inherits, so it is the whole
audit trail of 1,756 definitions -- and three halves of it are checkable.  Its
CENSUS ("N of its M emitted definitions are reached") is re-derived against the
table `--audit` prints, which found twenty-three of twenty-seven false at
`9d7fad2`.  A REWRITE of a reason an existing entry already inherits costs an
ISO date, because the ratchet compared entry KEYS and a wholesale replacement
of an existing section's reason was free.  (A NEW section named an EXIT as well
as a date until W-41, when a new section became a place no new entry may stand.)

WHAT THE FILE'S OWN SIZE IS FOR.  It is also the floor under the C symbol
computation.  `callgraph.symbol` is the pinned toolchain's mangling
transcribed; if a toolchain change moved the scheme, most definitions would
stop matching any emitted symbol, hundreds of entries would go STALE at once
and this check would fail by name -- rather than quietly finding nothing to
gate.  That is why a stale entry is a failure and not a warning.

WHAT IT CANNOT SEE, beyond `callgraph.py`'s own declared blind spots:

  * A definition that runs only at LOAD, from a hoisted closed constant.  That
    is `callgraph.closed_users`, it is 108 symbols today of which 32 are
    exempt here, and this file NAMES the class on every entry it touches
    instead of leaving it to be rediscovered: the property is "reachable from
    the export", and a load-time initialiser is not the export.
  * WHETHER A REACHED DEFINITION IS REACHED FOR A REASON.  A call from a
    reachable function is a call; a definition reached only from a refusal path
    nothing takes is reachable here.  Reachability is a floor under
    composition, never a proof of it.
  * A definition the compiler emits nothing for -- 216 of the library's 3,142
    `def`s and `abbrev`s.  The sentence here used to read "677 of 3,042 `def`s,
    every one of them a `Prop`, a type-level abbreviation or a declaration in
    the package root, which `lake` does not compile into the library at all",
    and it was FALSE BY 524: those 524 ARE compiled into the library, as
    `LEAN_EXPORT lean_object* <sym>;` globals, and the sentence was this gate's
    own header asserting its blind spot was empty (W-31 repair, gap 2257).
    `--audit` prints the population so the number is re-measured, not believed.
  * The Rust side, which is R3's business and not a Lean symbol's.
  * Two library modules whose file STEMS collide -- the comparison below is by
    stem, because that is how the code generator names its output, and the
    library is flat today.

AND IT CHECKS THE TREE IT READS, BOTH WAYS (README gap 2149).  A gate that reads
a build answers for the source only if the two agree: every library module must
have emitted C, which is AGENTS 2.3's rule that an unimported module is compiled
by nothing and gated by nothing -- check 1's own comment says it "proves nothing
about a module nobody imports" -- and every emitted C file must have a library
module, because `lake` does NOT delete the artefacts of a module you delete.
Two were found on the first run: ProbeLeaf.c and W21Audit.c, left by probes
deleted on 2026-09-22 and 2026-09-19, 10 emitted functions between them, none
reachable, and they had been inflating the emitted population every gate quoted
(11,945; it is 11,935).

USAGE: `reach.py [--audit] [<dir> ..]` (default: the library).  It exits 1 on a
definition no section answers for and on a stale entry.  `--audit` prints the
census and every unreachable definition with its module, which is how an entry
is adjudicated -- it never writes the file, because a ratchet a script can
regenerate is not a ratchet.
"""
import collections
import os
import pathlib
import re
import sys

import callgraph
import leanfiles
import mutate
import ratchet
import sections as reqsec

EXEMPT_FILE = pathlib.Path(__file__).resolve().parent / "reach-exempt.txt"
# The shipped binary's source.  The walk's root is derived from the requests
# `tm/src` builds, never assumed to be everything the export can answer
# (`sections.py`, README gap 2229).
RUST_SRC = pathlib.Path(__file__).resolve().parent.parent / "tm" / "src"
# THE POPULATION IS A KEYWORD CLASS AND NOT THE ONE WORD `def` (W-31 repair,
# README gap 2258).  This read `qualified_names(p, "def")` and said nothing
# about the others, while `mutate.py` had read `(def|abbrev|instance)` since
# W-24 and `twins.py` at least DECLARED the gap.  MEASURED on the committed
# tree: four library `abbrev`s had an emitted C FUNCTION, were unreachable, and
# were named in no exemption -- `Tm.jrenderNat`, `Tm.Planner.posLt`,
# `Tm.Planner.victimLt`, `Tm.PlannerWit.permissive` -- and with the global half
# of the emitted population (gap 2257) the `abbrev` count is 36.  `instance` is
# NOT here and the omission is declared: an instance is emitted, but it is
# reached through typeclass dispatch the generator resolves at the CALL SITE,
# so an unreached instance symbol is not the same finding and would need its
# own adjudication -- README gap 2260.
KEYWORDS = ("def", "abbrev")


def library_defs(roots):
    """`(defs, files)`: every `def` under `roots`, and the files it came from.

    A def is `(module, written, qualified, symbol)`.  The walk is
    `leanfiles.lean_files` -- the one enumeration five checkers now share --
    and the qualified name is `leanfiles.qualified_names`, the scanner check 3
    reconciles the axiom audit with.  Neither is this file's own."""
    files = set()
    for d in roots:
        files.update(leanfiles.lean_files(pathlib.Path(d)))
    files = sorted(files)
    out = []
    for p in files:
        for kw in KEYWORDS:
            pairs, leftover = leanfiles.qualified_names(p, kw)
            if leftover:
                raise SystemExit("reach.py: %s leaves %s open at end of file -- "
                                 "the qualified name of every declaration below "
                                 "it is wrong" % (p, leftover))
            for written, qualified in pairs:
                out.append((pathlib.Path(p).name, written, qualified,
                            callgraph.symbol(qualified)))
    return out, files


# An ISO date in a section's reason.  A REWRITE must be DATED (gap 2411); until
# W-41 growth had to be too (gap 2259), and there is no growth now.
SECTION_DATE = re.compile(r"\b20\d\d-[01]\d-[0-3]\d\b")
# THE EXIT A NEW SECTION HAD TO NAME (W-32 repair, README gap 2412) IS GONE WITH
# THE NEW SECTION ITSELF (W-41, gap 4043).  It was asked of GROWTH only -- a new
# dated section, and a new `CLASS` line -- and the strict ratchet below refuses
# both whatever they carry, so a rule about what they must say would be a rule
# nothing can reach.  The sections that name one keep it as prose.
# THE NUMERIC HALF OF A REASON IS RE-DERIVED, NOT READ (W-32 repair, README gap
# 2410).  A section's reason is what every entry under it inherits, and
# twenty-seven of them state a census of their module -- "N of its M emitted
# definitions are reached".  Twenty-three of the twenty-seven were FALSE on the
# tree that landed them: `## Planner.lean` said "178 of its 221" where the
# measurement is 0 of 236, because W-32 rewrote the file under a new root and
# re-derived none of the headings it moved.  That half of a reason is a number
# this script already computes, so it is checked here rather than believed --
# §5.11's rule, applied inside the gate D51 is.  A reason that TALKS about this
# census in any other spelling fails too: the evasion of a count you must state
# correctly is a count you do not state, and this makes that visible.
#
# WHAT IT DOES NOT READ, DECLARED.  This is one spelling of ONE quantity --
# reached-of-emitted, per module, over the whole population.  A reason stating a
# DIFFERENT quantity (the four W-31 widening sections say "0 of this module's
# 152 emitted globals are read by a function the export reaches", which is a
# count of a sub-population this script does not compute per module) is not
# re-derived and is still a reader's job.  Widening to those is a second
# measurement, not a second regex, and it is not done on a guess.
CENSUS = re.compile(r"(\d+) of its (\d+) emitted definitions are reached")
CENSUS_TOPIC = re.compile(r"emitted definitions are reached")

# TWO CLASSES ARE ANSWERED BY PROPERTY, NOT BY NAME (W-33 repair, README gap
# 2560).  The file grew 1,756 -> 1,772 in W-33 and the growth was lawful by D51's
# letter -- two new dated sections with EXITs -- and it was the wrong SHAPE: 509
# of its 1,772 entries were two classes this script already measures, listed
# name by name, so every definition a planner step added had to be added here
# too, and "may only shrink" meant "grows by one dated section per step until
# R3".  A list where the rule is a class, the fourteenth counted instance.
# Both classes are stated where they are measured now, and the names left the
# file:
#
#   * UNSENT.  A definition the export reaches ONLY through a section `tm/src`
#     sends no request for.  `sections.py` already measures the cut; what was
#     listed by hand was its CONSEQUENCE, 296 names in eighteen sections that
#     all said "reached from the export ONLY through the request's `planner`
#     section".  The class is computed by walking the graph again with the
#     DECLARED unsent keys uncut: whatever that walk reaches and the real one
#     does not is answered by the key's `CLASS unsent <key> -- <reason>` line in
#     the exemption file.  Only a DECLARED key answers.  A section that stops
#     being sent tomorrow is not in the file, so its definitions arrive as NOT
#     EXEMPT by name -- gap 2229's finding cannot be absorbed silently.  A
#     declared key that is SENT, or that no longer exists, FAILS as STALE.  The
#     class line is ratcheted like a section: new at HEAD needs a date and an
#     EXIT, and a rewrite needs a date.
#   * WITNESS.  A definition of a module in `mutate.WITNESS_MODULES` -- check
#     9's own enumeration of EXACT PATHS, reused rather than minted (213 names
#     in six sections, every one `PlannerWit.lean`).  It is answered only while
#     `mutate.witness_violations()` is empty: that is the LEAF property, checked
#     by the same function check 9 fails on, and the moment a library module
#     imports a witness module every one of its unreached definitions is NOT
#     EXEMPT here by name.
#
# An entry the file still lists for a definition a class answers FAILS as
# ANSWERED BY PROPERTY -- delete it -- so the two cannot both answer, and the
# file can only get shorter by this route.  WHAT THE CLASSES CANNOT SEE, declared:
# a definition that is reached through an unsent section FOR NO REASON -- the
# walk's own blind spot above ("whether a reached definition is reached for a
# reason") applies inside the cut subtree exactly as it does outside it; and a
# witness module's definitions are exempt whatever they are, which is mutate.py's
# conjunct (c) caveat ("the rule is about a module, not about a body") restated,
# with the leaf property as the thing that keeps it cheap.
#
# A THIRD CLASS, PROOF (W-35 repair, README gap 2923).  `PlanCheck.lean` is
# L26's checker battery (D28): its definitions are the predicates the proved
# laws quantify over, and nothing calls them.  The file listed them name by
# name -- 61 entries in three sections -- and every predicate a step added
# grew it by one dated section: W-35 track K's `owedByItsGrant` did exactly
# that (EXEMPT 1262 -> 1263, gap 2803), the list-where-the-rule-is-a-class
# shape the WITNESS class above was built to end.  The property is the one
# that makes the module unreachable BY CONSTRUCTION, and it is checked, not
# assumed: no library module imports it except a WITNESS module and a
# declaration-free manifest (`proof_violations`, the witness class's own
# import scan).  A definition the export cannot reach unless some module that
# can reach anything imports its module is answered by its module's `CLASS
# proof <Module> -- <reason>` line.  Only a DECLARED module answers; the line
# is ratcheted like an unsent one (new: a date and an EXIT; rewritten: a
# date); and the moment another module imports it, every unreached definition
# of it is NOT EXEMPT by name.  What it cannot see: a definition of such a
# module that SHOULD have a caller -- the class says "unreachable by
# construction", not "unreachable for a good reason", which is the reason
# line's job, read by a person.
CLASS_LINE = re.compile(r"^CLASS[ \t]+(unsent|proof)[ \t]+([A-Za-z0-9_]+)[ \t]+--[ \t]+(.+)$")


def proof_violations(stem):
    """Why `CLASS proof <stem>` may not be trusted, as sentences: the module is
    not a library module, or a library module that is neither a WITNESS
    module nor a declaration-free manifest imports it -- mutate.py's
    `witness_violations` scan, applied to one more module."""
    files = set(mutate.lib_files())
    target = "TmKernel/TmKernel/%s.lean" % stem
    if target not in files:
        return ["%s is named by `CLASS proof %s` and is not a library module"
                % (target, stem)]
    name = mutate.module_name(target)
    out = []
    for path in sorted(files - set(mutate.WITNESS_MODULES) - {target}):
        text = mutate.read(os.path.join(mutate.HERE, path))
        if not mutate.decl_spans(text):
            continue  # an import manifest declares nothing and reaches nothing
        for line in text.split("\n"):
            head = line.split("--", 1)[0].rstrip()
            if head.startswith("import ") and head[len("import "):].strip() == name:
                out.append("%s imports %s, so its definitions are reachable from "
                           "code check 12 audits and `CLASS proof %s` answers "
                           "nothing" % (path, name, stem))
    return out


def read_exemptions(path, text=None):
    """`(entries, sections, complaints)` from the exemption file.

    `sections` is a LIST of `(module, reason, lineno)` in file order,
    `entries` is `{(module, name): (note, section index)}` and `classes` is
    `{section key: (reason, lineno)}`, one per `CLASS unsent <key> -- <reason>`
    line (W-33 repair, gap 2560: a class is answered by what the walk
    measures, never by a name).  A `##` line opens a
    section and carries the reason every entry under it inherits; a `#` line is
    prose; anything else is an entry, with an optional `#` note of its own.  A
    `EXEMPT <n>` line declares the size, which must match exactly.

    **AND THE REASON AN ENTRY CARRIED WAS NOT THE ONE WRITTEN ABOVE IT**
    (W-31 repair, README gap 2259).  `sections` was `{module: reason}` and every
    `##` line OVERWROTE its module's reason, while `entries` was keyed by
    `(module, name)`: so a SECOND heading for a module the file already sectioned
    silently rewrote the reason inherited by every pre-existing entry of that
    module, and nothing complained -- the count did not move either, because the
    dict had one key for both.  DRIVEN before this repair: a second `##
    Emit.lean -- AUDIT DRIVE: an entirely made-up reason that no human ever
    read.` appended at the end of the file left `sections["Emit.lean"]` holding
    the made-up reason for all four of Emit.lean's entries, `complaints` empty,
    and the summary still saying "45 section(s)".  The reason is attached to the
    ENTRY now, at the line it was read on, so a second heading is a second
    section and inherits nothing backwards -- which is also what lets a gate
    WIDENING grandfather a module that already has a section (gap 2257)."""
    entries, sections, complaints, classes = {}, [], [], {}
    cur, declared = None, None
    for lineno, raw in enumerate((path.read_text() if text is None
                                  else text).splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        if line.startswith("CLASS"):
            # A class line answers a MEASURED class, not a name (gap 2560).
            m = CLASS_LINE.match(line)
            if m is None:
                complaints.append("%s:%d  a class line is `CLASS unsent|proof <key> "
                                  "-- <reason>` and this one is `%s`"
                                  % (path.name, lineno, line))
                continue
            # The PROOF class is keyed `proof:<Module>` so it can share this
            # map, and the ratchet below, with the unsent keys.
            key = m.group(2) if m.group(1) == "unsent" else "proof:" + m.group(2)
            if key in classes:
                complaints.append("%s:%d  `CLASS %s %s` is declared twice"
                                  % (path.name, lineno, m.group(1), m.group(2)))
            else:
                classes[key] = (m.group(3).strip(), lineno)
            continue
        if line.startswith("##"):
            head = line[2:].strip()
            module, _, reason = head.partition("--")
            module, reason = module.strip(), reason.strip()
            if not module.endswith(".lean") or not reason:
                complaints.append("%s:%d  a section is `## <Module.lean> -- <reason>` "
                                  "and this one is `%s`" % (path.name, lineno, head))
                cur = None
            else:
                sections.append((module, reason, lineno))
                cur = len(sections) - 1
            continue
        if line.startswith("#"):
            continue
        if line.startswith("EXEMPT "):
            declared = line.split()[1]
            continue
        name, _, note = line.partition("#")
        name, note = name.strip(), note.strip()
        if cur is None:
            complaints.append("%s:%d  `%s` sits under no section, so it carries no "
                              "reason" % (path.name, lineno, name))
            continue
        module = sections[cur][0]
        if (module, name) in entries:
            complaints.append("%s:%d  `%s` is listed twice under %s"
                              % (path.name, lineno, name, module))
            continue
        entries[(module, name)] = (note, cur)
    used = {c for _, c in entries.values()}
    for k, (module, reason, lineno) in enumerate(sections):
        if k not in used:
            complaints.append("%s:%d  the `## %s` section holds no entry -- a "
                              "reason nothing carries" % (path.name, lineno, module))
    if declared is None or not declared.isdigit():
        complaints.append("%s  has no `EXEMPT <n>` line, so its size is not declared"
                          % path.name)
    elif int(declared) != len(entries):
        complaints.append("%s  declares EXEMPT %s and holds %d entries -- the count "
                          "is the ratchet, so correct it in the same edit"
                          % (path.name, declared, len(entries)))
    return entries, sections, complaints, classes


def committed_exemptions(path, rev="HEAD"):
    """The exemption file's text as `git` has it at HEAD, or `None`.

    **THE RATCHET WAS A COMMENT** (W-31 repair, README gap 2259).  D51 asked for
    a file that may only SHRINK; the file's own header says so and `reach.py`'s
    teaching line forty lines away told the next track to "add it to
    reach-exempt.txt .. AND raise the EXEMPT count in the same edit".  Both
    shipped in the same commit, and the only mechanical rule was `int(declared)
    == len(entries)` -- a number held against ITSELF.  The file went EXEMPT 952
    -> 953 in the run that landed it and every gate stayed green.

    So the comparand is the COMMITTED file, which is the only thing in this tree
    that a working copy cannot edit.  `main` holds the new entry set against it,
    and SINCE W-41 STRICTLY (the campaign's D81 call on README gap 3953; gap
    4043): an entry or a `CLASS` line the committed file did not hold FAILS,
    whatever section or heading it sits under.  From the W-31 repair until W-41 a
    new entry passed under a section heading new at HEAD whose reason carried an
    ISO DATE (and, from W-32, an EXIT) -- growth as a dated section in the diff
    rather than a digit in it -- and D51 says this file only SHRINKS.

    WHAT IT STILL CANNOT SEE, declared: whether a REWRITTEN reason is TRUE (it
    costs an ISO date, gap 2411).  No gate can read a sentence.  It reads the
    file at HEAD, so a commit that grew the file passed the NEXT run's comparand
    -- until the W-41 repair (README gap 4132), which holds every commit since
    `ratchet.BASE` against its first parent as well (`ratchet.grown`).  `rev`
    reads another commit's copy (the history walk's structure lookups)."""
    import subprocess
    try:
        out = subprocess.run(["git", "-C", str(path.parent), "show",
                              rev + ":./" + path.name],
                             capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return None
    return out.stdout if out.returncode == 0 else None


def main(argv):
    audit = "--audit" in argv
    roots = [a for a in argv if not a.startswith("--")] or \
        [str(pathlib.Path(__file__).resolve().parent / "TmKernel")]
    defs, files = library_defs(roots)
    if not files:
        raise SystemExit("reach.py: no .lean file under %s" % ", ".join(roots))
    # The IR is `lake`'s own output BESIDE the package, so it is found from a
    # FILE of the library and never from the directory named on the command
    # line -- `.lake/build/ir` sits inside that directory, not above it.
    ir = callgraph.ir_root(files[0])
    # THE TREE THIS READS MUST BE THE SOURCE'S, BOTH WAYS (W-31, gap 2149).
    # `.lake/build/ir` is where the package builds, so the package is two
    # levels above it, and its LIBRARY is `leanfiles.library_files` -- the
    # enumeration that names the root module as well as the directory.
    pkg = ir.parents[2]
    # THE ROOT IS MEASURED AND NOT ASSUMED (W-32, README gap 2229).  The export
    # is a door: a section `tm/src` never sends is a room nobody enters, and
    # `sections.py` reads both sides -- the kernel's own top-level sections,
    # walked from the `@[export]`, and the requests the shipped binary builds --
    # to cut the arms no request takes.
    # `defs` is handed in rather than rebuilt: it is already every `(module,
    # written, qualified)` of the library, and asking `leanfiles.qualified_names`
    # for it a second time cost 1.16 s on a check whose wall was 1.6 s.
    cuts, wire, wirebad, keyed = reqsec.cuts(pkg, RUST_SRC, defs)
    # A ROOT THAT COULD NOT BE MEASURED IS NOT A ROOT, AND NO VERDICT IS TAKEN
    # FROM IT (W-32 repair, README gap 2413).  `wirebad` used to be appended to
    # the adjudication's own complaints and everything below ran anyway -- so an
    # unreadable request printed its own true complaint *beside* six FALSE ones
    # ("no request the shipped binary can build reaches it" about definitions a
    # request does reach) and the teaching line then told the reader to exempt
    # them.  DRIVEN before this: one unrecognised sibling key in
    # `kernel_log.rs`'s only shipped send of `emit` accused the whole of D16's
    # log WRITER of having no caller.  The two questions are ordered now: the
    # root is measured first, and if it cannot be, this says only that.  Every
    # check below -- the exemption adjudication, the ratchet, the census, the
    # stale-artefact sweep -- reads a reachable set derived from the root, so
    # none of them has an answer worth printing until the root has one.
    if wirebad:
        for line in wirebad:
            print(line)
        print("  -- check 12's root is the set of sections `tm/src` actually sends "
              "(README gap 2229).  Until every line above is resolved, this walk "
              "does not know what a user can reach, so it takes NO verdict about "
              "any definition: nothing here says a definition is unreachable, and "
              "nothing here says an exemption is stale.  Fix the root and run "
              "again.")
        print("ROOT NOT MEASURED: %d complaint(s) about the requests %s builds; "
              "%d def/abbrev(s) in the library were not adjudicated"
              % (len(wirebad), RUST_SRC, len(defs)))
        return 1
    reached, emitted = callgraph.reachable(
        ir, {callgraph.symbol(k): {callgraph.symbol(v) for v in vs}
             for k, vs in cuts.items()})
    library = {p.stem: p for p in leanfiles.library_files(pkg)}
    compiled = {c.stem for c in ir.rglob("*.c")}
    closed = callgraph.closed_users(ir)

    population = [d for d in defs if d[3] in emitted]
    if not population:
        raise SystemExit("reach.py: not one of %d `def`/`abbrev`s matches an emitted C symbol "
                         "-- the mangling or the `%s` prefix has moved and this check "
                         "would gate nothing" % (len(defs), callgraph.PREFIX))
    live = [d for d in population if d[3] in reached]
    dead = {(d[0], d[2]): d for d in population if d[3] not in reached}

    entries, sections, bad, classes = read_exemptions(EXEMPT_FILE)
    # THE TWO CLASSES, MEASURED (gap 2560; the declaration is above
    # `CLASS_LINE`).  UNSENT: walk again with the DECLARED unsent keys' cuts
    # lifted; what that walk reaches and the real one does not is the class.
    proofs = {k[len("proof:"):]: v for k, v in classes.items() if k.startswith("proof:")}
    unsents = {k: v for k, v in classes.items() if not k.startswith("proof:")}
    declared_cuts = {q for k in unsents for q in keyed.get(k, ())}
    for k in sorted(unsents):
        if k not in keyed:
            bad.append("STALE: %s:%d  `CLASS unsent %s` answers for a section "
                       "that is %s -- delete the line; every definition it "
                       "answered is now REACHED or NOT EXEMPT by name"
                       % (EXEMPT_FILE.name, unsents[k][1], k,
                          "SENT by %s" % RUST_SRC if any(
                              line.split()[:2] == ["SENT", k] for line in wire)
                          else "not a section the walk cut"))
    via, _ = callgraph.reachable(
        ir, {callgraph.symbol(q): {callgraph.symbol(v) for v in vs}
             for q, vs in cuts.items() if q not in declared_cuts})
    unsent = {k for k, d in dead.items() if d[3] in via}
    # WITNESS: check 9's own enumeration and check 9's own leaf test.
    wviol = mutate.witness_violations()
    for v in wviol:
        bad.append("WITNESS: %s -- so no definition of it is answered by the "
                   "witness class here either" % v)
    wmods = set() if wviol else {pathlib.Path(m).name for m in mutate.WITNESS_MODULES}
    witness = {k for k in dead if k[0] in wmods}
    # PROOF: a declared module no auditable module imports (gap 2923).
    pmods = set()
    for stem in sorted(proofs):
        pviol = proof_violations(stem)
        for v in pviol:
            bad.append("PROOF: %s -- so no definition of it is answered by the "
                       "proof class here either" % v)
        if not pviol:
            pmods.add(stem + ".lean")
    proof = {k for k in dead if k[0] in pmods} - witness
    answered = unsent | witness | proof
    for stem in sorted(set(library) - compiled):
        bad.append("UNCOMPILED: %s is a library module and `lake` emitted no C "
                   "for it -- nothing imports it (AGENTS 2.3), so this check and "
                   "every other one that reads the build is silent about every "
                   "definition in it" % library[stem])
    for stem in sorted(compiled - set(library)):
        bad.append("STALE ARTEFACT: %s has no library module -- it is what a "
                   "DELETED module left behind, and this walk reads its functions "
                   "as if they were emitted; delete it" % (ir / "TmKernel" / (stem + ".c")))
    for key in sorted(dead):
        if key in answered and key in entries:
            bad.append("ANSWERED BY PROPERTY: %s (%s) is %s, and this file still "
                       "names it -- delete the entry; a class and a name may not "
                       "both answer, and the file only shrinks this way (gap 2560)"
                       % (key[1], key[0], "a witness fixture of a leaf module"
                          if key in witness else
                          "a definition of a declared proof-only module"
                          if key in proof else
                          "reached only through a declared unsent section"))
        if key not in entries and key not in answered:
            d = dead[key]
            bad.append("NOT EXEMPT: %s (%s) is emitted and no request the shipped "
                       "binary can build reaches it from %s%s"
                       % (d[2], d[0], callgraph.EXPORT_ROOT,
                          " -- it does run at load, from a hoisted closed "
                          "constant" if d[3] in closed else ""))
    known = {(d[0], d[2]) for d in population}
    for key in sorted(entries):
        if key in dead:
            continue
        if key in known:
            bad.append("STALE: %s (%s) is REACHED now -- delete this entry, the file "
                       "may only shrink" % (key[1], key[0]))
        else:
            bad.append("STALE: %s (%s) is not an emitted `def`/`abbrev` of that "
                       "module any more -- delete this entry" % (key[1], key[0]))
    # THE NUMERIC HALF OF EVERY REASON, RE-DERIVED (W-32 repair, gap 2410).
    # A heading's census is a second copy of a number this script computes, and
    # twenty-three of the twenty-seven copies were wrong on the tree that landed
    # them.  It is held against the measurement now, the way `EXEMPT <n>` is
    # held against the entry count, so a reason cannot go stale in silence.
    for module, reason, lineno in sections:
        emit = sum(1 for d in population if d[0] == module)
        reach = emit - sum(1 for k in dead if k[0] == module)
        m = CENSUS.search(reason)
        if m is None:
            if CENSUS_TOPIC.search(reason):
                bad.append("CENSUS: %s:%d  the `## %s` section's reason talks about "
                           "its module's emitted definitions and states no `<n> of "
                           "its <m> emitted definitions are reached` -- that is the "
                           "one spelling this gate can re-derive, and a census it "
                           "cannot read is a census nothing checks"
                           % (EXEMPT_FILE.name, lineno, module))
            continue
        if (int(m.group(1)), int(m.group(2))) != (reach, emit):
            bad.append("CENSUS: %s:%d  the `## %s` section's reason says %s of its "
                       "%s emitted definitions are reached and the measurement is "
                       "%d of %d -- every entry below inherits that reason, so "
                       "correct it in the same edit (`--audit` prints the table)"
                       % (EXEMPT_FILE.name, lineno, module, m.group(1), m.group(2),
                          reach, emit))
    # THE RATCHET, against the file as COMMITTED and not against itself
    # (gap 2259), and STRICT since W-41 (the campaign's D81 call on README gap
    # 3953; gap 4043): a line the committed file did not hold -- an entry, or a
    # `CLASS` line -- FAILS, whatever section or heading it stands under.  Until
    # W-41 a new entry passed under a NEW section whose reason carried an ISO date
    # and an EXIT, and a new `CLASS` line with a date and an EXIT: the escape
    # check 13's `fields.ratchet_file` closed at W-40's repair (gap 3953), the
    # same rule here.  A heading groups lines and licenses nothing.
    prev = committed_exemptions(EXEMPT_FILE)
    if prev is None:
        bad.append("RATCHET UNCHECKED: `git show HEAD:./%s` gave nothing, so the "
                   "only comparand this file has is itself -- which is the state "
                   "D51's ratchet was in before W-31's repair" % EXEMPT_FILE.name)
    else:
        prev_entries, prev_sections, _, prev_classes = read_exemptions(EXEMPT_FILE, prev)
        for k, (reason, lineno) in sorted(classes.items()):
            spelled = k.replace("proof:", "proof ") if k.startswith("proof:") else "unsent " + k
            if k not in prev_classes:
                bad.append("RATCHET: %s:%d  `CLASS %s` is a NEW class line, held by no "
                           "line at HEAD -- this file may only SHRINK (D51), and a class "
                           "answers every definition behind it (README gaps 3953 and "
                           "4043)" % (EXEMPT_FILE.name, lineno, spelled))
            elif reason != prev_classes[k][0] and not SECTION_DATE.search(reason):
                bad.append("RATCHET: %s:%d  `CLASS %s`'s reason has been "
                           "REWRITTEN and carries no ISO date (gap 2411's rule)"
                           % (EXEMPT_FILE.name, lineno, spelled))
        for key in sorted(set(entries) - set(prev_entries)):
            module, _, lineno = sections[entries[key][1]]
            bad.append("RATCHET: %s (%s) is a NEW exemption, held by no entry at HEAD -- "
                       "this file may only SHRINK (D51), whatever section it stands under "
                       "(README gaps 3953 and 4043; the section at line %d)"
                       % (key[1], module, lineno))
        # AND THE REASON AN ALREADY-GRANDFATHERED ENTRY CARRIES IS PINNED TOO
        # (W-32 repair, gap 2411).  The loop above examines only entries whose
        # KEY is new, so the reason above 1,756 entries that already existed was
        # held by nothing: DRIVEN before this rule, `## Recur.lean`'s whole
        # reason -- its gap-501 citation, its ISO date and its exit -- was
        # replaced with an invented sentence and this gate printed the unchanged
        # summary at rc=0, silently re-parenting all 58 of its entries onto the
        # fabrication.  That is gap 2259's own class one layer out, in the file
        # W-31 repaired it in.  A rewrite now costs what growth cost until
        # W-41: an ISO DATE in the reason it is rewritten to.  What it still cannot
        # read is whether the new sentence is TRUE -- but the numeric half is
        # re-derived above, and an undated rewrite fails by name.
        for key in sorted(set(entries) & set(prev_entries)):
            module, reason, lineno = sections[entries[key][1]]
            was = prev_sections[prev_entries[key][1]][1]
            if reason != was and not SECTION_DATE.search(reason):
                bad.append("RATCHET: %s:%d  the `## %s` section's reason has been "
                           "REWRITTEN and carries no ISO date, and %s inherits it "
                           "-- the reason is the only thing that makes a "
                           "grandfathered entry auditable, so changing one costs "
                           "a date (gap 2411)"
                           % (EXEMPT_FILE.name, lineno, module, key[1]))

    # AND AGAINST THE FILE'S COMMITTED HISTORY (the W-41 repair, README gap 4132):
    # the comparand above is HEAD, so growth that reached a COMMIT was invisible
    # to every later run -- driven by W-41's verifier, a committed entry gave
    # rc=0 and `EXEMPT 1200`.  Every commit since `ratchet.BASE` is held against
    # its first parent by this file's own reader.
    def keys(text):
        ents, _secs, _c, cls = read_exemptions(EXEMPT_FILE, text)
        return {"%s %s" % k for k in ents} | {"CLASS %s" % k for k in cls}
    hist = ratchet.grown(EXEMPT_FILE, keys)
    if hist is None:
        bad.append("RATCHET UNCHECKED: git cannot read %s's committed history since %s, so "
                   "growth that reached a commit is invisible (README gap 4132)"
                   % (EXEMPT_FILE.name, ratchet.BASE[:9]))
    else:
        bad.extend(hist)

    if audit:
        for line in wire:
            print(line)
        per = collections.Counter(m for m, _ in dead)
        print("%-24s %6s %6s %6s %6s" % ("module", "emit", "reach", "unreach", "load"))
        for module in sorted(per):
            emit = sum(1 for d in population if d[0] == module)
            print("%-24s %6d %6d %6d %6d"
                  % (module, emit, emit - per[module], per[module],
                     sum(1 for d in dead.values() if d[0] == module and d[3] in closed)))
        for key in sorted(dead):
            print("  %-22s %s%s" % (key[0], key[1],
                                    "   (load-time)" if dead[key][3] in closed else ""))
    for line in bad:
        print(line)
    # A GATE THAT BLOCKS SHOULD ALSO TEACH.  The next track to meet this check
    # will meet it by adding a witness fixture nothing calls, which is a normal
    # thing to do and has two correct answers; printing neither is how a gate
    # becomes something to route around.
    if any(b.startswith("NOT EXEMPT") for b in bad):
        print("  -- give it a caller the export reaches, or a property a class "
              "already answers (a witness module, a declared proof-only module, "
              "a declared unsent section).  %s is STRICTLY SHRINK-ONLY since "
              "W-41 (D51; README gaps 3953 and 4043): an entry it did not hold at "
              "HEAD fails under any section, and growth is the owner's to grant "
              "in the commit that changes reach.py" % EXEMPT_FILE.name)
    print("%d def/abbrev(s) in %d library module(s), %d emitted (%d as a global), "
          "%d reachable from %s over the %d section(s) tm/src sends (%d cut), "
          "%d exempt in %d section(s) (%d of them run at load), "
          "%d answered by property (%d reached only through %d declared unsent "
          "section(s), %d witness fixture(s), %d of %d declared proof-only "
          "module(s)), %d UNANSWERED"
          % (len(defs), len(library), len(population),
             sum(1 for d in population if d[3] in callgraph.emitted_globals(ir)),
             len(live), callgraph.EXPORT_ROOT,
             sum(1 for line in wire if line.startswith("  SENT")), len(cuts),
             len(entries), len(sections),
             sum(1 for k, d in dead.items() if d[3] in closed and k in entries),
             len(answered), len(unsent), len(unsents), len(witness), len(proof),
             len(proofs), len(bad)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
