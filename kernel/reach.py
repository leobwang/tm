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
TO BE COVERED.  `reach-exempt.txt` grandfathers the definitions that were
unreachable on 2026-09-25 -- 952 when the gate landed, 1,459 after the same
day's repair widened the population by the 524 `def`s and `abbrev`s the
compiler emits as a GLOBAL and not as a function (gaps 2257/2258) -- each under
a section naming its module, its reason and, where the section GREW the file,
its date; and it may only SHRINK: an entry that becomes reachable, stops being
emitted or stops existing FAILS this check and must be deleted, and a
definition that becomes unreachable and is not in the file FAILS it too.  A
bare threshold -- "no more than N unreachable" -- would have been the
list-shaped answer this campaign has now got wrong eleven counted times, and
gap 2130 says so itself.

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
import pathlib
import re
import sys

import callgraph
import leanfiles

EXEMPT_FILE = pathlib.Path(__file__).resolve().parent / "reach-exempt.txt"
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


# An ISO date in a section's reason.  Growth must be DATED (gap 2259).
SECTION_DATE = re.compile(r"\b20\d\d-[01]\d-[0-3]\d\b")


def read_exemptions(path, text=None):
    """`(entries, sections, complaints)` from the exemption file.

    `sections` is a LIST of `(module, reason, lineno)` in file order and
    `entries` is `{(module, name): (note, section index)}`.  A `##` line opens a
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
    entries, sections, complaints = {}, [], []
    cur, declared = None, None
    for lineno, raw in enumerate((path.read_text() if text is None
                                  else text).splitlines(), 1):
        line = raw.strip()
        if not line:
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
    return entries, sections, complaints


def committed_exemptions(path):
    """The exemption file's text as `git` has it at HEAD, or `None`.

    **THE RATCHET WAS A COMMENT** (W-31 repair, README gap 2259).  D51 asked for
    a file that may only SHRINK; the file's own header says so and `reach.py`'s
    teaching line forty lines away told the next track to "add it to
    reach-exempt.txt .. AND raise the EXEMPT count in the same edit".  Both
    shipped in the same commit, and the only mechanical rule was `int(declared)
    == len(entries)` -- a number held against ITSELF.  The file went EXEMPT 952
    -> 953 in the run that landed it and every gate stayed green.

    So the comparand is the COMMITTED file, which is the only thing in this tree
    that a working copy cannot edit.  `main` holds the new entry set against it:
    an entry that is not in the committed file must sit under a section heading
    that is not in the committed file EITHER, and that heading's reason must
    carry an ISO DATE.  Adding a line to an existing section -- which is exactly
    what W-31 track G did -- FAILS.  Growth is then a dated section in the diff
    rather than a digit in it.

    WHAT IT STILL CANNOT SEE, declared: whether a new section's reason is TRUE.
    No gate can read a sentence.  What it can do is make growth cost a heading
    and a date instead of a character, and make the diff say so."""
    import subprocess
    try:
        out = subprocess.run(["git", "-C", str(path.parent), "show",
                              "HEAD:./" + path.name],
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
    reached, emitted = callgraph.reachable(ir)
    # THE TREE THIS READS MUST BE THE SOURCE'S, BOTH WAYS (W-31, gap 2149).
    # `.lake/build/ir` is where the package builds, so the package is two
    # levels above it, and its LIBRARY is `leanfiles.library_files` -- the
    # enumeration that names the root module as well as the directory.
    pkg = ir.parents[2]
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

    entries, sections, bad = read_exemptions(EXEMPT_FILE)
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
        if key not in entries:
            d = dead[key]
            bad.append("NOT EXEMPT: %s (%s) is emitted and nothing reaches it from "
                       "%s%s" % (d[2], d[0], callgraph.EXPORT_ROOT,
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
    # THE RATCHET, against the file as COMMITTED and not against itself
    # (gap 2259).  A new entry must sit under a section heading that is new too,
    # and a new heading must carry a date.
    prev = committed_exemptions(EXEMPT_FILE)
    if prev is None:
        bad.append("RATCHET UNCHECKED: `git show HEAD:./%s` gave nothing, so the "
                   "only comparand this file has is itself -- which is the state "
                   "D51's ratchet was in before W-31's repair" % EXEMPT_FILE.name)
    else:
        prev_entries, prev_sections, _ = read_exemptions(EXEMPT_FILE, prev)
        prev_heads = {(m, r) for m, r, _ in prev_sections}
        for key in sorted(set(entries) - set(prev_entries)):
            module, reason, lineno = sections[entries[key][1]]
            if (module, reason) in prev_heads:
                bad.append("RATCHET: %s (%s) is a NEW exemption under a section "
                           "that already existed at HEAD -- this file may only "
                           "SHRINK (D51), and growth is a NEW DATED SECTION or it "
                           "is not growth, it is a line in a diff" % (key[1], module))
            elif not SECTION_DATE.search(reason):
                bad.append("RATCHET: %s:%d  the new `## %s` section grandfathers "
                           "%s and its reason carries no ISO date -- growth is "
                           "dated here or it is not made"
                           % (EXEMPT_FILE.name, lineno, module, key[1]))

    if audit:
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
        print("  -- either give it a caller the export reaches, or add it to %s "
              "under a NEW `## <Module.lean> -- <reason carrying an ISO "
              "date>` section AND raise the EXEMPT count in the same edit -- an "
              "entry added under a section that already exists at HEAD fails "
              "the ratchet" % EXEMPT_FILE.name)
    print("%d def/abbrev(s) in %d library module(s), %d emitted (%d as a global), "
          "%d reachable from %s, %d exempt in %d section(s) (%d of them run at "
          "load), %d UNANSWERED"
          % (len(defs), len(library), len(population),
             sum(1 for d in population if d[3] in callgraph.emitted_globals(ir)),
             len(live), callgraph.EXPORT_ROOT, len(entries), len(sections),
             sum(1 for d in dead.values() if d[3] in closed), len(bad)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
