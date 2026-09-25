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
file was written: of the 2,365 emitted `def`s, 260 are referenced by at least
one `theorem` and by no `def` at all.  Exempting those 260 by that property
would have been the wrong rule TWICE OVER.  It swallows `Tm.edf` and
`Tm.edfGrants` -- §7's EDF grant machine, whose fast twins the W-30 repair
deleted as dead (gap 2126) and whose originals nothing has called since -- and
it cannot see `Tm.remainingMin`, which nine of `Tree.lean`'s ten definitions
reference from inside their own module, exactly as `assignFold` did.  A rule
that depends on who mentions a name is a rule the blind spot is defined by.  So
the antecedent is the compiler's, the exemptions are NAMED, and the reason each
one carries is readable and dated instead of inferred.

THE EXEMPTION FILE IS W-27'S SHAPE: AN ENUMERATION YOU JOIN TO BE EXEMPT, NOT
TO BE COVERED.  `reach-exempt.txt` grandfathers the 952 definitions that were
unreachable on 2026-09-25, each under a section naming its module and its
reason, and it may only SHRINK: an entry that becomes reachable, stops being
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
  * A definition the compiler emits nothing for -- 677 of the library's 3,042
    `def`s, every one of them a `Prop`, a type-level abbreviation or a
    declaration in the package root, which `lake` does not compile into the
    library at all.  `--audit` prints that population so the number is
    re-measured rather than believed.
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
import sys

import callgraph
import leanfiles

EXEMPT_FILE = pathlib.Path(__file__).resolve().parent / "reach-exempt.txt"


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
        pairs, leftover = leanfiles.qualified_names(p, "def")
        if leftover:
            raise SystemExit("reach.py: %s leaves %s open at end of file -- the "
                             "qualified name of every declaration below it is "
                             "wrong" % (p, leftover))
        for written, qualified in pairs:
            out.append((pathlib.Path(p).name, written, qualified,
                        callgraph.symbol(qualified)))
    return out, files


def read_exemptions(path):
    """`(entries, sections, complaints)` from the exemption file.

    `entries` is `{(module, name): note}`, `sections` is `{module: reason}`.
    A `##` line opens a section and carries the reason every entry under it
    inherits; a `#` line is prose; anything else is an entry, with an optional
    `#` note of its own.  A `EXEMPT <n>` line declares the size, which must
    match exactly -- the count is in the diff so that GROWTH is a deliberate
    edit and not a side effect."""
    entries, sections, complaints = {}, {}, []
    module, declared = None, None
    for lineno, raw in enumerate(path.read_text().splitlines(), 1):
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
                module = None
            else:
                sections[module] = reason
            continue
        if line.startswith("#"):
            continue
        if line.startswith("EXEMPT "):
            declared = line.split()[1]
            continue
        name, _, note = line.partition("#")
        name, note = name.strip(), note.strip()
        if module is None:
            complaints.append("%s:%d  `%s` sits under no section, so it carries no "
                              "reason" % (path.name, lineno, name))
            continue
        if (module, name) in entries:
            complaints.append("%s:%d  `%s` is listed twice under %s"
                              % (path.name, lineno, name, module))
            continue
        entries[(module, name)] = note
    if declared is None or not declared.isdigit():
        complaints.append("%s  has no `EXEMPT <n>` line, so its size is not declared"
                          % path.name)
    elif int(declared) != len(entries):
        complaints.append("%s  declares EXEMPT %s and holds %d entries -- the count "
                          "is the ratchet, so correct it in the same edit"
                          % (path.name, declared, len(entries)))
    return entries, sections, complaints


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
        raise SystemExit("reach.py: not one of %d `def`s matches an emitted C symbol "
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
            bad.append("STALE: %s (%s) is not an emitted `def` of that module any "
                       "more -- delete this entry" % (key[1], key[0]))
    for module in sorted({m for m, _ in entries}):
        if module not in sections:
            bad.append("SECTION: %s has entries under no `##` heading" % module)

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
    print("%d def(s) in %d library module(s), %d emitted, %d reachable from %s, "
          "%d exempt in %d section(s) (%d of them run at load), %d UNANSWERED"
          % (len(defs), len(library), len(population), len(live),
             callgraph.EXPORT_ROOT, len(entries), len(sections),
             sum(1 for d in dead.values() if d[3] in closed), len(bad)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
