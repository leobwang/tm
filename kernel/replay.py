#!/usr/bin/env python3
"""check.sh check 14: the environment the axiom audit reads is one the KERNEL checked.

THE HOLE (W-34 repair, README gap 2730).  Check 3 asks `#print axioms` of every
theorem, and `#print axioms` reads the ENVIRONMENT -- it does not re-check it.
So a declaration that entered the environment without the kernel checking it is
audited as if it had been.  DRIVEN by W-34's verifier in a clone and again by
this repair: a library module holding

    def v34RunTacP : True := by
      run_tac (Lean.withOptions (fun o => o.setBool `debug.skipKernelTC true)
        (Lean.addDecl (Lean.Declaration.thmDecl
          { name := `Tm.v34Bad, type := Lean.mkConst ``False,
            value := Lean.mkConst ``True.intro, .. })))
      trivial
    theorem v34_one_is_two : (1 : Nat) = 2 := (Tm.v34Bad).elim

built (`lake build` ok), and `#print axioms Tm.v34_one_is_two` printed "does not
depend on any axioms".  A proof of `1 = 2` passed all thirteen checks.

totality.py's rules are a LIST of spellings (`set_option debug.skipKernelTC`,
`run_cmd`, `#eval` ..) and the plant used none of them: run_tac is a TACTIC,
and the option was set by withOptions inside it.  The syntactic half of the
repair closes the ROUTE -- a kernel file may import only the kernel's own
modules, so `Lean.addDecl` is not in scope (totality.py's import rule; the same
plant without `import Lean` fails at `Unknown constant Lean.Elab.Tactic.TacticM`).
THIS file is the PROPERTY, and it does not care about spelling:

    every declaration of every module Lake compiles into the library is
    re-checked by the kernel, replayed from the built `.olean` into the
    environment its imports give, by the pinned toolchain's own `leanchecker`
    (`src/lean/LeanChecker.lean`: "a tool to detect environment hacking").

The replay adds each constant through `Environment.replay`, which runs the
kernel's `addDecl` with no options -- `debug.skipKernelTC` is not an argument
it takes.  DRIVEN on the plant above: `leanchecker TmKernel.V34` rc=1,
"(kernel) declaration type mismatch, 'Tm.v34Bad' has type True but it is
expected to have type False".

WHAT IT CANNOT SEE, declared.  `Environment.replay` re-adds an AXIOM without
complaint (an axiom has nothing to check), so an axiom added by metaprogramming
replays clean; that route is closed by the import rule and the `axiom` keyword
ban, not here.  And it checks what the kernel checks: a definition the kernel
accepts that is not the one the source spells is not its business.

COST, AND WHY THERE IS A CACHE.  Measured at `fb05f4e`, one module at a time
under a 16G cap: 6 min 3 s wall, 3.1 GB peak, 181 s of it `PlannerWit` and
125 s `Boundary`.  So modules run in parallel (`JOBS`), and a module whose
replay PASSED is remembered under a key that is a Merkle hash: its own `.olean`
parts, the toolchain pin, and the keys of every module it imports.  Replay is a
function of exactly those, so a remembered pass is the same pass; a changed
module, or any change beneath it, changes the key and is replayed again.  A
FAILURE is never remembered.  The cache lives in `.lake/`, which is derived.

A library file with no `.olean` is a FAILURE here, by name: a module nobody
imports is not built (AGENTS §2.3), and a check over built modules that skipped
it would be the disguised gap that section names.
"""
import concurrent.futures as cf
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys

import leanfiles

HERE = pathlib.Path(__file__).resolve().parent
PKG = HERE / "TmKernel"
OLEAN_DIR = PKG / ".lake" / "build" / "lib" / "lean"
CACHE = PKG / ".lake" / "replay-cache.json"
LAKE = pathlib.Path.home() / ".elan" / "bin" / "lake"
JOBS = 6
IMPORT = re.compile(r"(?m)^(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?(\S+)")


def module_of(path):
    rel = path.relative_to(PKG).with_suffix("")
    return ".".join(rel.parts)


def olean_parts(mod):
    base = OLEAN_DIR.joinpath(*mod.split(".")).with_suffix(".olean")
    parts = [base]
    for ext in (".olean.server", ".olean.private"):
        p = base.with_name(base.name.replace(".olean", ext))
        if p.exists():
            parts.append(p)
    return parts


def main():
    files = leanfiles.library_files(PKG)
    mods = {module_of(p): p for p in files}
    imports = {}
    for m, p in mods.items():
        code = leanfiles.strip_comments(p.read_text(encoding="utf-8"))
        imports[m] = [i for i in IMPORT.findall(code) if i in mods]
    # THE ROOT MODULE IS IMPORTS AND NOTHING ELSE (AGENTS §2.2), and here that
    # is a check and not a description: `leanchecker TmKernel` would match every
    # module by prefix and replay them all at once (18 GB, measured), so the
    # root is not replayed -- which is sound only while it declares nothing.
    root = PKG.name
    rest = IMPORT.sub("", leanfiles.strip_comments(mods[root].read_text(encoding="utf-8")))
    if rest.strip():
        print("replay: %s.lean holds more than import lines, and the root module "
              "is not replayed (AGENTS §2.2)" % root)
        return 1
    del mods[root], imports[root]
    missing = [m for m in mods if not olean_parts(m)[0].exists()]
    if missing:
        for m in sorted(missing):
            print("replay: %s has no .olean -- not built, so not checked "
                  "(import it, AGENTS §2.3)" % m)
        return 1
    pin = (PKG / "lean-toolchain").read_text().strip()
    keys = {}

    def key(m, seen=()):
        if m in keys:
            return keys[m]
        if m in seen:
            raise SystemExit("replay: import cycle at %s" % m)
        h = hashlib.sha256(pin.encode())
        for part in olean_parts(m):
            h.update(part.name.encode())
            h.update(part.read_bytes())
        for i in sorted(imports[m]):
            h.update(key(i, seen + (m,)).encode())
        keys[m] = h.hexdigest()
        return keys[m]

    for m in mods:
        key(m)
    try:
        cache = json.loads(CACHE.read_text())
    except (OSError, ValueError):
        cache = {}
    todo = sorted(m for m in mods if cache.get(m) != keys[m])

    def run(m):
        r = subprocess.run([str(LAKE), "env", "leanchecker", m], cwd=PKG,
                           capture_output=True, text=True)
        return m, r.returncode, (r.stdout + r.stderr).strip()

    bad = []
    with cf.ThreadPoolExecutor(max_workers=JOBS) as ex:
        for m, rc, out in ex.map(run, todo):
            if rc == 0:
                cache[m] = keys[m]
            else:
                cache.pop(m, None)
                bad.append((m, out))
    for m in list(cache):
        if m not in mods:
            del cache[m]
    try:
        CACHE.write_text(json.dumps(cache, indent=1, sort_keys=True))
    except OSError:
        pass
    for m, out in bad:
        print("replay: the kernel refuses %s:" % m)
        for line in out.splitlines()[:6]:
            print("    " + line)
    if bad:
        return 1
    print("%d modules replayed by the kernel (%d this run, %d remembered)"
          % (len(mods), len(todo), len(mods) - len(todo)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
