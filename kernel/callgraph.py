#!/usr/bin/env python3
"""THE EMITTED CALL GRAPH: one walk, three readers.

Every other instrument in this kernel reads the SOURCE or the THEOREM SET.
Check 9 pins a body against a constant, check 11 pins uniqueness, check 3 pins
the axiom set, check 8 pins a citation -- and a definition can be pinned,
unique, audited and cited and still be called by nothing.  That is README gap
2130 and the owner's D51, and reachability is not a property of any of those
layers: it is a property of the C the code generator EMITS.

WHAT THIS FILE IS.  The emitted tree under `.lake/build/ir` read once, as a
graph: each `LEAN_EXPORT .. name(..){` body taken brace-balanced, the
identifiers in it read as call edges, and a BFS from the one symbol the host
dials.  Three checks read it and NONE of them owns it -- check 11 (`twins.py`)
for E2's second half, check 12 (`reach.py`) for the reachability property
itself, and check 8 (`citations.py`) so that prose naming an emitted symbol
resolves against the tree instead of against an allow-list entry.  Two copies
of this walk would be the §5.3 defect check 11 exists to catch, in the gates
that catch it.

THE ROOT IS `tm_kernel_call` (R9, the `@[export]` at `PlanWire.lean:1198`), and
the rooting is the whole difference between this instrument and a wrong one:
rooting at `Tm.callExport` -- the Lean definition that CARRIES the attribute --
reports almost everything dead, because the emitted function for `Tm.callExport`
is itself reached from nothing.  A missing root is a hard error here, never a
quiet empty answer.

THE MANGLING IS DERIVED FROM THE PINNED TOOLCHAIN, NOT GUESSED.  `symbol` is
`String.mangleAux` and `Lean.Name.mangleAux` of
`Lean/Compiler/NameMangling.lean` in `leanprover/lean4:v4.33.1` (R8 pins it),
transcribed: a letter or digit stands, `_` DOUBLES, and anything else becomes
`_x`/`_u`/`_U` plus its code point in lower hex.  The rule this replaced was
`name.replace(".", "_")` and it was wrong in both directions for a name that
is not pure alphanumerics: `Tm.binsOfPairs?` is emitted as
`lp_TmKernel_Tm_binsOfPairs_x3f` and was looked up under its own spelling with
the `?` still in it, which is no symbol at all -- 70 `def`s of this library
carry a `?`, a `!` or a `'` -- and a `def` whose own name holds an underscore
was looked up under the name of a DIFFERENT declaration one namespace down
(Tm.foo_bar emits Tm_foo__bar, and Tm.foo.bar emits Tm_foo_bar).  W-31 track A,
README gap 2140.

WHAT IT CANNOT SEE, declared rather than discovered later:

  * A definition used only inside a HOISTED CLOSED CONSTANT.  The generator
    lifts a closed subterm into `static .. _init_<owner>___closed__N()` and
    calls it from the module initializer, and neither is a `LEAN_EXPORT ..`
    function, so neither is a node here.  `closed_users` is the measurement of that class,
    and `reach.py` runs it every time rather than asserting it is empty.
  * An indirect call.  A closure's code pointer is passed as a value
    (`lean_alloc_closure((void*)l_foo, ..)`), which reads as an identifier in
    the caller's body and so IS an edge here; a pointer that arrives from
    outside the emitted tree is not.
  * The Rust side.  `tm_kernel_call` is the only symbol the shim dials (R9) and
    a second `@[export]` would need adding here as a second root.
  * A name spelled with a guillemet component that holds a `.` -- this splits a
    dotted name on `.` before mangling it.  The library's guillemet identifiers
    are `«matches»` and `«meta»`, neither of which does.
"""
import pathlib
import re

# THE ROOT OF THE CALL GRAPH: the one symbol the host dials (R9, `@[export
# tm_kernel_call]` at `PlanWire.lean:1198`).
EXPORT_ROOT = "tm_kernel_call"
# The prefix the code generator gives this package's declarations: lp_ plus
# the mangled package name.  `TmKernel` is the package `lakefile.toml` declares
# and it mangles to itself.  A toolchain that changed the scheme would make
# every lookup miss, so `reach.py` carries a floor that fails loudly instead.
PREFIX = "lp_TmKernel_"
# ANY emitted function, by its own C symbol -- the walk's population, which
# includes the export itself (`tm_kernel_call` carries neither of the code
# generator's two name prefixes).
ANY_EMITTED = re.compile(r"(?m)^LEAN_EXPORT[^\n(;]*?\b(\w+)\([^\n]*\{")
# An identifier in an emitted body.  A C body names its callees and nothing
# else that can collide with an exported symbol, so a reference is a call edge.
C_IDENT = re.compile(r"\b[A-Za-z_]\w*\b")
# A hoisted closed constant's own initialiser, which is NOT a `LEAN_EXPORT ..`
# function and so is not a node of the graph: `static lean_object* _init_.. ()`.
INIT_FN = re.compile(r"(?m)^static[^\n(;]*?\b(_init_\w+)\([^\n]*\{")
_FUNCS = {}
_REACH = {}
_CLOSED = {}


def ir_root(path):
    """`.lake/build/ir` above `path`, or a hard error.

    Every reader of this file reads the EMITTED code, so a missing IR tree is
    a failure and never a silent pass: `check.sh` runs all three of them after
    check 1, which is the build that writes it."""
    for parent in pathlib.Path(path).resolve().parents:
        cand = parent / ".lake" / "build" / "ir"
        if cand.is_dir():
            return cand
    raise SystemExit("callgraph.py: no .lake/build/ir above %s -- the emitted "
                     "call graph is read from lake's own output and there is "
                     "none; run `lake build` first" % path)


def check_disambiguation(s, i=0):
    """Lean's `checkDisambiguation`: could `s` be read back as an escape?

    Transcribed from `Lean/Compiler/NameMangling.lean`.  Leading underscores
    are skipped; `x`, `u` and `U` must then be followed by 2, 4 or 8 lower-hex
    digits; a digit answers yes on its own; end of string answers yes."""
    while i < len(s) and s[i] == "_":
        i += 1
    if i >= len(s):
        return True
    c = s[i]
    if c in ("x", "u", "U"):
        want = {"x": 2, "u": 4, "U": 8}[c]
        tail = s[i + 1:i + 1 + want]
        return len(tail) == want and all(d in "0123456789abcdef" for d in tail)
    return c.isdigit() and c.isascii()


def mangle_component(s):
    """Lean's `String.mangleAux` for ONE name component.

    A letter or digit stands (ASCII only -- Lean's `Char.isAlpha` is), `_`
    doubles, and everything else is `_x`/`_u`/`_U` plus its code point in lower
    hex.  The doubling is why a name holding an underscore and a name one
    namespace deeper are different symbols, and why reading one as the other
    was a defect and not a detail."""
    out = []
    for c in s:
        if c.isascii() and (c.isalpha() or c.isdigit()):
            out.append(c)
        elif c == "_":
            out.append("__")
        elif ord(c) < 0x100:
            out.append("_x%02x" % ord(c))
        elif ord(c) < 0x10000:
            out.append("_u%04x" % ord(c))
        else:
            out.append("_U%08x" % ord(c))
    return "".join(out)


def mangle(name):
    """Lean's `Lean.Name.mangleAux` for a dotted name (no prefix).

    The separator is `_`, or `_00` when the joined spelling could be read back
    as something else -- the previous component ended in `_`, or the next one
    begins with an escape.  A component that is all digits is a `Name.num`
    component and is written `<n>_`."""
    out, prev, first = "", None, True
    for seg in name.split("."):
        if seg.isdigit() and seg.isascii():
            out = (seg + "_") if first else (out + "_" + seg + "_")
            prev = None
        else:
            m = mangle_component(seg)
            if first:
                out = ("00" + m) if check_disambiguation(m) else m
            else:
                need = (prev is not None and prev.endswith("_")) or check_disambiguation(m)
                out = out + ("_00" if need else "_") + m
            prev = seg
        first = False
    return out


def symbol(name):
    """The C symbol the code generator gives the Lean declaration `name`."""
    return PREFIX + mangle(name)


def _body(text, at):
    """The brace-balanced body that opens at `text[at - 1]`."""
    i, depth = at - 1, 0
    while i < len(text):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                break
        i += 1
    return text[at:i]


def functions(ir):
    """`{C symbol: [body, ..]}` for every `LEAN_EXPORT ..` function under `ir`.

    The body is taken brace-balanced from the header, so a function's own name
    -- which always differs -- is not part of what a caller compares.

    THE INITIALISERS ARE A SECOND PASS AND NOT THIS ONE, measured: folding
    `closed_users`' scan into this loop reads the 45 MB tree once instead of
    twice and costs 0.65 s -> 0.88-0.94, because the 6,655 initialiser bodies
    have to be brace-balanced too.  Check 12's own wall is the same either way
    (1.63-1.65 s), and check 11 does not ask the initialiser question at all --
    so the one-read version spent a quarter of a second of check 11's budget on
    a measurement check 11 has no use for.  A gate paying for another gate's
    question is the kind of cost that never shows up as anyone's line item."""
    key = str(ir)
    if key in _FUNCS:
        return _FUNCS[key]
    funcs = {}
    for c in sorted(ir.rglob("*.c")):
        text = c.read_text(errors="replace")
        for m in ANY_EMITTED.finditer(text):
            funcs.setdefault(m.group(1), []).append(_body(text, m.end()))
    _FUNCS[key] = funcs
    return funcs


def reachable(ir):
    """`(reached, emitted)`: what the export reaches, and what was emitted.

    The BFS starts at `EXPORT_ROOT` and follows every identifier in a body that
    is itself an emitted function.  It is what tells a definition the callers
    run from a definition nothing calls, and no other instrument in this tree
    can tell them apart."""
    key = str(ir)
    if key in _REACH:
        return _REACH[key]
    funcs = functions(ir)
    if EXPORT_ROOT not in funcs:
        raise SystemExit("callgraph.py: `%s` is not an emitted function under "
                         "%s -- the call graph has no root and every definition "
                         "would look dead" % (EXPORT_ROOT, ir))
    seen, stack = set(), [EXPORT_ROOT]
    while stack:
        n = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        for body in funcs.get(n, ()):
            for r in C_IDENT.finditer(body):
                if r.group(0) in funcs and r.group(0) not in seen:
                    stack.append(r.group(0))
    _REACH[key] = (seen & set(funcs), set(funcs))
    return _REACH[key]


def closed_users(ir):
    """Every symbol called from a HOISTED CLOSED CONSTANT's initialiser.

    This is the walk's own declared blind spot, MEASURED rather than asserted
    empty.  The generator lifts a closed subterm out of a body into `static ..
    _init_<owner>___closed__N()` and calls it from the module initializer;
    neither is a `LEAN_EXPORT ..` function, so a definition whose only use is inside one is
    reported unreachable while it does in fact run at load.  `reach.py` reports
    the intersection of this set with what it is about to fail on."""
    key = str(ir)
    if key in _CLOSED:
        return _CLOSED[key]
    funcs = functions(ir)
    users = set()
    for c in sorted(ir.rglob("*.c")):
        text = c.read_text(errors="replace")
        for m in INIT_FN.finditer(text):
            for r in C_IDENT.finditer(_body(text, m.end())):
                if r.group(0) in funcs:
                    users.add(r.group(0))
    _CLOSED[key] = users
    return users
