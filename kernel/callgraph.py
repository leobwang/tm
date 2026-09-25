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
    a second `@[export]` would need adding here as a second root.  WHICH
    REQUESTS THE RUST DIALS IT WITH is a different question and this walk
    cannot ask it either: the export is a door, and a section nothing sends is
    a room nobody enters.  `sections.py` measures that, `reachable`'s `cuts`
    argument is where its answer enters, and README gap 2229 is the finding --
    289 definitions were reachable from this root and from no request the
    shipped binary can build.
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
# AND A DEFINITION THE GENERATOR EMITS AS A GLOBAL AND NOT AS A FUNCTION
# (W-31 repair, README gap 2257).  `ANY_EMITTED` recognises a definition only
# where the code generator gave it a C FUNCTION.  A `def` with no parameters
# whose body is a closed constant -- every witness fixture, every codec
# `abbrev`, every table -- is emitted as `LEAN_EXPORT lean_object* <sym>;` plus
# `static .. _init_<sym>___closed__N()` initialisers assigned by the module
# initializer, and NEVER as a function.  MEASURED on the committed tree: 1,244
# such globals, 524 of them a library `def` or `abbrev`, 470 of those named by
# no function the export reaches -- exactly the shape check 12 exists for, and
# all of it outside check 12's population.  `reach.py`'s own header asserted the
# non-emitting remainder was "every one of them a `Prop`, a type-level
# abbreviation or a declaration in the package root"; it was false by 524.
#
# A GLOBAL IS A LEAF OF THE WALK, not a node with a body: it is REACHED when a
# body the export reaches names it, and it calls nothing itself.  The two
# populations do not overlap (measured: 0 symbols in both).
#
# **AND THE GENERATOR WRITES A GLOBAL TWO WAYS** -- which this pattern read as
# one until a plant caught it, in the repair that was written to close exactly
# this shape.  `LEAN_EXPORT lean_object* <sym>;` is the global the MODULE
# INITIALIZER assigns, and `LEAN_EXPORT const lean_object* <sym> = (const
# lean_object*)&<sym>___closed__N_value;` is the one the C file initialises
# statically; both are the same definition and neither is a function.  DRIVEN in
# a `git clone --local` with its own build tree: `def w31CriticOrphanConst :
# List Nat := [3,1,4,1,5,9,2,6]` planted in `SealInStep.lean`, reached by
# nothing, emitted at `SealInStep.c:94` as the SECOND spelling -- and a pattern
# anchored on `;` left the emitted count unmoved at 2,880 and this check green,
# while the `abbrev` planted beside it was named.  So the test is what does NOT
# follow the symbol: an emitted definition whose name is followed by `(` is a
# function and everything else is data.
ANY_GLOBAL = re.compile(r"(?m)^LEAN_EXPORT\s[^\n(;=]*?\b(\w+)\s*(?:;|=)")
# An identifier in an emitted body.  A C body names its callees and nothing
# else that can collide with an exported symbol, so a reference is a call edge.
C_IDENT = re.compile(r"\b[A-Za-z_]\w*\b")
# A hoisted closed constant's own initialiser, which is NOT a `LEAN_EXPORT ..`
# function and so is not a node of the graph: `static lean_object* _init_.. ()`.
INIT_FN = re.compile(r"(?m)^static[^\n(;]*?\b(_init_\w+)\([^\n]*\{")
_FUNCS = {}
_GLOBALS = {}
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
    twice and costs 0.65 s -> 0.88-0.94, because the 6,679 initialiser bodies
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


def emitted_globals(ir):
    """Every `LEAN_EXPORT <type> <sym>;` global under `ir`, by its C symbol.

    The second half of the emitted population (W-31 repair, gap 2257).  It is a
    separate scan and not a second group in `ANY_EMITTED` because the two
    shapes are told apart by what follows the symbol -- `(` for a function, `;`
    for a global -- and folding them into one pattern makes the distinction the
    walk needs (a body, or none) depend on a regex alternation instead of on
    which dictionary the symbol came out of."""
    key = str(ir)
    if key in _GLOBALS:
        return _GLOBALS[key]
    globs = set()
    for c in sorted(ir.rglob("*.c")):
        globs.update(ANY_GLOBAL.findall(c.read_text(errors="replace")))
    _GLOBALS[key] = globs
    return globs


def reachable(ir, cuts=None):
    """`(reached, emitted)`: what the export reaches, and what was emitted.

    The BFS starts at `EXPORT_ROOT` and follows every identifier in a body that
    is itself an emitted function OR an emitted global.  It is what tells a
    definition the callers run from a definition nothing calls, and no other
    instrument in this tree can tell them apart.

    A GLOBAL HAS NO BODY, so it is a leaf: reaching one adds nothing to the
    stack.  Its module initializer assigns it and no initializer is reachable
    from the export, so a global is reached exactly when a function the export
    reaches READS it -- which is the question the emitted-function walk asks of
    a function, asked of data.

    `cuts` is `{symbol: set of symbols}` and is how the export stops being an
    ASSUMED root (`sections.py`, README gap 2229).  The export is a door, not a
    caller: what comes through it is a request, and a dispatcher for a section
    `tm/src` never sends runs only its absent arms.  A symbol named in `cuts`
    contributes exactly the callees given instead of everything its body
    mentions.  `None` -- the default, and what checks 8 and 11 pass -- is the
    walk as it was, so their answers do not move."""
    key = (str(ir), None if cuts is None else
           tuple(sorted((k, tuple(sorted(v))) for k, v in cuts.items())))
    if key in _REACH:
        return _REACH[key]
    funcs = functions(ir)
    globs = emitted_globals(ir)
    if EXPORT_ROOT not in funcs:
        raise SystemExit("callgraph.py: `%s` is not an emitted function under "
                         "%s -- the call graph has no root and every definition "
                         "would look dead" % (EXPORT_ROOT, ir))
    node = set(funcs) | globs
    seen, stack = set(), [EXPORT_ROOT]
    while stack:
        n = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        if cuts and n in cuts:
            for m in cuts[n]:
                if m in node and m not in seen:
                    stack.append(m)
            continue
        for body in funcs.get(n, ()):
            for r in C_IDENT.finditer(body):
                if r.group(0) in node and r.group(0) not in seen:
                    stack.append(r.group(0))
    _REACH[key] = (seen & node, node)
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
