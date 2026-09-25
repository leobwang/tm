#!/usr/bin/env python3
"""CHECK 12'S ROOT, DERIVED FROM THE BINARY INSTEAD OF ASSUMED (README gap 2229).

Check 12 asks *is this definition reachable from `tm_kernel_call`* and it
passes.  `tm_kernel_call` is the `@[export]`, so that question is answerable --
but it is not the question the check was built to ask, and the difference is a
whole subtree.  **The export is not a caller.**  It is a door, and what comes
through it is a REQUEST: a JSON object whose top-level keys select which of the
kernel's sections runs.  A section nothing sends is a door into a room nobody
enters, and every definition behind it is as dead as `assignFold` was -- while
being, on the export's own call graph, perfectly reachable.

THE FINDING THIS FILE IS THE ANSWER TO.  W-31's track P priced R3 and found
that `Planner.dayPlan` -- §8.2's whole planner -- is reached by NO shipped
caller: `grep -rn '"planner"' tm/src` is EMPTY, and the `planner` section is
sent only by `tm/tests/planner_invariants.rs` and
`tm/tests/kernel_planner_wire.rs`, two harnesses no user can run.  Measured
here on 2026-09-25: the `plan` section (W-24's rows) is in the same position,
and `tm/src`'s three `"plan":` occurrences are all a CANDIDATE's nested key
inside `kernel_capacity.rs`'s `plan_json`, never a request's own.  289 of the
1,467 definitions check 12 called reachable are reached only through those two
sections.

WHAT IS MEASURED, ON BOTH SIDES.

  * THE KERNEL'S TOP-LEVEL SECTIONS, by walking the REQUEST from the export.
    `spine` starts at the `@[export]` definition and follows one edge only --
    a callee applied to the request value -- so a reader of a request FIELD
    (`readTz` on the `tz` object, `mkLogReq?` on the `log` object) is never
    mistaken for a reader of the request.  Every `jget`/`getArr` of a literal
    key inside a spine definition is a top-level section, and where the read is
    the scrutinee of a `match .. with` the definition is that section's
    DISPATCHER: the arms tell us what still runs when the key is absent.

  * WHAT `tm/src` SENDS, by reading the JSON the shipped binary builds.
    `sent_sections` scans every `json!(..)` block and every string literal in
    `tm/src` for the keys at brace depth 1, and calls the region a REQUEST when
    those keys are all top-level sections of the kernel and either the region
    carries `docs` or it is a FRAGMENT (a literal that does not open its own
    object -- `kernel_log.rs` builds its request by `push_str`, so `,"tz":` and
    `,"log":` arrive one piece at a time).  That is what separates a request
    from `kernel_capacity.rs`'s candidate object, whose depth-1 keys include
    `"plan"` and eleven names no section has.

THE CUT, AND WHY IT IS AN ARM AND NOT A ROOT.  A walk "rooted at the section
readers" would lose the plumbing every request runs -- `jparse`, `jemit`, the
loader -- and report it dead.  The root stays `tm_kernel_call`; what changes is
that a DISPATCHER for a section nothing sends contributes only the callees of
its ABSENT arms.  For `planner` that is `runPlanner`'s `.error` and `.ok none`
arms, which name `jsonErr` and `EmitWire.runRows`; the `.ok (some sec)` arm,
which names `readPlannerSection`, `planReqOf`, `planJson` and
`Planner.dayPlan`, contributes nothing, because no request the binary can build
takes it.  The kernel PROVES the cut is the right one --
`runPlanner_without_a_planner_section_is_runRows` and
`runRows_without_a_plan_section_is_runCap` are its own laws about exactly this
absence -- and `--audit` prints the arm so the cut is readable rather than
asserted.

WHY THE ARM AND NOT THE THEOREM'S RIGHT-HAND SIDE, which was tried first:
`runRows_without_a_plan_section_is_runCap` is EXTENSIONAL.  It says the two
compute the same value, not that the same code runs -- `runRows` still executes
`runRowsP`, which still executes `runCapP`, and cutting to the theorem's `runCap`
would have called all three dead.  An exemption's reason has to be TRUE, so the
cut is taken where the program branches and not where the proof does.

WHAT THIS CANNOT SEE, declared rather than discovered later:

  * WHETHER A SENT SECTION IS SENT ON A PATH A USER TAKES.  A section named in
    a `#[cfg(test)]` fixture inside `tm/src` counts as sent here (`tz` and `log`
    are named in one, and both are sent by shipped code as well).  This is the
    quiet direction -- it can only make the gate weaker -- and `--audit` prints
    every region it accepted, with its file and line.
  * A REQUEST THIS SCAN CANNOT READ.  A section key assembled from a variable,
    or spliced from a helper that returns a whole object, is invisible; the
    floor is that `docs` must come out SENT, since every request the kernel
    accepts carries documents, and that at least one region must be accepted.
  * A SECTION WITH NO CUTTABLE ARM.  A dispatcher whose `match` has no `.ok
    none` arm (`zoneOf`'s `tz`, which binds and maps instead) cannot be cut
    here.  That is a hard error when the section is UNSENT, never a silent
    pass: a section nothing sends whose arm we cannot find would leave check 12
    rooted where it was.
  * THE ARMS ARE READ FROM THE SOURCE, so a `match` this library writes in a
    shape the arm reader does not know fails loudly (no arms found) instead of
    contributing an empty cut.
"""
import collections
import pathlib
import re

import leanfiles

# The `@[export]`'s own definition: the request's first reader, and the seed of
# the spine.  `callgraph.EXPORT_ROOT` is the C symbol the shim dials; this is
# the Lean declaration that carries the attribute, and the two are not the same
# name (rooting the C walk here is the mistake `callgraph.py`'s header records).
EXPORT_DEF = "callExport"
EXPORT_MODULE = "PlanWire.lean"
# The request value's two spellings in this library: the `String` the export
# takes and the `JVal` every reader below `jparse` is given.  A callee applied
# to one of them is on the spine; a callee applied to anything else is reading a
# FIELD and is not.  The floor below is what makes this a measurement and not a
# guess: `docs` must come out of the walk, because every request carries it.
REQUEST_VARS = ("input", "j")
# The two readers that take a request and a literal key.  A third spelling would
# make a section invisible, so `floors` fails when a key `tm/src` sends is not a
# section this walk found.
READERS = ("jget", "getArr")

DEFHEAD = re.compile(
    r"(?m)^(?:(?:private|protected|noncomputable|nonrec)[ \t]+)*(?:def|abbrev)[ \t]+"
    r"(«[^»]+»|[A-Za-z_][A-Za-z0-9_'!?.]*)")
# The next top-level command, which ends a definition's body.  Comments are
# blanked before this runs, so a docstring between two definitions is
# whitespace and never a false end.
CMD = re.compile(
    r"(?m)^(?:@\[|def |abbrev |theorem |instance |structure |inductive |namespace |end\b"
    r"|section\b|set_option |open |example |private |protected |noncomputable |nonrec "
    r"|partial |unsafe |mutual\b|attribute |deriving |macro |syntax |elab )")
READ = re.compile(r"(?<![\w'?!.])(%s)[ \t\r\n]+([A-Za-z_]\w*)[ \t]+\"( *)\""
                  % "|".join(READERS))
REQ_APPLY = re.compile(r"(?<![\w'?!.])([A-Za-z_][A-Za-z0-9_'!?.]*)[ \t]+(?:%s)\b"
                       % "|".join(REQUEST_VARS))
IDENT = re.compile(r"(?<![\w'?!.«])([A-Za-z_][A-Za-z0-9_'!?.]*)")
# A namespace this library `open`s: a scope every name in that file resolves
# against, beside the enclosing namespaces.
OPENED = re.compile(r"(?m)^[ \t]*open[ \t]+((?:[A-Za-z_][A-Za-z0-9_'.]*[ \t]*)+)")
# An arm whose pattern takes the key's VALUE, so it cannot run when the key is
# absent.  `.ok (some .null)` is the exception and is kept: `readEmitSection`
# reads an explicit `null` as no section at all.
SOME_ARM = re.compile(r"\.ok[ \t\r\n]*\([ \t\r\n]*some\b")
NULL_ALT = re.compile(r"\.ok[ \t\r\n]*\([ \t\r\n]*some[ \t\r\n]+\.null[ \t\r\n]*\)")


class Lib:
    """The library's definitions, comment-stripped, with their bodies.

    The enumeration is `leanfiles.library_files` -- the one that names the
    ROOT MODULE as well as the directory, and the one check 12 already reads
    the population from.  `leanfiles.strip_comments` is LENGTH-PRESERVING and blanks the inside of a
    string literal, so the stripped text is what the structure is read from and
    the raw text at the same offset is what a literal key is read from.  One
    stripper, the one `totality.py` and check 3's roster already share.

    AND IT IS LAZY, BECAUSE A GATE PAYING FOR A QUESTION IT DOES NOT ASK IS A
    COST THAT SHOWS UP AS NOBODY'S LINE ITEM (check 12's own comment, on the
    walk it shares with check 11).  Stripping all 86 library modules to read a
    spine of 22 definitions cost 0.55 s, and asking `leanfiles.qualified_names`
    for the map check 12 has ALREADY BUILT cost 1.16 s more -- 1.7 s on a check
    whose whole wall was 1.6 s.  So the qualified map is HANDED IN by the
    caller, and a module is read and stripped only when a name lookup needs it,
    filtered by a raw substring test: a module whose text does not contain the
    name cannot declare it.  Measured after: 0.05 s."""

    def __init__(self, pkg, defs=None):
        self.files = leanfiles.library_files(pkg)
        self.raw = {p: p.read_text() for p in self.files}
        if defs is None:
            defs = []
            for p in self.files:
                for kw in ("def", "abbrev"):
                    pairs, _ = leanfiles.qualified_names(p, kw)
                    defs.extend((p.name, w, q) for w, q in pairs)
        self.qualified = collections.defaultdict(set)
        self.named = {}
        for d in defs:
            module, written, q = d[0], d[1], d[2]
            self.named.setdefault((module, written), q)
            self.qualified[q].add(q)
            seg = q.split(".")
            for k in range(1, len(seg)):
                self.qualified[".".join(seg[k:])].add(q)
        # `open` is read from the RAW text, not the stripped: a commented-out
        # `open` would add a scope that resolves one more candidate, which is
        # the conservative direction (an extra edge, never a missing one).
        self.opened = set()
        # Which module could declare which name, from the RAW text in one pass:
        # `DEFHEAD` is anchored at a line head, so comment prose almost never
        # matches and a superset costs only a strip that finds nothing.  Without
        # it every name lookup was a substring search over all 86 modules.
        self.heads = collections.defaultdict(list)
        for p, text in self.raw.items():
            for m in OPENED.finditer(text):
                self.opened.update(m.group(1).split())
            for m in DEFHEAD.finditer(text):
                self.heads[m.group(1)].append(p)
        self._index = {}

    def _read(self, p):
        if p in self._index:
            return self._index[p]
        raw = self.raw[p]
        st = leanfiles.strip_comments(raw)
        if len(st) != len(raw):
            raise SystemExit("sections.py: the comment stripper moved %s's "
                             "offsets -- the structure and the literals "
                             "would be read from different places" % p.name)
        out = collections.defaultdict(list)
        heads = list(DEFHEAD.finditer(st))
        for k, m in enumerate(heads):
            stop = heads[k + 1].start() if k + 1 < len(heads) else len(st)
            nxt = CMD.search(st, m.end())
            if nxt and nxt.start() < stop:
                stop = nxt.start()
            out[m.group(1)].append((p.name, st[m.start():stop], raw[m.start():stop]))
        self._index[p] = out
        return out

    def bodies(self, name):
        """`[(module, qualified, stripped, raw)]` for every definition of `name`.

        The qualified name is the one check 12's own population already carries
        for that (module, written) pair, so the two readers cannot disagree
        about what `lean` calls a declaration."""
        out = []
        for p in dict.fromkeys(self.heads.get(name, ())):
            for mod, st, raw in self._read(p).get(name, ()):
                out.append((mod, self.named.get((mod, name), name), st, raw))
        return out

    def resolve(self, written, namespace):
        """Every qualified name `written` could mean inside `namespace`, as a set.

        Lean's own rule, walked outwards: a candidate counts when its prefix is
        `namespace` or one of `namespace`'s enclosing namespaces.  Without it a
        bare `none` in an arm resolves to `Tm.Planner.SegFlags.none` by suffix
        alone and the cut quietly keeps a definition alive that nothing names --
        measured, and it was one of the 288 this file is about.

        The namespaces the LIBRARY `open`s are scopes too -- library-wide and
        not per file, which is the conservative half of this rule -- and they
        are read for the same reason: an `open` this walk did not know about would DROP a live
        callee, and a dropped edge calls dead a definition that is not.  There
        is no wider fallback, because the wider answer is the quiet one -- a
        dropped edge FAILS check 12 by name and a human adjudicates it, while a
        spurious one is a definition nothing calls, called reachable."""
        cands = self.qualified.get(written, set()) | \
            self.qualified.get(written.split(".")[-1], set())
        seg = namespace.split(".")
        scopes = {".".join(seg[:k]) for k in range(len(seg) + 1)} | self.opened
        return {q for q in cands
                if q == written or (q.endswith("." + written) and
                                    q[:len(q) - len(written) - 1] in scopes)}


def arms(stripped, at):
    """The arms of the `match` whose `with` ends at `at`: `[(pattern, body)]`.

    An arm opens with `|` at the column the first one set; anything indented
    deeper belongs to the arm above it, and the first line at a shallower
    column ends the match."""
    lines = stripped[at:].split("\n")
    col, out, cur = None, [], None
    for line in lines[1:] if lines and not lines[0].strip() else lines:
        if not line.strip():
            if cur is not None:
                cur.append(line)
            continue
        ind = len(line) - len(line.lstrip())
        if col is None:
            if not line.lstrip().startswith("|"):
                break
            col = ind
        if ind < col:
            break
        if ind == col and line.lstrip().startswith("|"):
            if cur is not None:
                out.append("\n".join(cur))
            cur = [line]
            continue
        if cur is None:
            break
        cur.append(line)
    if cur is not None:
        out.append("\n".join(cur))
    split = []
    for a in out:
        pat, _, body = a.partition("=>")
        split.append((pat, body))
    return split


def absent_arms(stripped, at):
    """The arms that can still run when the key is absent."""
    return [(p, b) for p, b in arms(stripped, at)
            if not SOME_ARM.search(NULL_ALT.sub("", p))]


def spine(lib):
    """`(sections, dispatchers, walked)` -- the request, followed from the export.

    `sections` is `{key: [(module, qualified, "match"|"read")]}` and
    `dispatchers` is `{key: [(module, qualified, live callees as written names)]}`
    for the reads that scrutinise a `match`."""
    sections = collections.defaultdict(list)
    dispatchers = collections.defaultdict(list)
    seen, stack = set(), [(EXPORT_MODULE, EXPORT_DEF)]
    while stack:
        mod, name = stack.pop()
        if (mod, name) in seen:
            continue
        seen.add((mod, name))
        for fmod, qual, st, raw in lib.bodies(name):
            if fmod != mod:
                continue
            for m in READ.finditer(st):
                key = raw[m.start(3):m.end(3)]
                head = st.rfind("match", 0, m.start())
                tail = re.compile(r"[ \t\r\n]+with\b").match(st, m.end())
                is_match = (tail is not None and head >= 0 and
                            not st[head + 5:m.start()].strip())
                sections[key].append((fmod, qual, "match" if is_match else "read"))
                if is_match:
                    live = set()
                    for pat, body in absent_arms(st, tail.end()):
                        live.update(i.group(1) for i in IDENT.finditer(pat + body))
                    dispatchers[key].append((fmod, qual, live))
            for m in REQ_APPLY.finditer(st):
                callee = m.group(1).split(".")[-1]
                if callee == name:
                    continue
                for cmod, _, _, _ in lib.bodies(callee):
                    stack.append((cmod, callee))
    return sections, dispatchers, seen


KEY = re.compile(r'"([A-Za-z0-9_]+)"[ \t]*:')
RAW_STR = re.compile(r'r(#*)"')


def regions(text):
    """`(body, offset)` for every `json!(..)` block and string literal in `text`.

    A `json!` body is taken paren-balanced and a string literal is unescaped, so
    `\\"docs\\"` inside an ordinary Rust string reads the same as `"docs"` inside
    a raw one."""
    i, n = 0, len(text)
    while i < n:
        if text.startswith("json!(", i):
            depth, k = 0, i + 5
            while k < n:
                if text[k] == "(":
                    depth += 1
                elif text[k] == ")":
                    depth -= 1
                    if depth == 0:
                        break
                k += 1
            yield text[i + 6:k], i
            i = k + 1
            continue
        m = RAW_STR.match(text, i)
        if m:
            close = '"' + m.group(1)
            k = text.find(close, m.end())
            if k < 0:
                return
            yield text[m.end():k], i
            i = k + len(close)
            continue
        if text[i] == '"':
            k, buf = i + 1, []
            while k < n:
                if text[k] == "\\":
                    buf.append(text[k + 1:k + 2])
                    k += 2
                    continue
                if text[k] == '"':
                    break
                buf.append(text[k])
                k += 1
            yield "".join(buf), i
            i = k + 1
            continue
        i += 1


def top_keys(body):
    """`(keys at brace depth 1, whether the region opens its own object)`.

    A region that does not open with `{` is a FRAGMENT of one that did, so its
    own depth starts at 1 -- which is how `kernel_log.rs`'s `,"tz":` and
    `,"log":` are read as the top-level keys they are."""
    opens = body.lstrip().startswith("{")
    depth, out, i = (0 if opens else 1), [], 0
    while i < len(body):
        c = body[i]
        if c in "{[":
            depth += 1
        elif c in "}]":
            depth -= 1
        else:
            m = KEY.match(body, i)
            if m:
                if depth == 1:
                    out.append(m.group(1))
                i = m.end()
                continue
        i += 1
    return out, opens


def sent_sections(src, known):
    """`{key: [(file, line)]}` -- the top-level keys `src` builds requests with.

    A region is a REQUEST when its depth-1 keys are all sections of the kernel
    and it either carries `docs` or is a fragment.  The first test is what keeps
    `kernel_capacity.rs`'s candidate object out (`"plan"` sits there beside
    eleven keys no section has); the second is what keeps a refusal fixture
    (`json!({"capacity":"nowAbsent"})`) from standing in for a request."""
    out = collections.defaultdict(list)
    for p in sorted(leanfiles.rust_files(pathlib.Path(src))):
        text = p.read_text(errors="replace")
        for body, off in regions(text):
            keys, opens = top_keys(body)
            if not keys or not set(keys) <= set(known):
                continue
            if opens and "docs" not in keys:
                continue
            line = text.count("\n", 0, off) + 1
            for k in keys:
                out[k].append((p.name, line))
    return out


def cuts(pkg, src_dir, defs=None):
    """`(cut, report, complaints)` -- check 12's root, measured.

    `cut` is `{Lean name: set of Lean names}`: a dispatcher for a section
    nothing sends, and the callees its absent arms still reach."""
    lib = Lib(pkg, defs)
    sections, dispatchers, walked = spine(lib)
    complaints, report = [], []
    if not any(n == "run" for _, n in walked):
        complaints.append("SPINE: the walk from %s never reached `run` -- the "
                          "request was lost and every section below it is "
                          "invisible" % EXPORT_DEF)
    sent = sent_sections(src_dir, sections)
    if not sent:
        complaints.append("SENT: not one request region in %s -- the root would "
                          "be derived from nothing and every section would be "
                          "cut" % src_dir)
    if "docs" not in sent:
        complaints.append("SENT: `docs` is not sent by %s, and every request the "
                          "kernel accepts carries documents -- the scan is not "
                          "reading the requests" % src_dir)
    cut = {}
    for key in sorted(sections):
        where = sent.get(key)
        if where:
            report.append("  SENT   %-9s %s" % (key, ", ".join(
                "%s:%d" % w for w in sorted(set(where))[:3])))
            continue
        ds = dispatchers.get(key, [])
        if not ds:
            complaints.append("NO ARM: `%s` is a top-level section %s never "
                              "sends and no `match jget .. with` dispatches on "
                              "it, so the walk cannot be cut there and check 12 "
                              "would stay rooted at the export" % (key, src_dir))
            continue
        for mod, qual, live in ds:
            if not live:
                complaints.append("NO ARM: `%s`'s dispatcher %s (%s) has no arm "
                                  "that survives the key's absence -- the match "
                                  "was not read" % (key, qual, mod))
                continue
            names = set()
            ns = qual.rpartition(".")[0]
            for w in live:
                names.update(lib.resolve(w, ns))
            cut.setdefault(qual, set()).update(names)
            report.append("  UNSENT %-9s cut at %s (%s), %d live callee(s)"
                          % (key, qual, mod, len(names)))
    return cut, report, complaints
