#!/usr/bin/env python3
"""check.sh's check 13 (W-33 track A, README gap 2403): a field the wire EMITS
must have a WRITER the day builder REACHES.

THE FINDING.  W-32 drove the shipped binary and read `--json plan`'s
diagnostics: twelve keys with values in them.  The kernel's `Planner.Diagnostics`
carries all twelve fields, with the fork's meanings and in the fork's order,
and `PlanWire.diagJson` emits every one of them under its own key -- and
`Planner.dayDiagnostics` writes THREE (`conflicts`, `aCapacityLost`, `notes`)
and leaves nine at whatever `Diagnostics.empty` put there (ten written and two
left since the W-33 land step merged track P's seven writers).  Found by hand,
while doing something else, the fourth composition gap of this campaign: a
type that matches the fork's shape pins nothing about the fork's values, and no
gate could tell a field that is empty because the day was clean from a field
that is empty because nobody writes it.  Gap 2419 is the same fact from the
proof side: `PlanCheck.impossibleKept` ranges over `Diagnostics.impossible`
and is PROVABLY empty at every request, because nothing writes that field.

THE PROPERTY.  For every key the planner wire emits under `diagnostics`, the
field it projects is ASSIGNED BY NAME -- `field := ..` in a structure instance
or a structure update -- inside a definition that `Planner.dayPlan` reaches in
the emitted call graph (`callgraph.py`'s walk, rooted at the day builder
instead of at the door); or the field is named in `fields-exempt.txt` under a
dated reason that names its EXIT.  Both directions of the wire are checked
beside it (AGENTS 5.8): every field of the structure is emitted under some
key, and every key projects a field the structure has.  The emitter is found
by the KEY, not by name: the definition applied to the day's `.diagnostics`
under `"diagnostics"` on the planner wire, whatever it is called.

WHY THE EMITTED GRAPH AND NOT THE SOURCE.  A writer has to be REACHED from
the day, not merely present: `Diagnostics.withNote` writes `notes` and nothing
in the day calls it, and a fixture in `PlannerWit.lean` that wrote `hot` would
be a witness, not the planner.  Reachability from `Tm.Planner.dayPlan` in the
C the code generator emitted is the one instrument in this tree that answers
"does the day run this", and check 12 already reads it.

WHAT IT CANNOT SEE, declared:
  * a POSITIONAL constructor, `⟨a, b, ..⟩`, names no field.  `Diagnostics.empty`
    is one and is exactly the write this check must NOT count, so the blind spot
    is the right way round -- but a real writer spelled positionally would be
    reported unwritten, and the remedy is to spell the field.
  * a write that COPIES another record's field (`{ d with hot := d'.hot }`) is
    a write here, whatever it copies.
  * a writer the code generator INLINED into its caller has no symbol of its
    own and is not reached; `dayDiagnostics` is a function in the emitted C
    today (`Planner.c`), measured, and a writer that stops being one would be
    reported unwritten, the loud direction.
  * a field written with a value that is ALWAYS the empty one.  Written is a
    floor under populated, never a proof of it; the proof is a witness request
    at which the field is not `Diagnostics.empty`'s, which is `PlannerWit.lean`'s
    to hold and check 9's to demand.
  * one wire key, one structure.  The question generalises to every record the
    wire emits; it is asked of the one whose nine empty fields were found.

USAGE: `fields.py [--audit]`.  Exits 1 on an unwritten field no exemption
names, on an exempt field that is written now (STALE -- the file may only
shrink), on an exemption the file did not hold at HEAD for a field the
structure already had there (RATCHET, W-33 repair, gap 2564), on a field the
wire does not emit, on a key that projects no field, and on an exemption line
without a date or an EXIT.  `--audit` prints every
field with its writers.
"""
import collections
import pathlib
import re
import subprocess
import sys

import callgraph
import leanfiles
from reach import committed_exemptions

HERE = pathlib.Path(__file__).resolve().parent
LIB = HERE / "TmKernel"
EXEMPT_FILE = HERE / "fields-exempt.txt"
# The wire key whose object this checks, and the one total day builder (D28)
# the walk is rooted at.
WIRE_KEY = "diagnostics"
ROOT_DEF = "Tm.Planner.dayPlan"
DEF = re.compile(r"(?<![\w'?!.«])def[ \t\r\n]+([^\s(){}:]+)")
ISO_DATE = re.compile(r"\b20\d\d-[01]\d-[0-3]\d\b")
EXIT = re.compile(r"\bEXIT\b")


def chunks(code):
    """`[(name, start, end)]` of every `def` in comment-stripped `code`."""
    out = []
    for m in DEF.finditer(code):
        stop = leanfiles.NEXT_COMMAND.search(code, m.end())
        out.append((m.group(1), m.end(), stop.start() if stop else len(code)))
    return out


def split_top(text):
    """The comma-separated parts of `text` at bracket depth zero."""
    parts, depth, cur = [], 0, []
    for c in text:
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        if c == "," and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(c)
    if "".join(cur).strip():
        parts.append("".join(cur))
    return parts


def emitter(texts, codes):
    """`(path, name, raw chunk, stripped chunk, param, tname)`: the definition
    applied to the day's `.diagnostics` under the wire key, found by the KEY.

    The key is read off the RAW text: `leanfiles.strip_comments` blanks a
    string's content and keeps its quotes, offset-preserving, so the stripped
    code locates a declaration and the raw text at the same offsets spells
    the literal (the discipline `twins.literals` uses)."""
    pat = re.compile(r'\("%s"\.toList,\s*([A-Za-z_][\w.\'?!]*)\s+[A-Za-z_]\w*\.%s\)'
                     % (WIRE_KEY, WIRE_KEY))
    for path, text in texts.items():
        m = pat.search(text)
        if not m:
            continue
        code = codes[path]
        name = m.group(1).split(".")[-1]
        for n, a, b in chunks(code):
            if n.split(".")[-1] == name:
                sig = code[a:b].split(":=", 1)[0]
                p = re.search(r"\(\s*([A-Za-z_]\w*)\s*:\s*([A-Za-z_][\w.]*)\s*\)", sig)
                if not p:
                    raise SystemExit("fields.py: the emitter `%s` takes no `(d : T)` this "
                                     "reads" % name)
                return path, name, text[a:b], code[a:b], p.group(1), p.group(2)
        raise SystemExit("fields.py: `%s` is applied under \"%s\" in %s and declared "
                         "nowhere in it" % (name, WIRE_KEY, path))
    raise SystemExit("fields.py: no definition is applied to a `.%s` under the key "
                     "\"%s\" in the library -- the wire does not emit the object this "
                     "check is about, or spells it another way" % (WIRE_KEY, WIRE_KEY))


def emitted_keys(raw, chunk, param):
    """`{key: {fields projected}}` for the top-level pairs of the emitter's
    `.obj [..]` -- structure from the stripped chunk, key text from the raw."""
    at = chunk.find(":=")
    a = chunk.find("[", at)
    depth, b = 0, a
    for i in range(a, len(chunk)):
        if chunk[i] == "[":
            depth += 1
        elif chunk[i] == "]":
            depth -= 1
            if depth == 0:
                b = i
                break
    keys, i = {}, a + 1
    for part in split_top(chunk[a + 1:b]):
        j = i + len(part)
        q = re.search(r'"([^"]*)"', chunk[i:j])
        if q:
            key = raw[i + q.start() + 1:i + q.end() - 1]
            keys[key] = set(re.findall(r"\b%s\.([A-Za-z_]\w*)" % re.escape(param), part))
        i = j + 1
    return keys


def structure_fields(codes, tname):
    """The fields `structure <tname>` declares, in order, from the library."""
    pat = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+)*"
                     r"structure[ \t]+(?:[A-Za-z_][\w.]*\.)?%s\b" % re.escape(tname))
    for path, code in codes.items():
        m = pat.search(code)
        if not m:
            continue
        stop = leanfiles.NEXT_COMMAND.search(code, m.end())
        block = code[m.end():stop.start() if stop else len(code)]
        return path, [f for f in leanfiles.STRUCT_FIELD.findall(block)]
    raise SystemExit("fields.py: no `structure %s` in the library" % tname)


def result_type(sig):
    """The declared result type of a signature: what follows its last depth-zero `:`."""
    depth, at = 0, -1
    for i, c in enumerate(sig):
        if c in "([{\u27e8\u2983":
            depth += 1
        elif c in ")]}\u27e9\u2984":
            depth -= 1
        elif c == ":" and depth == 0:
            at = i
    return sig[at + 1:].strip() if at >= 0 else ""


def param_types(sig):
    """`{parameter: declared type}` from the binder groups of a signature."""
    out, depth, i, n = {}, 0, 0, len(sig)
    while i < n:
        c = sig[i]
        if depth == 0 and c in "({[\u2983":
            d, j = 0, i
            while j < n:
                if sig[j] in "([{\u27e8\u2983":
                    d += 1
                elif sig[j] in ")]}\u27e9\u2984":
                    d -= 1
                    if d == 0:
                        break
                j += 1
            group = sig[i + 1:j]
            if ":" in group:
                names, _, ty = group.partition(":")
                for nm in names.split():
                    out[nm] = ty.strip()
            i = j + 1
            continue
        if depth == 0 and c == ":":
            break
        i += 1
    return out


def braces(text):
    """Every `{ .. }` region of `text`, outermost first, as `(start, end)`."""
    out, stack = [], []
    for i, c in enumerate(text):
        if c == "{":
            stack.append(i)
        elif c == "}" and stack:
            out.append((stack.pop(), i))
    return sorted(out)


def writers(codes, fields, tname):
    """`{field: [(path, def name)]}`: every `def` that assigns the field by name
    ON A SUBJECT OF THE STRUCTURE'S TYPE.

    A field name is shared across structures -- `SegFlags` has `underused`,
    `hot` and `deferred` and `Placed` has `deferred` too -- and this test
    counted `assignedSeg` and `placeStep` as writers of the DIAGNOSTICS'
    fields until the structure was asked for (W-33, the gate's first run).
    The subject's type is what the SOURCE declares: the base of a `{ e with
    .. }` is a parameter whose declared type is the structure, or an
    expression whose head is qualified by the structure's name
    (`Diagnostics.empty`); a plain instance `{ f := .. }` is of the structure
    when the definition's result type is.  A subject typed only by inference
    (a `let`, a nested field) is not seen, and a writer spelled that way is
    reported unwritten -- the loud direction."""
    out = collections.defaultdict(list)
    pats = {f: re.compile(r"(?<![\w.])%s[ \t]*:=" % re.escape(f)) for f in fields}
    short = tname.split(".")[-1]
    for path, code in codes.items():
        for n, a, b in chunks(code):
            chunk = code[a:b]
            if ":=" not in chunk:
                continue
            sig, body = chunk.split(":=", 1)
            res = result_type(sig).split(".")[-1] == short
            ptypes = {k: v.split(".")[-1] for k, v in param_types(sig).items()}
            for i, j in braces(body):
                region = body[i + 1:j]
                head, sep, _rest = region.partition(" with ")
                if sep:
                    base = head.strip()
                    subject = ptypes.get(base) == short or \
                        ("%s." % short) in base.split("(")[0] or base.startswith(short + ".")
                else:
                    subject = res
                if not subject:
                    continue
                for f, pat in pats.items():
                    if pat.search(region) and (path, n) not in out[f]:
                        out[f].append((path, n))
    return out


def read_exemptions(path, text=None):
    """`({field: (reason, lineno)}, complaints)`; a line is `<Type.field> -- <reason>`."""
    entries, bad = {}, []
    if text is None:
        if not path.exists():
            return entries, bad
        text = path.read_text()
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        name, sep, reason = line.partition(" -- ")
        if not sep or "." not in name:
            bad.append("%s:%d  an entry is `<Type.field> -- <reason>` and this is `%s`"
                       % (path.name, lineno, line[:60]))
            continue
        field = name.split(".")[-1]
        if field in entries:
            bad.append("%s:%d  `%s` is listed twice" % (path.name, lineno, name))
            continue
        if not ISO_DATE.search(reason):
            bad.append("%s:%d  `%s` carries no ISO date" % (path.name, lineno, name))
        if not EXIT.search(reason):
            bad.append("%s:%d  `%s` names no EXIT -- say which step writes it and what "
                       "happens to this line when it does" % (path.name, lineno, name))
        entries[field] = (reason, lineno)
    return entries, bad


def main(argv):
    audit = "--audit" in argv
    files = sorted(leanfiles.lean_files(LIB))
    texts = {p: pathlib.Path(p).read_text() for p in files}
    codes = {p: leanfiles.strip_comments(texts[p]) for p in files}
    epath, ename, raw, chunk, param, tname = emitter(texts, codes)
    keys = emitted_keys(raw, chunk, param)
    spath, fields = structure_fields(codes, tname.split(".")[-1])
    bad = []
    projected = set().union(*keys.values()) if keys else set()
    for f in fields:
        if f not in projected:
            bad.append("NOT EMITTED: %s.%s is a field of the structure and no key of `%s` "
                       "projects it" % (tname, f, ename))
    for k, fs in keys.items():
        for f in fs - set(fields):
            bad.append("NO SUCH FIELD: `%s` emits \"%s\" from `%s.%s`, which `structure %s` "
                       "does not declare" % (ename, k, param, f, tname))
    ir = callgraph.ir_root(files[0])
    reached = callgraph.reachable(ir, root=callgraph.symbol(ROOT_DEF))[0]
    tables = {}
    written = collections.defaultdict(list)
    for f, lst in writers(codes, fields, tname).items():
        for path, name in lst:
            if path not in tables:
                pairs, _ = leanfiles.qualified_names(path, "def", code=codes[path])
                tables[path] = {}
                for w, q in pairs:
                    tables[path].setdefault(w, q)
            q = tables[path].get(name, name)
            if callgraph.symbol(q) in reached:
                written[f].append(q)
    entries, ebad = read_exemptions(EXEMPT_FILE)
    bad.extend(ebad)
    for f in fields:
        if f in written and f in entries:
            bad.append("STALE: %s:%d  %s.%s is WRITTEN now, by %s -- delete this line, the "
                       "file may only shrink" % (EXEMPT_FILE.name, entries[f][1], tname, f,
                                                 ", ".join(sorted(written[f]))))
        elif f not in written and f not in entries:
            bad.append("UNWRITTEN: %s.%s is emitted under \"%s\" and no definition `%s` "
                       "reaches assigns it by name -- the wire carries a field the day "
                       "never fills.  Write it, or name it in %s under a dated reason "
                       "with an EXIT"
                       % (tname, f, next((k for k, fs in keys.items() if f in fs), "?"),
                          ROOT_DEF, EXEMPT_FILE.name))
    for f in set(entries) - set(fields):
        bad.append("STALE: %s:%d  `%s` is not a field of %s -- delete this line"
                   % (EXEMPT_FILE.name, entries[f][1], f, tname))
    # THE RATCHET, against the file as COMMITTED (W-33 repair, README gap 2564).
    # This file's header said it "may only SHRINK" and only the STALE direction
    # was checked: driven by W-33's auditor in a clone, deleting `blocked :=`
    # from `dayDiagnostics` and appending a dated `Planner.Diagnostics.blocked`
    # line with an EXIT gave rc=0 -- gap 2403's own regression, a field back to
    # unwritten, with the gate green.  The comparand is `reach.py`'s,
    # `committed_exemptions` (one reader of HEAD, not two): a line for a field
    # HEAD's file did not list FAILS, unless the field is not a field of the
    # structure AT HEAD either -- a field the wire has never carried may arrive
    # unwritten with a dated EXIT, and a field that was written may never go
    # back.
    prev = committed_exemptions(EXEMPT_FILE)
    if prev is None:
        bad.append("RATCHET UNCHECKED: `git show HEAD:./%s` gave nothing, so this file's "
                   "only comparand is itself" % EXEMPT_FILE.name)
    else:
        prev_entries, _ = read_exemptions(EXEMPT_FILE, prev)
        new = sorted(set(entries) - set(prev_entries))
        if new:
            head_src = committed_exemptions(pathlib.Path(spath))
            head_fields = set()
            if head_src is not None:
                try:
                    _p, head_fields = structure_fields(
                        {spath: leanfiles.strip_comments(head_src)}, tname.split(".")[-1])
                except SystemExit:
                    head_fields = set()  # the structure is new at this commit
            for f in new:
                if head_src is None or f in head_fields:
                    bad.append("RATCHET: %s:%d  %s.%s is a NEW exemption and the field "
                               "existed at HEAD -- this file may only SHRINK, and a field "
                               "that was written does not go back to unwritten (gap 2403's "
                               "own regression)" % (EXEMPT_FILE.name, entries[f][1], tname, f))
    if audit:
        for f in fields:
            print("  %-16s %-14s %s" % (f, next((k for k, fs in keys.items() if f in fs), "-"),
                                        ", ".join(sorted(written.get(f, []))) or
                                        ("exempt: " + entries[f][0][:60] if f in entries
                                         else "UNWRITTEN")))
    for line in bad:
        print(line)
    print("%d field(s) of %s, %d emitted under %d key(s) by %s (%s), %d written by a "
          "definition %s reaches, %d exempt, %d UNANSWERED"
          % (len(fields), tname, len(projected & set(fields)), len(keys), ename,
             pathlib.Path(epath).name, sum(1 for f in fields if f in written),
             ROOT_DEF, len(entries), len(bad)))
    return 1 if bad else 0


# ===========================================================================
# THE INPUT HALF (W-34 repair, README gap 2734): a field the planner request
# DECODES must have a READER the day builder REACHES.
#
# THE FINDING.  W-34's reuse critic measured five decoded request fields no
# definition of the day reads: `RuntimeIn.brk`, `.lastHash`, `.yesterday` and
# `PlanOverrides.estMin`, `.extraMin`.  Check 13 was output-side only and check
# 12 counts a decoder as reached, so no gate could see an INPUT with no reader
# -- and `PlanWire.lean` said the kernel compares `state.lastHash`, which
# nothing in the kernel does.  It is the output half's finding one wire over:
# a type that matches the fork's shape pins nothing about what is read.
#
# THE PROPERTY.  Start at `PlanReq`, the record the planner section decodes.
# Every field of it must be PROJECTED -- `x.field` on a subject whose declared
# type is the structure -- inside a definition `Planner.dayPlan` reaches in the
# emitted call graph, or be named in `inputs-exempt.txt` under a dated reason
# with an EXIT.  A field that IS read and whose type is another structure the
# planner module declares is followed, and ITS fields are asked the same; a
# field that is not read is reported once, not with every field beneath it.
# The class is "the records the planner request decodes into", read off the
# declarations, never a list of names.
#
# HOW A SUBJECT IS TYPED, and what that cannot see (declared).  A parameter by
# its binder; `let x := <chain>`; `fun x =>` right after `<chain>.map (` and
# its kin; `| some x` under `match <chain> with`; and a qualified `S.field`.
# A subject typed only by deeper inference is not seen and its reads are
# missed -- the LOUD direction (a read field reported unread).  A reader the
# code generator inlined has no symbol and is not reached -- loud as well.  A
# read whose value is then IGNORED is a read here: read is a floor under used.
# ===========================================================================
IN_ROOT_TYPE = "PlanReq"
IN_EXEMPT_FILE = HERE / "inputs-exempt.txt"
LAMBDA_HOSTS = ("map", "filter", "filterMap", "any", "all", "bind", "find?", "forM",
                "mapM", "foldl", "foldr", "attach", "getD", "elim", "isSome", "all?")
CHAIN = r"[A-Za-z_][\w'?!]*(?:\.[A-Za-z_][\w'?!]*)+"


def typed_fields(codes, tname):
    """`(path, [(field, type text)])` of `structure <tname>`, from the library."""
    pat = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+)*"
                     r"structure[ \t]+(?:[A-Za-z_][\w.]*\.)?%s\b" % re.escape(tname))
    for path, code in codes.items():
        m = pat.search(code)
        if not m:
            continue
        stop = leanfiles.NEXT_COMMAND.search(code, m.end())
        block = code[m.end():stop.start() if stop else len(code)]
        out = re.findall(r"(?m)^[ \t]+([A-Za-z_][A-Za-z0-9_'!?]*)[ \t]*:[ \t]*([^=\n][^\n]*)$",
                         block)
        return path, [(f, t.strip()) for f, t in out]
    return None, []


def core_type(ty, known):
    """The structure a declared type is about: the first identifier in it whose
    last segment is a structure in `known` (so `Option ActiveBlock`, `Capped
    RoutineIn` and `Planner.PlanOverrides` all say what they hold)."""
    for ident in re.findall(r"[A-Za-z_][\w.]*", ty):
        if ident.split(".")[-1] in known:
            return ident.split(".")[-1]
    return None


def reads_in(body, env, fields_of):
    """`{(struct, field)}` projected in `body`, subjects typed by `env` and by
    the bindings the body itself makes."""
    env = dict(env)
    known = set(fields_of)

    def resolve(chain):
        segs = chain.split(".")
        t = env.get(segs[0])
        got = []
        for seg in segs[1:]:
            if t is None:
                break
            fs = dict(fields_of.get(t, []))
            if seg in fs:
                got.append((t, seg))
                t = core_type(fs[seg], known)
            else:
                break
        return t, got

    for _ in range(2):  # bindings can feed bindings; two passes reach a fixpoint here
        for m in re.finditer(r"\blet[ \t]+([A-Za-z_][\w']*)[ \t]*(?::[^=]*)?:=[ \t]*(%s)" % CHAIN, body):
            t, _g = resolve(m.group(2))
            if t:
                env[m.group(1)] = t
        for m in re.finditer(r"(%s)\.(?:%s)[ \t]*\(?[ \t]*fun[ \t]+\(?([A-Za-z_][\w']*)"
                             % (CHAIN, "|".join(re.escape(h) for h in LAMBDA_HOSTS)), body):
            t, _g = resolve(m.group(1))
            if t:
                env[m.group(2)] = t
        for m in re.finditer(r"\bmatch[ \t]+(?:h[\w']*[ \t]*:[ \t]*)?(%s)[ \t]+with" % CHAIN, body):
            t, _g = resolve(m.group(1))
            if not t:
                continue
            nxt = re.search(r"\bmatch\b", body[m.end():])
            scope = body[m.end():m.end() + (nxt.start() if nxt else len(body))]
            for x in re.findall(r"\|[ \t]*\.?some[ \t]+([A-Za-z_][\w']*)", scope):
                env[x] = t
    reads = set()
    for m in re.finditer(r"(?<![\w'.])(%s)" % CHAIN, body):
        _t, got = resolve(m.group(1))
        reads.update(got)
        head, _, rest = m.group(1).partition(".")
        if head in fields_of and rest.split(".")[0] in dict(fields_of[head]):
            reads.add((head, rest.split(".")[0]))
    return reads


def inputs_main(audit, files, codes):
    root_path, _ = typed_fields(codes, IN_ROOT_TYPE)
    if root_path is None:
        raise SystemExit("fields.py: no `structure %s` in the library -- the input half "
                         "would gate nothing" % IN_ROOT_TYPE)
    # The planner module's structures: the ones declared where `PlanReq` is.
    local = re.findall(r"(?m)^structure[ \t]+([A-Za-z_][\w']*)", codes[root_path])
    fields_of = {t: typed_fields({root_path: codes[root_path]}, t)[1] for t in local}
    ir = callgraph.ir_root(files[0])
    reached = callgraph.reachable(ir, root=callgraph.symbol(ROOT_DEF))[0]
    reads = set()
    for path in files:
        pairs, _ = leanfiles.qualified_names(path, "def", code=codes[path])
        table = {}
        for w, q in pairs:
            table.setdefault(w, q)
        for n, a, b in chunks(codes[path]):
            q = table.get(n, n)
            if callgraph.symbol(q) not in reached:
                continue
            chunk = codes[path][a:b]
            if ":=" not in chunk:
                continue
            sig, body = chunk.split(":=", 1)
            env = {}
            for k, v in param_types(sig).items():
                t = core_type(v, set(fields_of))
                if t:
                    env[k] = t
            # a `PlanReq.x (r : PlanReq)` view is also reached under generalised
            # field notation; its binder typing covers it like any parameter.
            reads |= reads_in(body, env, fields_of)
    todo, seen, unread = [IN_ROOT_TYPE], set(), []
    while todo:
        t = todo.pop(0)
        if t in seen:
            continue
        seen.add(t)
        for f, ty in fields_of.get(t, []):
            if (t, f) in reads:
                c = core_type(ty, set(fields_of))
                if c and c not in seen:
                    todo.append(c)
            else:
                unread.append((t, f))
    entries, bad = {}, []
    text = IN_EXEMPT_FILE.read_text() if IN_EXEMPT_FILE.exists() else ""
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        name, sep, reason = line.partition(" -- ")
        key = tuple(name.split(".")[-2:])
        if not sep or len(key) != 2:
            bad.append("%s:%d  an entry is `<Type>.<field> -- <reason>`" % (IN_EXEMPT_FILE.name, lineno))
            continue
        if not ISO_DATE.search(reason) or not EXIT.search(reason):
            bad.append("%s:%d  `%s` needs an ISO date and an EXIT" % (IN_EXEMPT_FILE.name, lineno, name))
        entries[key] = lineno
    for t, f in unread:
        if (t, f) not in entries:
            bad.append("UNREAD: %s.%s is decoded from the planner request and no definition "
                       "%s reaches projects it -- read it, or name it in %s under a dated "
                       "reason with an EXIT" % (t, f, ROOT_DEF, IN_EXEMPT_FILE.name))
    for key, lineno in sorted(entries.items(), key=lambda kv: kv[1]):
        if key not in unread:
            bad.append("STALE: %s:%d  %s.%s is %s -- delete this line, the file may only "
                       "shrink" % (IN_EXEMPT_FILE.name, lineno, key[0], key[1],
                                   "READ now" if key in reads else "not a field this walk asks"))
    prev = committed_exemptions(IN_EXEMPT_FILE)
    if prev is not None:
        prev_keys = {tuple(ln.strip().partition(" -- ")[0].split(".")[-2:])
                     for ln in prev.splitlines() if ln.strip() and not ln.strip().startswith("#")}
        for key in sorted(set(entries) - prev_keys):
            bad.append("RATCHET: %s:%d  %s.%s is a NEW exemption -- this file may only SHRINK"
                       % (IN_EXEMPT_FILE.name, entries[key], key[0], key[1]))
    if audit:
        for t in sorted(seen):
            for f, _ty in fields_of.get(t, []):
                print("  in  %-14s %-12s %s" % (t, f, "read" if (t, f) in reads else
                                                "exempt" if (t, f) in entries else "UNREAD"))
    for line in bad:
        print(line)
    asked = sum(len(fields_of.get(t, [])) for t in seen)
    print("inputs: %d field(s) of %d record(s) the planner request decodes, %d read by a "
          "definition %s reaches, %d exempt, %d UNANSWERED"
          % (asked, len(seen), asked - len(unread), ROOT_DEF, len(entries), len(bad)))
    return 1 if bad else 0


# ===========================================================================
# THE SENT HALF (W-36 track H, README gap 2931): a key the HOST'S ENCODER
# writes into the planner section must have a READER in the kernel.
#
# THE FINDING.  W-35 track R built D58's host half: `planwire::overtime_json`
# writes `grown{remaining, plannedMin, needMin}` beside `id` and `blocks`, and
# `PlanWire.readOvertime` reads `id` and `blocks` -- so the route was "built"
# and read by nothing, and no gate could say so.  The input half above counts
# the fields of DECODED records; a key no reader decodes never becomes one.
# And an optional key an encoder MISSPELLS reads as absent with no refusal, so
# a typo in the host is a feature quietly switched off.
#
# THE PROPERTY, AS W-36 STATED IT FOR ONE SECTION (since W-40 the host side is
# `sentkeys.host_sections`, below).  Every JSON key path the host codec's `<section>_json`
# writes (`sentkeys.host_paths`: its `json!` literals, inserts, index assignments and
# arrays, its helpers composed by call, a caller's value placed by the module's
# `<key>_json`) must be DECODED by the kernel's reader of that section
# (`sentkeys.kernel_paths`: the section's value followed from the definition
# that `jget`s its key off the request, through every binding and call), or be
# named in `sent-exempt.txt` under a dated reason with an EXIT.  An unread key
# is reported ONCE, at its shallowest path, not with every key beneath it.  A
# line for a key that is decoded now -- or that the encoder no longer writes --
# FAILS as STALE, and a line the committed file did not hold FAILS as RATCHET:
# the file may only shrink, W-27's shape.
#
# WHAT IT CANNOT SEE is `sentkeys.py`'s header.  Until W-40 it asked ONE section,
# the planner's, of ONE encoder, `tm-core/src/planwire.rs` (README gap 3081, and gap
# 3717: `day.rs`' `call_the_walls` wrote `emit.walls.week` with no gate asking whether
# a kernel reader decoded it).
#
# SINCE W-40 TRACK E (README gap 3717) IT ASKS EVERY SECTION, AT EVERY PLACE A REQUEST
# GAINS ONE.  The sections are the kernel's own -- `sections.spine`, the walk from the
# export that check 12 roots itself on -- and the host side of each is
# `sentkeys.host_sections`: every `json!` object any function of the program (`tm/src`
# and every crate it links by path) builds that carries `docs`, wherever it is written,
# and every request built as TEXT (`kernel_log`'s `log` section and request, the
# `format!` that splices it into the capacity and walls requests) is a request, and
# each of its top-level keys a section whose value is read through the helpers it
# calls, in whatever module (`Foreign`); the codec's `<section>_json` that no codec
# function composes is a section's root (the only host side `planner` has until R3),
# and its `&mut Value` writers join it.  The sites are held to check 12's own scan of
# `tm/src` (`sections.sent_sections`): a request that scan reads and no site holds
# FAILS, UNREAD REQUEST.
# Both sides are compared NORMALIZED (`sentkeys.normalized`): prefix-closed, an array
# of scalars read as its key.  A key path is reported once, at its shallowest, and an
# exemption line names a path or a whole section and answers everything under it.
# ===========================================================================
# The section R3 swaps in: its host side is the codec's alone until then, so a
# reader that lost it would compare nothing where it matters most (a floor, not a scope).
SENT_SECTION = "planner"
SENT_EXEMPT_FILE = HERE / "sent-exempt.txt"

# ===========================================================================
# THE WRITTEN HALF (W-36 repair, README gap 3132): a key the kernel DECODES
# must have a WRITER in the host's codec -- the converse of the sent half.
#
# THE FINDING.  The sent half asks sent => decoded and the input half decoded
# => read, and check 12 reaches per SECTION; nothing asked decoded => written.
# The W-36 reuse critic measured three decoded keys no host encoder writes --
# `planner.overrides`, `state.lastHash`, `state.yesterday` -- and one of them
# is READ by the day: `overrides.drop` drives the active run's `d done`
# what-if (Planner.lean), written only by tests (kernel_planner_wire.rs), while the TUI's
# one override is `PlanOverrides::extending`.  After R3 the section is sent,
# that code counts as reached, and no host key ever drives it.
#
# THE PROPERTY, AS THE W-36 REPAIR STATED IT (since W-40 the writers are every place a
# request is built, `sentkeys.host_sections`).  Every key path `sentkeys.kernel_paths`
# decodes under the section is WRITTEN by the codec (`sentkeys.host_paths`, which since this
# repair also follows every codec function taking the section as `&mut
# Value`), or is named in `written-exempt.txt` under a dated reason with an
# EXIT -- reported once at its shallowest path, STALE when it is written now or
# no longer decoded, RATCHET when the committed file did not hold it: W-27's
# shape, the file may only SHRINK.
#
# WHAT IT CANNOT SEE: whether the binary CALLS the writer.  `add_worked_min`
# writes `state.active.workedMin` and has no caller in `tm/src` (README gap
# 3043, R3's): "written by the codec" is a floor under "sent by the binary",
# the same sentence as the input half's read-is-a-floor-under-used.
# ===========================================================================
WRITTEN_EXEMPT_FILE = HERE / "written-exempt.txt"


HEADING = re.compile(r"^##[ \t]+(.*)$")


def ratchet_file(path, shallow, under, why_stale, bad, sections):
    """The exemption entries of `path` against the shallow key paths they may
    exempt.  An entry is `<section>[.key.path] -- <reason with an ISO date and an
    EXIT>`, for any section in `sections`, and answers every shallow path equal to or
    under it.  A malformed, undated or repeated line, a line no shallow path is at or
    under (STALE; `why_stale(p)` says why), and a line the committed file did not hold
    are each a complaint in `bad` -- WHATEVER heading it sits under (README gap 3953,
    the W-40 repair).  W-40 track E gave this ratchet reach.py's escape -- a new line
    was let through under a `## <heading>` new in the diff and carrying an ISO date --
    and both files it governs grew under it (sent 0 -> 1, written 3 -> 5); driven by
    the W-40 verifier, an unread key planted with a dated heading passed at rc=0.  The
    owner's D51 says these files only SHRINK, and `inputs-exempt.txt` and
    `fields-exempt.txt`, this script's other two, never had the escape: growth is the
    owner's to grant, in the commit that changes this script, and never a heading.  A
    heading stays a way to group lines.  Returns `{entry: lineno}`."""
    entries, heading_of, headings = {}, {}, {}
    text = path.read_text() if path.exists() else ""
    current = None
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        hd = HEADING.match(line)
        if hd:
            current = hd.group(1).strip()
            headings[current] = lineno
            if not ISO_DATE.search(current):
                bad.append("%s:%d  the heading `%s` carries no ISO date" % (path.name, lineno, current))
            continue
        if not line or line.startswith("#"):
            continue
        name, sep, reason = line.partition(" -- ")
        sec = re.split(r"[.\[]", name, 1)[0]
        if not sep or sec not in sections:
            bad.append("%s:%d  an entry is `<section>[.key.path] -- <reason>`, the section one the "
                       "kernel reads off a request" % (path.name, lineno))
            continue
        if not ISO_DATE.search(reason) or not EXIT.search(reason):
            bad.append("%s:%d  `%s` needs an ISO date and an EXIT" % (path.name, lineno, name))
        if name in entries:
            bad.append("%s:%d  `%s` is listed twice" % (path.name, lineno, name))
        entries[name] = lineno
        heading_of[name] = current
    for e, lineno in sorted(entries.items(), key=lambda kv: kv[1]):
        if not any(p == e or under(p, e) for p in shallow):
            bad.append("STALE: %s:%d  `%s` is %s -- delete this line, the file may only shrink"
                       % (path.name, lineno, e, why_stale(e)))
    prev = committed_exemptions(path)
    if prev is None:
        bad.append("RATCHET UNCHECKED: `git show HEAD:./%s` gave nothing, so the only comparand "
                   "this file has is itself" % path.name)
    else:
        held = set()
        for ln in prev.splitlines():
            ln = ln.strip()
            if ln and not ln.startswith("#") and not HEADING.match(ln):
                held.add(ln.partition(" -- ")[0])
        for e in sorted(set(entries) - held):
            if any(under(e, q) for q in held):
                continue
            bad.append("RATCHET: %s:%d  `%s` is a NEW exemption, under no key exempt at HEAD -- "
                       "this file may only SHRINK (D51), whatever heading it sits under "
                       "(README gap 3953)" % (path.name, entries[e], e))
    return entries


def answered(p, entries, under):
    """Is the shallow path `p` answered by an exemption entry (itself or an ancestor)?"""
    return any(p == e or under(p, e) for e in entries)


def under(p, q):
    """Is key path `p` strictly under `q`?"""
    return p != q and (p.startswith(q + ".") or p.startswith(q + "[]"))


def section_paths(files, codes):
    """`(sections, host, kernel, where, complaints)`: the kernel's top-level sections
    (`sections.spine`), and for each the normalized key paths the program writes and
    the kernel's reader decodes."""
    import sentkeys
    import sections as reqsec
    # Check 12's own qualified map, read off the text this process already stripped:
    # `Lib` builds it from the raw files otherwise, 1.6 s of this check's wall (W-40).
    defs = []
    for p in files:
        for kw in ("def", "abbrev"):
            pairs, _ = leanfiles.qualified_names(p, kw, code=codes[p] if codes else None)
            defs.extend((pathlib.Path(p).name, w, q) for w, q in pairs)
    lib = reqsec.Lib(LIB, defs=defs)
    secs, _, _ = reqsec.spine(lib)
    names = sorted(secs)
    host_raw, where, complaints = sentkeys.host_sections(HERE.parent, names)
    reader = sentkeys.LeanReader(files, codes)
    host, kernel = {}, {}
    for sec in names:
        host[sec] = sentkeys.normalized(host_raw.get(sec, ()), sec)
        kernel[sec] = sentkeys.normalized(sentkeys.kernel_paths(files, sec, codes, reader), sec)
    return names, host, kernel, where, complaints


def written_main(names, host, kernel):
    """The written half: every decoded key path has a writer where a request is built."""
    bad = []
    unwritten = sorted(p for sec in names for p in kernel[sec] if p not in host[sec])
    shallow = [p for p in unwritten if not any(under(p, q) for q in unwritten)]
    allk = set().union(*kernel.values()) if kernel else set()
    allh = set().union(*host.values()) if host else set()
    entries = ratchet_file(
        WRITTEN_EXEMPT_FILE, shallow, under,
        lambda p: ("WRITTEN now" if p in allh else "not a key the kernel decodes"
                   if p not in allk and p not in names else "under a key unwritten itself"),
        bad, names)
    for p in shallow:
        if not answered(p, entries, under):
            bad.append("UNWRITTEN: `%s` is decoded by the kernel's reader of `%s` and written at no "
                       "place a request is built (`sentkeys.host_sections`) -- write it, stop "
                       "decoding it, or name it in %s under a dated reason with an EXIT"
                       % (p, re.split(r"[.\[]", p, 1)[0], WRITTEN_EXEMPT_FILE.name))
    for line in bad:
        print(line)
    print("written: %d key path(s) the kernel decodes over %d section(s), %d written where a "
          "request is built, %d unwritten (%d shallow, %d answered by %d exemption(s)), %d UNANSWERED"
          % (len(allk), len(names), len(allk) - len(unwritten), len(unwritten), len(shallow),
             sum(1 for p in shallow if answered(p, entries, under)), len(entries), len(bad)))
    return 1 if bad else 0


def sent_main(audit, files, codes=None):
    names, host, kernel, where, complaints = section_paths(files, codes)
    bad = list(complaints)
    if not host.get(SENT_SECTION):
        bad.append("NO HOST KEYS: nothing the program builds writes `%s` -- the half would "
                   "compare nothing for the section R3 swaps in" % SENT_SECTION)
    if not kernel.get(SENT_SECTION):
        bad.append("NO KERNEL READS: no definition reads `%s` off the request, or the walk from "
                   "it was lost -- every key would read as unread" % SENT_SECTION)
    unread = sorted(p for sec in names for p in host[sec] if p not in kernel[sec])
    shallow = [p for p in unread if not any(under(p, q) for q in unread)]
    allk = set().union(*kernel.values()) if kernel else set()
    allh = set().union(*host.values()) if host else set()
    entries = ratchet_file(
        SENT_EXEMPT_FILE, shallow, under,
        lambda p: ("DECODED now" if p in allk else "not a key any request writes"
                   if p not in allh and p not in names else "under a key unread itself"),
        bad, names)
    for p in shallow:
        if not answered(p, entries, under):
            bad.append("UNREAD: `%s` is written into a request (%s) and decoded by no kernel reader "
                       "of `%s` -- read it, stop sending it, or name it in %s under a dated reason "
                       "with an EXIT"
                       % (p, ", ".join(where.get(re.split(r"[.\[]", p, 1)[0], ["?"])[:3]),
                          re.split(r"[.\[]", p, 1)[0], SENT_EXEMPT_FILE.name))
    if audit:
        for sec in names:
            print("  section %-9s host %3d kernel %3d  written at %s"
                  % (sec, len(host[sec]), len(kernel[sec]), ", ".join(where.get(sec, ["nowhere"]))))
            for p in sorted(host[sec]):
                print("    sent %-52s %s" % (p, "read" if p in kernel[sec] else
                                             "exempt" if answered(p, entries, under) else "UNREAD"))
    for line in bad:
        print(line)
    print("sent: %d key path(s) written into a request over %d section(s) (%s), %d decoded by the "
          "kernel, %d unread (%d shallow, %d answered by %d exemption(s)), %d UNANSWERED"
          % (len(allh), len(names), ", ".join("%s %d" % (sec, len(host[sec])) for sec in names
                                               if host[sec]),
             len(allh) - len(unread), len(unread), len(shallow),
             sum(1 for p in shallow if answered(p, entries, under)), len(entries), len(bad)))
    written_rc = written_main(names, host, kernel)
    return 1 if bad or written_rc else 0


if __name__ == "__main__":
    out_rc = main(sys.argv[1:])
    files_ = sorted(leanfiles.lean_files(LIB))
    codes_ = {p_: leanfiles.strip_comments(pathlib.Path(p_).read_text()) for p_ in files_}
    in_rc = inputs_main("--audit" in sys.argv[1:], files_, codes_)
    sent_rc = sent_main("--audit" in sys.argv[1:], files_, codes_)
    sys.exit(1 if out_rc or in_rc or sent_rc else 0)
