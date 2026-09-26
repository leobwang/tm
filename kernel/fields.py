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
shrink), on a field the wire does not emit, on a key that projects no field,
and on an exemption line without a date or an EXIT.  `--audit` prints every
field with its writers.
"""
import collections
import pathlib
import re
import subprocess
import sys

import callgraph
import leanfiles

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


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
