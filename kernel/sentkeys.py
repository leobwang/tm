#!/usr/bin/env python3
"""The two readings check 13's SENT half compares (W-36 track H, README gap 2931).

`fields.py`'s input half asks whether every field the planner request DECODES
is read.  It could not see the step before that: a key the HOST's encoder
writes that no kernel reader decodes at all.  `tm_core::planwire::overtime_json`
writes `grown{remaining, plannedMin, needMin}` and `PlanWire.readOvertime`
reads `id` and `blocks` -- D58's route "built" and read by nothing -- and an
optional key an encoder misspells reads as absent with no refusal.  The input
half counts fields of decoded RECORDS, so it cannot see a key that never
became one.  This module produces the two sets of KEY PATHS that answer it:

  * `host_paths` -- every JSON key path the host's encoder writes into a
    request section, read off the RUST SOURCE of the codec
    (`tm-core/src/planwire.rs`): `json!` object literals, `.insert("k"..)`,
    `o["k"] = ..`, arrays built by `Value::Array(.. .map(|..| json!(..)) ..)`,
    and the encoder's own helpers composed by call.  A value handed IN by the
    caller (`planner_json`'s `overtime`) is the output of the module function
    named `<key>_json` -- the codec's own naming, `state_json`,
    `routines_json`, `overtime_json` -- and a caller's value under a key with
    no such function is UNPLACEABLE, a failure and never a pass.
  * `kernel_paths` -- every key path the kernel's reader DECODES under that
    section, read off the LEAN SOURCE by following the section's value from
    its dispatcher (the definition that `jget`s the section's key off the
    request, found by the key, not by name) through every definition it is
    handed to: a key read is a literal key given to one of the JSON getters
    on a value whose path is known, and a sub-value's path follows it into the
    arm or `let` that binds it and into every definition that binding is
    passed to (by position, a list's elements through `.mapM`/`.zipIdx.mapM`).

WHAT IT CANNOT SEE, declared:
  * a key assembled from a variable, or an object built by a helper outside
    the codec module, on the host side; the ROOT of the section is the module
    function `<section>_json`, so an encoder that writes the section some other
    way is not read at all (the loud direction: nothing to compare is a
    failure in `fields.py`, never a pass).
  * on the kernel side, a value that reaches a reader through a structure
    field (`parts.sec`) rather than a bound name: its reads are not
    attributed, and a host key under it reports UNREAD -- loud.  A binding the
    arm reader cannot parse likewise loses its reads -- loud.  The QUIET
    direction would be a read attributed to the wrong object; bindings are
    scoped to the arm or the rest of the definition that makes them, so a name
    bound twice for two keys does not merge.
  * a key the kernel reads and then IGNORES counts as read: read is a floor
    under used, the same sentence as the input half's.
"""
import collections
import pathlib
import re

import leanfiles

# ---------------------------------------------------------------------------
# Rust: a tokenizer, just enough of one
# ---------------------------------------------------------------------------

Tok = collections.namedtuple("Tok", "kind val at")
RUST_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
RUST_NUM = re.compile(r"[0-9][0-9A-Za-z_.]*")
RUST_RAW = re.compile(r"r(#*)\"")
RUST_CHAR = re.compile(r"'(?:\\.[^']*|[^'\\])'")


def rust_tokens(text):
    """`[Tok]`: identifiers, strings (unescaped), numbers, chars and single
    punctuation characters, with comments dropped.  `::`, `=>`, `->` are two
    tokens each, which every pattern below spells out."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
            continue
        if text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("/*", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/*", i):
                    depth += 1
                    i += 2
                elif text.startswith("*/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        m = RUST_RAW.match(text, i)
        if m:
            close = '"' + m.group(1)
            k = text.find(close, m.end())
            k = n if k < 0 else k
            out.append(Tok("str", text[m.end():k], i))
            i = k + len(close)
            continue
        if c == "b" and text.startswith('b"', i):
            i += 1
            c = '"'
        if c == '"':
            k, buf = i + 1, []
            while k < n and text[k] != '"':
                if text[k] == "\\":
                    buf.append(text[k + 1:k + 2])
                    k += 2
                    continue
                buf.append(text[k])
                k += 1
            out.append(Tok("str", "".join(buf), i))
            i = k + 1
            continue
        if c == "'":
            m = RUST_CHAR.match(text, i)
            if m:
                out.append(Tok("char", m.group(0), i))
                i = m.end()
                continue
            m = RUST_IDENT.match(text, i + 1)  # a lifetime or a loop label
            if m:
                out.append(Tok("lifetime", m.group(0), i))
                i = m.end()
                continue
        m = RUST_IDENT.match(text, i)
        if m:
            out.append(Tok("ident", m.group(0), i))
            i = m.end()
            continue
        m = RUST_NUM.match(text, i)
        if m:
            out.append(Tok("num", m.group(0), i))
            i = m.end()
            continue
        out.append(Tok("punct", c, i))
        i += 1
    return out


OPEN = {"(": ")", "[": "]", "{": "}"}


def close_of(toks, i):
    """The index of the token closing the bracket at `toks[i]`."""
    want, depth = OPEN[toks[i].val], 0
    for k in range(i, len(toks)):
        v = toks[k].val if toks[k].kind == "punct" else None
        if v in OPEN:
            depth += 1
        elif v in (")", "]", "}"):
            depth -= 1
            if depth == 0:
                return k
    raise ValueError("an unclosed %r at offset %d" % (toks[i].val, toks[i].at))


def split_top(toks, sep=","):
    """`toks` split at depth-0 `sep` punctuation."""
    parts, cur, depth = [], [], 0
    for t in toks:
        if t.kind == "punct" and t.val in OPEN:
            depth += 1
        elif t.kind == "punct" and t.val in (")", "]", "}"):
            depth -= 1
        if depth == 0 and t.kind == "punct" and t.val == sep:
            parts.append(cur)
            cur = []
        else:
            cur.append(t)
    if cur:
        parts.append(cur)
    return parts


def test_spans(toks):
    """Token ranges of every `#[cfg(test)]` item: the codec's own tests build
    `json!` fixtures that are not the encoder."""
    spans = []
    for i in range(len(toks) - 6):
        if [t.val for t in toks[i:i + 7]] == ["#", "[", "cfg", "(", "test", ")", "]"]:
            k = i + 7
            while k < len(toks) and not (toks[k].kind == "punct" and toks[k].val == "{"):
                k += 1
            if k < len(toks):
                spans.append((i, close_of(toks, k)))
    return spans


def rust_fns(toks):
    """`{name: (param names, body tokens)}` for every `fn` outside a test item."""
    tests = test_spans(toks)
    out = {}
    i = 0
    while i < len(toks) - 1:
        if toks[i].kind == "ident" and toks[i].val == "fn" and toks[i + 1].kind == "ident" \
                and not any(a <= i <= b for a, b in tests):
            name = toks[i + 1].val
            k = i + 2
            while k < len(toks) and not (toks[k].kind == "punct" and toks[k].val == "("):
                k += 1
            pclose = close_of(toks, k)
            params = []
            for part in split_top(toks[k + 1:pclose]):
                if len(part) >= 2 and part[0].kind == "ident" and part[1].val == ":":
                    params.append(part[0].val)
                elif len(part) >= 3 and part[0].val == "mut" and part[2].val == ":":
                    params.append(part[1].val)
            b = pclose + 1
            while b < len(toks) and not (toks[b].kind == "punct" and toks[b].val in "{;"):
                b += 1
            if b < len(toks) and toks[b].val == "{":
                bclose = close_of(toks, b)
                out[name] = (params, toks[b + 1:bclose])
                i = bclose + 1
                continue
        i += 1
    return out


class Link:
    """A value that is another encoder function's output."""
    def __init__(self, fn):
        self.fn = fn

    def __repr__(self):
        return "Link(%s)" % self.fn


class Param:
    """A value the caller handed in through parameter `name`."""
    def __init__(self, name):
        self.name = name


ARRAY = "[]"


class RustEncoder:
    """The encoder functions of one Rust module and what each one writes."""

    def __init__(self, text):
        self.fns = rust_fns(rust_tokens(text))
        self.complaints = []
        self._out = {}

    def is_call(self, toks, i):
        return (toks[i].kind == "ident" and toks[i].val in self.fns and i + 1 < len(toks)
                and toks[i + 1].val == "(" and (i == 0 or toks[i - 1].val != "."))

    def value(self, toks, env, fn):
        """The tree a Rust expression writes: a dict of keys, `None` for a
        scalar, a `Link` or a `Param`."""
        toks = [t for t in toks]
        if not toks:
            return None
        if len(toks) == 1 and toks[0].kind == "ident" and toks[0].val in env:
            return env[toks[0].val]
        # `Value::Array(<iterator of json!>)` is an array of what it maps to.
        if [t.val for t in toks[:4]] == ["Value", ":", ":", "Array"] and toks[4].val == "(":
            inner = self.value(toks[5:close_of(toks, 4)], env, fn)
            return {ARRAY: inner}
        if [t.val for t in toks[:4]] == ["Value", ":", ":", "Object"] and toks[4].val == "(":
            return self.value(toks[5:close_of(toks, 4)], env, fn)
        for i in range(len(toks) - 2):
            if toks[i].val == "json" and toks[i + 1].val == "!" and toks[i + 2].val == "(":
                return self.json_value(toks[i + 3:close_of(toks, i + 2)], env, fn)
        for i in range(len(toks)):
            if self.is_call(toks, i):
                out = self.output(toks[i].val)
                if out is not None:
                    return Link(toks[i].val)
        return None

    def json_value(self, toks, env, fn):
        """A `json!` value: `{..}` an object in JSON syntax, `[..]` an array,
        anything else a Rust expression."""
        if not toks:
            return None
        if toks[0].val == "{" and close_of(toks, 0) == len(toks) - 1:
            obj = {}
            for part in split_top(toks[1:-1]):
                if len(part) >= 2 and part[0].kind == "str" and part[1].val == ":":
                    obj[part[0].val] = self.json_value(part[2:], env, fn)
                elif part:
                    self.complaints.append("UNPLACEABLE: `%s` writes a json! object member "
                                           "that is not `\"key\": value`" % fn)
            return obj
        if toks[0].val == "[" and close_of(toks, 0) == len(toks) - 1:
            elems = [self.json_value(p, env, fn) for p in split_top(toks[1:-1])]
            merged = {}
            for e in elems:
                if isinstance(e, dict):
                    merged.update(e)
            return {ARRAY: merged or None}
        return self.value(toks, env, fn)

    def output(self, name):
        """What function `name` writes: a tree, or `None` for no JSON at all."""
        if name in self._out:
            return self._out[name]
        self._out[name] = None  # a cycle reads as scalar, and is not expected
        params, body = self.fns[name]
        env = {p: Param(p) for p in params}
        roots = {}
        i, n = 0, len(body)
        while i < n:
            t = body[i]
            # `let [mut] x = <expr>;`
            if t.val == "let" and i + 2 < n:
                k = i + 1
                if body[k].val == "mut":
                    k += 1
                if body[k].kind == "ident" and k + 1 < n and body[k + 1].val == "=":
                    e = k + 2
                    while e < n and not (body[e].val == ";" and self.depth0(body, k + 2, e)):
                        e += 1
                    rhs = body[k + 2:e]
                    if [x.val for x in rhs] == ["Map", ":", ":", "new", "(", ")"]:
                        env[body[k].val] = {}
                    else:
                        v = self.value(rhs, env, name)
                        if v is not None:
                            env[body[k].val] = v
                    i = e + 1
                    continue
            # `if let Some(x) = <param>` and `.. = <var>.get_mut("k")..`
            if t.val == "if" and i + 6 < n and body[i + 1].val == "let" and body[i + 2].val == "Some" \
                    and body[i + 3].val == "(" and body[i + 4].kind == "ident" and body[i + 5].val == ")" \
                    and body[i + 6].val == "=":
                x = body[i + 4].val
                src = body[i + 7] if i + 7 < n else None
                if src is not None and src.kind == "ident" and src.val in env:
                    tail = [b.val for b in body[i + 8:i + 12]]
                    if tail[:3] == [".", "get_mut", "("] and i + 11 < n and body[i + 11].kind == "str":
                        base = env[src.val]
                        if isinstance(base, Param):
                            base = roots.setdefault(src.val, {})
                            env[src.val] = base
                        if isinstance(base, dict):
                            env[x] = base.setdefault(body[i + 11].val, {})
                    elif isinstance(env[src.val], Param):
                        env[x] = env[src.val]
            # `x.insert("k".to_string(), <expr>)`
            if t.kind == "ident" and t.val in env and i + 4 < n and body[i + 1].val == "." \
                    and body[i + 2].val == "insert" and body[i + 3].val == "(" and body[i + 4].kind == "str":
                c = close_of(body, i + 3)
                parts = split_top(body[i + 4:c])
                self.put(env, t.val, body[i + 4].val, parts[1] if len(parts) > 1 else [], name)
                i = c + 1
                continue
            # `x["k"] = <expr>;`
            if t.kind == "ident" and t.val in env and i + 4 < n and body[i + 1].val == "[" \
                    and body[i + 2].kind == "str" and body[i + 3].val == "]" and body[i + 4].val == "=":
                e = i + 5
                while e < n and not (body[e].val == ";" and self.depth0(body, i + 5, e)):
                    e += 1
                self.put(env, t.val, body[i + 2].val, body[i + 5:e], name)
                i = e + 1
                continue
            i += 1
        # The function's value: its last depth-0 expression.
        last = self.tail_expr(body)
        out = self.value(last, env, name) if last else None
        if roots:
            out = {"__param__" + p: tree for p, tree in roots.items()} if out is None else out
        self._out[name] = out
        return out

    def depth0(self, toks, a, b):
        depth = 0
        for t in toks[a:b]:
            if t.kind == "punct" and t.val in OPEN:
                depth += 1
            elif t.kind == "punct" and t.val in (")", "]", "}"):
                depth -= 1
        return depth == 0

    def tail_expr(self, body):
        """The tokens after the last depth-0 `;` or `}` statement end."""
        depth, cut = 0, 0
        for k, t in enumerate(body):
            if t.kind == "punct" and t.val in OPEN:
                depth += 1
            elif t.kind == "punct" and t.val in (")", "]", "}"):
                depth -= 1
                if depth == 0 and t.val == "}":
                    cut = k + 1
            elif depth == 0 and t.val == ";":
                cut = k + 1
        return body[cut:]

    def put(self, env, var, key, rhs, fn):
        target = env[var]
        if not isinstance(target, dict):
            self.complaints.append("UNPLACEABLE: `%s` writes `%s` into `%s`, which is not an "
                                   "object this reader built" % (fn, key, var))
            return
        v = self.value(rhs, env, fn)
        if isinstance(v, Param):
            # A caller's value: the module's `<key>_json` builds it, or nothing does.
            name = key + "_json"
            if name in self.fns:
                v = Link(name)
            else:
                self.complaints.append("UNPLACEABLE: `%s` writes a caller's value under `%s` and "
                                       "the module has no `%s` to read it off" % (fn, key, name))
                v = None
        target[key] = v

    def tree(self, name, seen=()):
        """`name`'s output with every `Link` resolved."""
        def res(v, seen):
            if isinstance(v, Link):
                if v.fn in seen:
                    return None
                return res(self.output(v.fn), seen + (v.fn,))
            if isinstance(v, dict):
                return {k: res(x, seen) for k, x in v.items()}
            return None
        return res(self.output(name), seen + (name,))


def flatten(tree, prefix):
    """Every key path of a tree: `prefix.k`, and `prefix.k[]` for an array."""
    out = []
    if not isinstance(tree, dict):
        return out
    for k, v in tree.items():
        if k == ARRAY:
            p = prefix + "[]"
            out.extend(flatten(v, p))
            continue
        p = "%s.%s" % (prefix, k)
        out.append(p)
        if isinstance(v, dict):
            if ARRAY in v:
                out.append(p + "[]")
            out.extend(flatten(v, p))
    return out


def host_paths(codec_text, section):
    """`(paths, complaints)`: every key path the codec's `<section>_json`
    writes, rooted at `section`."""
    enc = RustEncoder(codec_text)
    root = section + "_json"
    if root not in enc.fns:
        return [], ["NO ENCODER: the codec has no `%s` -- the section's host side is not "
                    "read, so nothing is compared" % root]
    tree = enc.tree(root)
    if not isinstance(tree, dict) or not tree:
        return [], enc.complaints + ["NO ENCODER: `%s` writes no object this reader can see" % root]
    return sorted(set(flatten(tree, section))), enc.complaints


# ---------------------------------------------------------------------------
# Lean: the section's reader, followed
# ---------------------------------------------------------------------------

# A getter applied to `<value> "<key>"`.  SCALAR getters read a leaf; the
# others hand the key's VALUE on, to a binding.  A definition that takes the KEY
# as a parameter (`readOverrideList v "est" ..`) is not a getter here: its key
# reads under the object are not followed, which is the loud direction -- and
# no host encoder writes `overrides` (fields.py's input half says it leaves the
# request).
SCALAR = {"natAtP", "strAtP", "flagAtP", "optNatAtP", "optStrAtP", "natAt", "strAt",
          "boolAt", "optNatAt", "optStrAt", "optBoolAt"}
SUB = {"optAtP", "arrAtP", "jget", "getArr", "opt", "arrAt", "objAt"}
LISTY = {"arrAtP", "getArr", "arrAt"}
DEFHEAD = re.compile(r"(?m)^(?:(?:private|protected|noncomputable|nonrec)[ \t]+)*def[ \t]+"
                     r"([A-Za-z_][A-Za-z0-9_'!?.]*)")
IDENT = r"[A-Za-z_][A-Za-z0-9_'!?]*"
QIDENT = r"[A-Za-z_][A-Za-z0-9_'!?.]*"


def binders(sig):
    """`[(name, type)]` of the EXPLICIT `( .. )` binders of a signature, in order."""
    out, i, n = [], 0, len(sig)
    while i < n:
        c = sig[i]
        if c in "({[\u2983":
            depth, j = 0, i
            while j < n:
                if sig[j] in "({[\u2983":
                    depth += 1
                elif sig[j] in ")}]\u2984":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            if c == "(" and ":" in sig[i + 1:j]:
                names, _, ty = sig[i + 1:j].partition(":")
                for nm in names.split():
                    out.append((nm, ty.strip()))
            i = j + 1
            continue
        if c == ":":
            break
        i += 1
    return out


Def = collections.namedtuple("Def", "file qualified binders body raw sig")


class LeanReader:
    """The library's definitions, and the key paths a section's reader decodes.

    A BINDING is `(path, kind, start, end)`: the value at `path` (an object,
    `obj`, or a list of elements, `list`) held by a name from offset `start` to
    `end` of one definition's body -- a parameter for the whole body, an arm's
    pattern variable for its arm, a `let` for the rest of the body."""

    def __init__(self, files, codes=None):
        self.defs = collections.defaultdict(list)
        for p in files:
            raw = pathlib.Path(p).read_text()
            # The caller's stripped text when it has one (`fields.py` strips every
            # module once for its other two halves).
            st = codes[p] if codes and p in codes else leanfiles.strip_comments(raw)
            pairs, _ = leanfiles.qualified_names(p, "def", code=st)
            quals = collections.defaultdict(list)
            for w, q in pairs:
                quals[w].append(q)
            heads = list(DEFHEAD.finditer(st))
            for k, m in enumerate(heads):
                stop = leanfiles.NEXT_COMMAND.search(st, m.end())
                end = stop.start() if stop else len(st)
                if k + 1 < len(heads):
                    end = min(end, heads[k + 1].start())
                chunk = st[m.end():end]
                if ":=" not in chunk:
                    continue
                sig = chunk.partition(":=")[0]
                at = m.end() + len(sig) + 2
                written = m.group(1)
                q = (quals.get(written) or [written])[0]
                self.defs[written.split(".")[-1]].append(
                    Def(str(p), q, binders(sig), st[at:end], raw[at:end], sig))
        self.reads = set()
        self._seen = set()

    def resolve(self, written, caller):
        """The definitions a name written in `caller`'s file can mean: those whose
        qualified name ends in it, and of them the caller's own file's when it has
        one (Lean's current namespace), so `readState` in `PlanWire.lean` is
        `PlanWire.readState` and never `CapWire.readState` -- a read attributed to
        the wrong object is the one QUIET error this reader could make."""
        short = written.split(".")[-1]
        cands = [d for d in self.defs.get(short, [])
                 if d.qualified == written or d.qualified.endswith("." + written)]
        same = [d for d in cands if d.file == caller]
        return same or cands

    def run(self, section):
        """Every key path under `section` the kernel decodes, from the
        dispatcher(s) that read `section` off the request."""
        pat = re.compile(r"(?<![\w'.])(?:%s\.)?(?:jget|getArr)[ \t]+(%s)[ \t]+\"" % (QIDENT, IDENT))
        for ds in list(self.defs.values()):
            for d in ds:
                for m in pat.finditer(d.body):
                    close = d.body.find('"', m.end())
                    if d.raw[m.end():close] != section:
                        continue
                    env = collections.defaultdict(list)
                    self.bind(d, m, (section,), False, env)
                    self.scan(d, env, after=m.end())
        return self.reads

    def analyze(self, d, index, path, kind):
        key = (d.file, d.qualified, index, path, kind)
        if key in self._seen or index >= len(d.binders):
            return
        self._seen.add(key)
        env = collections.defaultdict(list)
        env[d.binders[index][0]].append((path, kind, 0, len(d.body)))
        self.scan(d, env)

    @staticmethod
    def lookup(env, var, at):
        best = None
        for b in env.get(var, []):
            if b[2] <= at <= b[3] and (best is None or b[3] - b[2] < best[3] - best[2]):
                best = b
        return best

    def scan(self, d, env, after=0):
        """Every key read on a bound value, in text order (a binding a read makes
        is in scope for the reads after it), then every call a binding is handed to."""
        names = sorted(SCALAR | SUB)
        pat = re.compile(r"(?<![\w'.])(?:%s\.)?(%s)[ \t\r\n]+(%s)[ \t\r\n]+\"" % (QIDENT, "|".join(names), IDENT))
        for m in pat.finditer(d.body, after):
            g, var = m.group(1), m.group(2)
            hit = self.lookup(env, var, m.start())
            if hit is None or hit[1] != "obj":
                continue
            close = d.body.find('"', m.end())
            path = hit[0] + (d.raw[m.end():close],)
            self.reads.add(path)
            if g not in SCALAR:
                self.bind(d, m, path, g in LISTY, env)
        self.calls(d, env)

    def bind(self, d, m, path, listy, env):
        """The names the value a SUB getter read at `path` is given: the pattern
        variables of the `match` it is the scrutinee of (`some w` an object,
        `some (.arr xs)` a list), scoped to their arms; the `let` it is the
        right-hand side of; and `let ys ← match .. | some (.arr xs) => pure xs`."""
        body = d.body
        head = body.rfind("\n", 0, m.start()) + 1
        line = body[head:m.start()]
        w = re.compile(r"[ \t\r\n]with\b").search(body, m.end())
        nl = body.find("\n", m.end())
        nl2 = body.find("\n", nl + 1) if nl >= 0 else -1
        # The scrutinee's `with` closes on this line or the next.
        is_match = re.search(r"\bmatch\b", line) is not None and w is not None and \
            w.start() < (nl2 if nl2 >= 0 else len(body))
        if is_match:
            arms = arm_spans(body, w.end())
            for pat, a, b in arms:
                arr = re.search(r"some[ \t]*\([ \t]*\.arr[ \t]+(%s)[ \t]*\)" % IDENT, pat)
                one = re.search(r"some[ \t]+(%s)\b" % IDENT, pat)
                if arr:
                    env[arr.group(1)].append((path, "list", a, b))
                elif one and one.group(1) != "_":
                    env[one.group(1)].append((path, "obj", a, b))
            let = re.search(r"let[ \t]+(%s)[ \t]*←[ \t]*match\b" % IDENT, line)
            if let and arms:
                for pat, a, b in arms:
                    arr = re.search(r"\.arr[ \t]+(%s)" % IDENT, pat)
                    if arr and re.match(r"[ \t\r\n]*pure[ \t]+%s\b" % re.escape(arr.group(1)), body[a:b]):
                        env[let.group(1)].append((path, "list", arms[-1][2], len(body)))
            return
        let = re.search(r"let[ \t]+(%s)[ \t]*←[ \t]*$" % IDENT, line)
        if let:
            env[let.group(1)].append((path, "list" if listy else "obj", m.end(), len(body)))

    def calls(self, d, env):
        """Every definition a bound value is handed to, by position; a list's
        elements through `xs.mapM (F ..)` and `xs.zipIdx.mapM (fun p => F .. p.1 ..)`."""
        call = re.compile(r"(?<![\w'.])(%s)((?:[ \t]+(?:[^\s()\[\]]+|\([^()]*\)))+)" % QIDENT)
        for var, bs in list(env.items()):
            for path, kind, a, b in bs:
                seg = d.body[a:b]
                if kind == "list":
                    for m in re.finditer(r"(?<![\w'.])%s\.mapM[ \t]*\([ \t]*(%s)((?:[ \t]+[^\s()]+)*)[ \t]*\)"
                                         % (re.escape(var), QIDENT), seg):
                        for f in self.resolve(m.group(1), d.file):
                            self.analyze(f, len(m.group(2).split()), path + ("[]",), "obj")
                    for m in re.finditer(r"(?<![\w'.])%s\.zipIdx\.mapM[ \t]*\([ \t]*fun[ \t]+(%s)[ \t]*=>[ \t]*(%s)([^)\n]*)"
                                         % (re.escape(var), IDENT, QIDENT), seg):
                        p, args = m.group(1), m.group(3).split()
                        if "%s.1" % p in args:
                            for f in self.resolve(m.group(2), d.file):
                                self.analyze(f, args.index("%s.1" % p), path + ("[]",), "obj")
                # Every identifier is tried as a head, not only the first of a
                # line: `match readState now w with` names two.
                for h in re.finditer(r"(?<![\w'.])%s" % QIDENT, seg):
                    fname = h.group(0)
                    if fname.split(".")[-1] not in self.defs:
                        continue
                    m = call.match(seg, h.start())
                    if not m:
                        continue
                    args = re.findall(r"\([^()]*\)|[^\s()\[\]]+", m.group(2))
                    if var not in args:
                        continue
                    for f in self.resolve(fname, d.file):
                        if f.qualified == d.qualified:
                            continue
                        self.analyze(f, args.index(var), path, kind)


def arm_spans(text, at):
    """`[(pattern, body start, body end)]` of the `match` whose `with` ends at
    `at` -- `sections.arms`' column rule, with offsets."""
    out = []
    pos = at
    lines = []
    while pos < len(text):
        e = text.find("\n", pos)
        e = len(text) if e < 0 else e
        lines.append((pos, text[pos:e]))
        pos = e + 1
    col, cur = None, None
    for start, line in lines:
        if not line.strip():
            continue
        ind = len(line) - len(line.lstrip())
        if col is None:
            if not line.lstrip().startswith("|"):
                if start == lines[0][0]:
                    continue
                break
            col = ind
        if ind < col:
            break
        if ind == col and line.lstrip().startswith("|"):
            if cur is not None:
                out.append(cur)
            arrow = line.find("=>")
            pat = line[:arrow] if arrow >= 0 else line
            cur = [pat, start + (arrow + 2 if arrow >= 0 else len(line)), start + len(line)]
            continue
        if cur is None:
            break
        cur[2] = start + len(line)
    if cur is not None:
        out.append(cur)
    return [tuple(c) for c in out]


def kernel_paths(files, section, codes=None):
    """Every key path the kernel's reader decodes under `section`, as
    `section.k1.k2` with `[]` for an array's elements."""
    reads = LeanReader(files, codes).run(section)
    out = set()
    for p in reads:
        # Prefix-closed: reading an element's field reads the element.
        s = p[0]
        for seg in p[1:]:
            s = s + "[]" if seg == "[]" else "%s.%s" % (s, seg)
            out.add(s)
    return out
