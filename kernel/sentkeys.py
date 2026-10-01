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

  * SINCE THE W-36 REPAIR (README gap 3131) the host side also follows every
    codec function that takes the section as a parameter named `<section>` of
    type `&mut Value` -- a helper the caller applies after `<section>_json`,
    as `add_worked_min` writes `state.active.workedMin` -- through
    `.get_mut("k")` and `.and_then(|v| v.get_mut("k"))` chains; and the kernel
    side follows a value handed to a call written as an anonymous
    constructor's field (`⟨.., ← readOptWorked sec⟩`), which it read as the
    argument `sec⟩` and lost.  The audit renamed the helper's key and the gate
    stayed green; it is UNREAD now.

  * SINCE W-40 TRACK E (README gap 3717) the host side is the PROGRAM, not one
    function: `host_sections` reads every `json!` object any function of `tm/src`
    or the codec builds that carries `docs` -- a request -- wherever it is written,
    and every request built as TEXT (`Text`, `skeleton`), and each of its
    top-level keys as a section, following helpers across modules (`Foreign`),
    `return`s, `.map(..).collect()`, `Vec::new()`/`.push` and every `json!` arm of
    a `match`; its sites are held to check 12's scan (`sections.sent_sections`).
    `host_paths` below is the W-36 one-function reader, kept for its record and no
    longer what check 13 asks.  The kernel side's getters, pass-throughs, key
    parameters and `where` helpers are derived by PROPERTY from the library's
    source (the comment above `LeanReader`), so the walk reads `capacity` through `need`,
    `needObj` and `readTables sec "pLounge" ..` where it stopped at the first
    `need` before, and `log.want` through `readWant`'s `where` clause.

WHAT IT CANNOT SEE, declared:
  * a key assembled from a variable, or an object built by a helper outside
    the program (`tm/src` and the codec), on the host side; the ROOT of the section is the module
    function `<section>_json`, so an encoder that writes the section some other
    way is not read at all (the loud direction: nothing to compare is a
    failure in `fields.py`, never a pass).  A writer that takes the section
    under any other parameter name (`req: &mut Value` writing
    `req["planner"]`) is not found, and a found writer's chain link it cannot
    read is a complaint.  Whether the BINARY calls a writer is not asked:
    `add_worked_min` has no caller in `tm/src` (README gap 3043).
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


def mut_value_params(toks):
    """`{fn: [param]}`: the parameters typed `&mut Value` of every `fn` outside a
    test item."""
    return {f: [p for p, ty in ps if ty[:3] == ["&", "mut", "Value"]]
            for f, ps in param_types(toks).items()}


def param_types(toks):
    """`{fn: [(param, [type tokens])]}` of every `fn` outside a test item."""
    tests = test_spans(toks)
    out = {}
    for i in range(len(toks) - 2):
        if toks[i].kind == "ident" and toks[i].val == "fn" and toks[i + 1].kind == "ident" \
                and not any(a <= i <= b for a, b in tests):
            k = i + 2
            while k < len(toks) and not (toks[k].kind == "punct" and toks[k].val == "("):
                k += 1
            if k >= len(toks):
                continue
            pclose = close_of(toks, k)
            ps = []
            for part in split_top(toks[k + 1:pclose]):
                v = [t.val for t in part]
                if v[:1] == ["mut"]:
                    v = v[1:]
                if len(v) >= 3 and v[1] == ":":
                    ps.append((v[0], v[2:]))
            out[toks[i + 1].val] = ps
    return out


class Link:
    """A value that is another encoder function's output."""
    def __init__(self, fn):
        self.fn = fn

    def __repr__(self):
        return "Link(%s)" % self.fn


class Foreign:
    """A value that is ANOTHER module's function's output (W-40, README gap 3717)."""
    def __init__(self, enc, fn):
        self.enc = enc
        self.fn = fn

    def __repr__(self):
        return "Foreign(%s::%s)" % (self.enc.module, self.fn)


class Param:
    """A value the caller handed in through parameter `name`."""
    def __init__(self, name):
        self.name = name


class Text:
    """**A JSON value a function builds as TEXT** (W-40 track E, README gap 3717): the
    fragments it appends, in source order -- `('lit', s, offset)` for a string literal
    (a `format!` template's text with `{{`/`}}` read as braces), `('hole', value, toks)`
    for anything else, the value as `RustEncoder.value` reads the expression.
    `kernel_log::log_section` builds the `log` section this way, and the capacity and
    walls requests splice it in with `format!("{{\"log\":{log},{}", &rest[1..])`,
    because a `serde_json::Value` would sort the checkpoint's keys (gap 144).  The
    branches of a `match` that each push are appended one after the other, so a key's
    value may be several values in a row: `reseal`'s `null` and its object are read
    as two alternatives and merged (`skeleton`)."""
    def __init__(self, enc, at, fn):
        self.enc = enc
        self.at = at
        self.fn = fn
        self.frags = []

    def lines(self):
        """The source lines of its literal fragments (where it gains its keys)."""
        return sorted({self.enc.text.count("\n", 0, f[2]) + 1 for f in self.frags if f[0] == "lit"})

    def __repr__(self):
        return "Text(%s@%d)" % (self.enc.module, self.at)


JSON_LEX = re.compile(r'\s*(?:([{}\[\]:,])|"((?:[^"\\]|\\.)*)"|(-?[0-9][0-9.eE+-]*|true|false|null))')


def skeleton(text, resolve):
    """The key tree of a `Text`: its literal fragments lexed as JSON, each hole a value
    `resolve(hole)` reads -- or, where a KEY is due, the members of the object the hole
    holds (`&rest[1..]`, the rest of a request whose `{` the format string wrote).
    Consecutive values for one key are alternatives (a `match`'s branches) and merge.
    Text this lexer cannot read is skipped, never guessed at: a key it cannot see is
    an UNWRITTEN key, the loud direction."""
    toks = []
    for f in text.frags:
        if f[0] == "hole":
            toks.append(("hole", f))
            continue
        s, i = f[1], 0
        while i < len(s):
            m = JSON_LEX.match(s, i)
            if not m or m.end() == i:
                if s[i:].strip() == "":
                    break
                i += 1
                continue
            if m.group(1):
                toks.append((m.group(1), None))
            elif m.group(2) is not None:
                toks.append(("str", m.group(2)))
            else:
                toks.append(("lit", m.group(3)))
            i = m.end()
    pos = [0]

    def peek(k=0):
        return toks[pos[0] + k] if pos[0] + k < len(toks) else ("eof", None)

    def starts_value(t):
        return t[0] in ("hole", "{", "[", "str", "lit")

    def one():
        t = peek()
        pos[0] += 1
        if t[0] == "hole":
            return resolve(t[1], False)
        if t[0] == "{":
            return obj()
        if t[0] == "[":
            elem = None
            while True:
                u = peek()
                if u[0] in ("]", "eof"):
                    pos[0] += 1
                    break
                if u[0] == ",":
                    pos[0] += 1
                    continue
                if not starts_value(u):
                    pos[0] += 1
                    continue
                v = one()
                if isinstance(v, dict):
                    elem = v if elem is None else (merge(elem, v) or elem)
            return {ARRAY: elem}
        return None

    def values():
        out = None
        while starts_value(peek()):
            v = one()
            if isinstance(v, dict):
                out = v if out is None else (merge(out, v) or out)
        return out

    def obj():
        o = {}
        while True:
            t = peek()
            if t[0] in ("}", "eof"):
                pos[0] += 1
                return o
            if t[0] == ",":
                pos[0] += 1
                continue
            if t[0] == "str" and peek(1)[0] == ":":
                pos[0] += 2
                v = values()
                if t[1] in o and isinstance(o[t[1]], dict) and isinstance(v, dict):
                    merge(o[t[1]], v)
                elif t[1] not in o or o[t[1]] is None:
                    o[t[1]] = v
                continue
            if t[0] == "hole":
                pos[0] += 1
                members = resolve(t[1], True)
                if isinstance(members, dict):
                    merge(o, members)
                continue
            pos[0] += 1

    return values()


ARRAY = "[]"
# A let-bound closure: calling it writes keys this reader does not compute (W-40).
CLOSURE = object()


def str_consts(toks):
    """`{NAME: [literal, ..]}` for every `const NAME: [&str; N] = ["a", ..];` of a
    module (W-40): a list of KEY literals a map may be collected over -- `LOCATIONS`,
    the two curves the capacity section's `energy` carries."""
    out = {}
    for i in range(len(toks) - 3):
        if toks[i].val == "const" and toks[i + 1].kind == "ident" and toks[i + 2].val == ":":
            k, depth = i + 3, 0
            while k < len(toks) and not (depth == 0 and toks[k].val in ("=", ";")):
                if toks[k].kind == "punct" and toks[k].val in OPEN:
                    depth += 1
                elif toks[k].kind == "punct" and toks[k].val in (")", "]", "}"):
                    depth -= 1
                k += 1
            if k >= len(toks) or toks[k].val != "=" or "str" not in [x.val for x in toks[i + 3:k]]:
                continue
            if k + 1 < len(toks) and toks[k + 1].val == "[":
                c = close_of(toks, k + 1)
                parts = split_top(toks[k + 2:c])
                if parts and all(len(x) == 1 and x[0].kind == "str" for x in parts):
                    out[toks[i + 1].val] = [x[0].val for x in parts]
    return out


class RustEncoder:
    """The encoder functions of one Rust module and what each one writes."""

    def __init__(self, text, module=None, program=None):
        toks = rust_tokens(text)
        self.module = module
        self.program = program
        self.text = text
        # Every `json!` object this module builds that carries `docs` -- a REQUEST
        # (`sections.sent_sections`' rule): `(fn, object tree, offset)`, recorded as
        # `output` evaluates the function (W-40, README gap 3717).
        self.sites = []
        self.fns = rust_fns(toks)
        self.methods = {f for f, ps in param_types(toks).items() if not ps and f in self.fns
                        and re.search(r"fn[ \t]+%s[ \t]*\([ \t]*&?(?:mut[ \t]+)?self\b" % re.escape(f), text)}
        self.mut_value = mut_value_params(toks)
        # A parameter is a CALLER'S JSON VALUE only when its type mentions `Value`;
        # any other is a Rust scalar or record the function reads fields of, and
        # `json!(worked_min)` over a `u32` writes a leaf, not a value to be placed
        # (W-36 repair, README gap 3131).
        self.scalar_params = {f: {p for p, ty in ps if "Value" not in ty}
                              for f, ps in param_types(toks).items()}
        self.complaints = []
        self._out = {}
        # Each function's bindings once `output` has read it (W-40): a `json!` request
        # written where no binding takes it -- a call's argument, `call(&json!({"docs":
        # ..}))` -- is read against them (`host_sections`).
        self._env = {}
        # Every `Text` a function builds (W-40): a request built as text is one of them.
        self.texts = []
        # `const NAME: [&str; N] = ["a", ..];` -- a list of key literals (W-40).
        self.consts = str_consts(toks)

    def is_call(self, toks, i):
        if not (toks[i].kind == "ident" and toks[i].val in self.fns and i + 1 < len(toks)
                and toks[i + 1].val == "("):
            return False
        if i == 0 or toks[i - 1].val != ".":
            return True
        # A METHOD of this module (`probe(tz).to_wire()`, `tz_table`'s; W-40): `.name(`
        # where this module defines `name` taking `self`.
        return toks[i].val in self.methods

    def value(self, toks, env, fn):
        """The tree a Rust expression writes: a dict of keys, `None` for a
        scalar, a `Link` or a `Param`."""
        toks = [t for t in toks]
        # `&x` and `&mut x` are `x` (W-40: `r.push_str(&section)`).
        while toks and toks[0].val == "&":
            toks = toks[2:] if len(toks) > 1 and toks[1].val == "mut" else toks[1:]
        if not toks:
            return None
        if len(toks) == 1 and toks[0].kind == "ident" and toks[0].val in env:
            return env[toks[0].val]
        # `format!(..)` is TEXT (W-40: the `log` section and its splice).
        if len(toks) >= 4 and [x.val for x in toks[:3]] == ["format", "!", "("] \
                and close_of(toks, 2) == len(toks) - 1:
            txt = Text(self, toks[0].at, fn)
            txt.frags.extend(self.format_frags(toks[3:-1], env, fn))
            self.texts.append((fn, txt))
            return txt
        # `Ok(<expr>)` is `<expr>` (a codec function returning `Result<Value, _>`, W-40).
        if [t.val for t in toks[:2]] == ["Ok", "("] and close_of(toks, 1) == len(toks) - 1:
            return self.value(toks[2:-1], env, fn)
        # `Value::Array(<iterator of json!>)` is an array of what it maps to.
        if [t.val for t in toks[:4]] == ["Value", ":", ":", "Array"] and toks[4].val == "(":
            inner = self.value(toks[5:close_of(toks, 4)], env, fn)
            if isinstance(inner, dict) and set(inner) == {ARRAY}:
                return inner
            return {ARRAY: inner}
        # `<iter>.map(|..| <expr>) .. .collect()` is an array of what the closure writes
        # (W-40: `render_values`' items, the capacity section's candidates).
        # A call of a let-bound CLOSURE (week_table(..), pair(..)) writes keys this
        # reader does not compute (a weekday per entry): a leaf, never the keys of a
        # helper the closure happens to call.
        if len(toks) >= 2 and toks[0].kind == "ident" and env.get(toks[0].val) is CLOSURE \
                and toks[1].val == "(":
            return None
        mapped = self.mapped(toks, env, fn)
        if mapped is not None:
            return {ARRAY: mapped}
        # `<option>.map(fname)` -- a codec function passed by name is called on the
        # value; a DEPTH-0 link of the expression's own chain only (inside a `json!`
        # literal it belongs to that member, which the object reader reads).
        depth = 0
        for i in range(len(toks) - 4):
            t = toks[i]
            if t.kind == "punct" and t.val in OPEN:
                depth += 1
            elif t.kind == "punct" and t.val in (")", "]", "}"):
                depth -= 1
            elif depth == 0 and t.val == "." and toks[i + 1].val == "map" and toks[i + 2].val == "(" \
                    and toks[i + 3].kind == "ident" and toks[i + 3].val in self.fns \
                    and toks[i + 4].val == ")" and self.output(toks[i + 3].val) is not None:
                return Link(toks[i + 3].val)
        if [t.val for t in toks[:4]] == ["Value", ":", ":", "Object"] and toks[4].val == "(":
            return self.value(toks[5:close_of(toks, 4)], env, fn)
        # Every `json!` of the expression that is not inside another one -- the arms of a
        # `match`, the branches of an `if` (W-40: `kernel_bridge`'s commands are eleven
        # arms, and the first one's keys were all this reader saw) -- merged.
        found, i = [], 0
        while i < len(toks) - 2:
            if toks[i].val == "json" and toks[i + 1].val == "!" and toks[i + 2].val == "(":
                c = close_of(toks, i + 2)
                found.append(self.json_value(toks[i + 3:c], env, fn))
                i = c + 1
                continue
            i += 1
        if found:
            objs = [v for v in found if isinstance(v, dict)]
            if not objs:
                return next((v for v in found if v is not None), None)
            if len(objs) == 1:
                return objs[0]
            out = {}
            for v in objs:
                merge(out, v)
            return out
        for i in range(len(toks)):
            if self.is_call(toks, i):
                out = self.output(toks[i].val)
                if out is not None:
                    return Link(toks[i].val)
            far = self.foreign(toks, i)
            if far is not None:
                return far
        return None

    def format_frags(self, args, env, fn):
        """The fragments of `format!(<template>, args..)`: the template's text with
        `{{`/`}}` read as braces, and each placeholder a hole -- `{}` the next
        positional argument, `{name}` a named argument or the binding it captures."""
        parts = split_top(args)
        if not parts or len(parts[0]) != 1 or parts[0][0].kind != "str":
            return [("hole", None, args)]
        tmpl, at = parts[0][0].val, parts[0][0].at
        positional = [x for x in parts[1:] if not (len(x) >= 2 and x[0].kind == "ident" and x[1].val == "="
                                                  and not (len(x) > 2 and x[2].val == "="))]
        named = {x[0].val: x[2:] for x in parts[1:]
                 if len(x) >= 2 and x[0].kind == "ident" and x[1].val == "=" and not (len(x) > 2 and x[2].val == "=")}
        frags, buf, i, nxt = [], [], 0, 0
        while i < len(tmpl):
            c = tmpl[i]
            if tmpl.startswith("{{", i) or tmpl.startswith("}}", i):
                buf.append(c)
                i += 2
                continue
            if c == "{":
                j = tmpl.find("}", i)
                if j < 0:
                    break
                name = tmpl[i + 1:j].split(":", 1)[0].strip()
                if buf:
                    frags.append(("lit", "".join(buf), at))
                    buf = []
                if name == "":
                    arg = positional[nxt] if nxt < len(positional) else []
                    nxt += 1
                elif name.isdigit():
                    arg = positional[int(name)] if int(name) < len(positional) else []
                else:
                    arg = named.get(name) or [Tok("ident", name, at)]
                frags.append(("hole", self.value(arg, env, fn), arg))
                i = j + 1
                continue
            buf.append(c)
            i += 1
        if buf:
            frags.append(("lit", "".join(buf), at))
        return frags

    def text_frags(self, toks, env, fn):
        """What `<text>.push_str(<expr>)` appends: a literal, a `format!`'s fragments,
        or one hole."""
        while toks and toks[0].val == "&":
            toks = toks[1:]
        if len(toks) == 1 and toks[0].kind == "str":
            return [("lit", toks[0].val, toks[0].at)]
        if len(toks) >= 4 and [x.val for x in toks[:3]] == ["format", "!", "("] \
                and close_of(toks, 2) == len(toks) - 1:
            return self.format_frags(toks[3:-1], env, fn)
        return [("hole", self.value(toks, env, fn), toks)]

    def foreign(self, toks, i):
        """`<module>::<fn>(` -- a function of ANOTHER module of the program, as a
        `Foreign` when that function writes JSON (`planwire::capacity_json(..)` in
        `kernel_capacity::request`, `kernel_bridge::doc_json(..)`)."""
        if self.program is None or i < 3 or i + 1 >= len(toks):
            return None
        if not (toks[i].kind == "ident" and toks[i + 1].val == "(" and toks[i - 1].val == ":"
                and toks[i - 2].val == ":" and toks[i - 3].kind == "ident"):
            return None
        enc = self.program.get(toks[i - 3].val)
        if enc is None or enc is self or toks[i].val not in enc.fns:
            return None
        if enc.output(toks[i].val) is None:
            return None
        return Foreign(enc, toks[i].val)

    def mapped(self, toks, env, fn):
        """What `.map(|..| <body>)` writes, when the expression ends its depth-0 chain
        with a `.collect`; `None` when it is not such an expression."""
        depth, m, coll = 0, None, False
        for i, t in enumerate(toks):
            if t.kind == "punct" and t.val in OPEN:
                depth += 1
            elif t.kind == "punct" and t.val in (")", "]", "}"):
                depth -= 1
            elif depth == 0 and t.val == "." and i + 2 < len(toks):
                if toks[i + 1].val == "map" and toks[i + 2].val == "(" and m is None:
                    m = i + 2
                elif toks[i + 1].val == "collect":
                    coll = True
        if m is None or not coll:
            return None
        inner = toks[m + 1:close_of(toks, m)]
        # The closure: `|args| body` (a `move` before it is not a value).
        bars = [k for k, t in enumerate(inner) if t.val == "|"]
        if len(bars) < 2:
            return None
        body = inner[bars[1] + 1:]
        if body and body[0].val == "{" and close_of(body, 0) == len(body) - 1:
            body = body[1:-1]
        v = self.value(body, env, fn)
        return v if v is not None else None

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
            if "docs" in obj:
                self.sites.append((fn, obj, toks[0].at))
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
        scalars = self.scalar_params.get(name, set())
        env = {p: Param(p) for p in params if p not in scalars}
        roots = {}
        i, n = 0, len(body)
        while i < n:
            t = body[i]
            # `let [mut] x = <expr>;`
            if t.val == "let" and i + 2 < n:
                k = i + 1
                if body[k].val == "mut":
                    k += 1
                # `let x: T = ..` -- the type is skipped (W-40: `render_values`' items).
                eq = k + 1
                if body[k].kind == "ident" and eq < n and body[eq].val == ":" and \
                        not (eq + 1 < n and body[eq + 1].val == ":"):
                    e2 = eq + 1
                    while e2 < n and not (body[e2].val in ("=", ";") and self.depth0(body, eq + 1, e2)):
                        e2 += 1
                    if e2 < n and body[e2].val == "=":
                        eq = e2
                if body[k].kind == "ident" and eq < n and body[eq].val == "=":
                    e = eq + 1
                    while e < n and not (body[e].val == ";" and self.depth0(body, eq + 1, e)):
                        e += 1
                    rhs = body[eq + 1:e]
                    ann = [x.val for x in body[k + 1:eq]]
                    if [x.val for x in rhs] == ["Map", ":", ":", "new", "(", ")"]:
                        env[body[k].val] = {}
                    elif [x.val for x in rhs] == ["Vec", ":", ":", "new", "(", ")"]:
                        env[body[k].val] = {ARRAY: None}
                    elif [x.val for x in rhs[:3]] == ["String", ":", ":"] and len(rhs) > 3 \
                            and rhs[3].val in ("new", "with_capacity"):
                        # A String built by `push_str`: TEXT (W-40, `log_section`).
                        txt = Text(self, rhs[0].at, name)
                        self.texts.append((name, txt))
                        env[body[k].val] = txt
                    elif rhs and rhs[0].val in ("|", "move"):
                        env[body[k].val] = CLOSURE
                    elif "Map" in ann:
                        # A map COLLECTED from an iterator (`prior`, `curves`): its keys
                        # are data, so it is a leaf here and not the array `.collect()`
                        # would otherwise read as -- unless it is collected over a
                        # module's list of KEY literals, keyed by the element itself
                        # (`LOCATIONS`: `energy`'s two curves; W-40).
                        keys = self.const_keys(rhs)
                        if keys:
                            env[body[k].val] = {key: None for key in keys}
                        else:
                            env.pop(body[k].val, None)
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
                    keys = self.get_mut_chain(body, i + 8, name)
                    if keys:
                        base = env[src.val]
                        if isinstance(base, Param):
                            base = roots.setdefault(src.val, {})
                            env[src.val] = base
                        if isinstance(base, dict):
                            for k in keys:
                                base = base.setdefault(k, {})
                            env[x] = base
                    elif isinstance(env[src.val], Param):
                        env[x] = env[src.val]
            # `x.push_str(<expr>)` and `x.push('c')` on a String built as TEXT (W-40).
            if t.kind == "ident" and isinstance(env.get(t.val), Text) and i + 3 < n \
                    and body[i + 1].val == "." and body[i + 2].val in ("push_str", "push") \
                    and body[i + 3].val == "(":
                c = close_of(body, i + 3)
                arg = body[i + 4:c]
                if body[i + 2].val == "push":
                    if len(arg) == 1 and arg[0].kind == "char":
                        lit = arg[0].val[1:-1]
                        env[t.val].frags.append(("lit", lit[1:] if lit.startswith("\\") else lit, arg[0].at))
                    else:
                        env[t.val].frags.append(("hole", self.value(arg, env, name), arg))
                else:
                    env[t.val].frags.extend(self.text_frags(arg, env, name))
                i = c + 1
                continue
            # `x.push(<expr>)` on a `Vec::new()` -- an element of the array (W-40:
            # `kernel_capacity::request`'s documents).
            if t.kind == "ident" and isinstance(env.get(t.val), dict) and set(env[t.val]) <= {ARRAY} \
                    and i + 3 < n and body[i + 1].val == "." and body[i + 2].val == "push" and body[i + 3].val == "(":
                c = close_of(body, i + 3)
                v = self.value(body[i + 4:c], env, name)
                if v is not None:
                    cur = env[t.val].get(ARRAY)
                    env[t.val][ARRAY] = v if cur is None else cur
                i = c + 1
                continue
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
        # The function's value: its last depth-0 expression -- and, since W-40, every
        # `return <expr>;` beside it (`resume_log_section` returns its `log_section`
        # from inside a loop and ends in an `Err`).  Several values merge.
        last = self.tail_expr(body)
        outs = [self.value(last, env, name) if last else None]
        for r in range(n):
            if body[r].kind == "ident" and body[r].val == "return":
                e = r + 1
                while e < n and not (body[e].val in (";", "}") and self.depth0(body, r + 1, e)):
                    e += 1
                outs.append(self.value(body[r + 1:e], env, name))
        outs = [o for o in outs if o is not None]
        if not outs:
            out = None
        elif len(outs) == 1:
            out = outs[0]
        else:
            out = {}
            for o in outs:
                got = self.resolve(o, ((self.module, name),))
                if isinstance(got, dict):
                    merge(out, got)
            out = out or None
        self._env[name] = env
        if roots:
            out = {"__param__" + p: tree for p, tree in roots.items()} if out is None else out
        self._out[name] = out
        return out

    def const_keys(self, rhs):
        """The key literals of a map collected over `<CONST>.iter()` whose closure keys
        each entry by the element (`(loc.to_string(), ..)`), or `None` (W-40)."""
        v = [x.val for x in rhs]
        if len(rhs) < 4 or rhs[0].val not in self.consts or v[1:5] != [".", "iter", "(", ")"]:
            return None
        if "collect" not in v:
            return None
        bars = [k for k, x in enumerate(rhs) if x.val == "|"]
        if len(bars) < 2 or bars[1] != bars[0] + 2 or rhs[bars[0] + 1].kind != "ident":
            return None
        elem = rhs[bars[0] + 1].val
        for k in range(len(rhs) - 5):
            if rhs[k].val == "(" and v[k + 1:k + 6] in ([elem, ".", "to_string", "(", ")"],):
                return self.consts[rhs[0].val]
            if rhs[k].val == "(" and v[k + 1:k + 7] == ["*", elem, ".", "to_string", "(", ")"]:
                return self.consts[rhs[0].val]
        return None

    def get_mut_chain(self, body, j, fn):
        """The keys of `.get_mut("a")` followed by any number of
        `.and_then(|v| v.get_mut("b"))` and `.and_then(Value::as_object_mut)`,
        read from token `j`: `planwire::add_worked_min`'s path to
        `state.active` (W-36 repair, README gap 3131).  A link of the chain this
        reader cannot read is a complaint, never a silently shorter path."""
        vals = [t.val for t in body]
        keys = []
        while j + 2 < len(body) and vals[j] == ".":
            if vals[j + 1] == "get_mut" and vals[j + 2] == "(" and j + 4 < len(body) \
                    and body[j + 3].kind == "str" and vals[j + 4] == ")":
                keys.append(body[j + 3].val)
                j += 5
                continue
            if vals[j + 1] == "and_then" and vals[j + 2] == "(":
                c = close_of(body, j + 2)
                inner = body[j + 3:c]
                iv = [t.val for t in inner]
                got = [inner[k + 2].val for k in range(len(inner) - 3)
                       if iv[k] == "get_mut" and iv[k + 1] == "(" and inner[k + 2].kind == "str"
                       and iv[k + 3] == ")"]
                if len(got) == 1:
                    keys.append(got[0])
                elif iv not in (["Value", ":", ":", "as_object_mut"], ["Value", ":", ":", "as_array_mut"]):
                    self.complaints.append("UNPLACEABLE: `%s` walks into its value through an "
                                           "`.and_then(..)` this reader cannot read" % fn)
                    return []
                j = c + 1
                continue
            break
        return keys

    def writers(self, section):
        """The codec's OTHER writers into the section: every function outside a
        test with a parameter named `section` of type `&mut Value` -- a helper
        the caller applies to the section after `<section>_json` built it, as
        `add_worked_min` is (W-36 repair, README gap 3131; the audit renamed its
        key and the gate stayed green).  Found by the parameter's name and type,
        the codec's own convention (`add_batch_max_min(capacity: &mut Value ..)`
        writes into the capacity section, which this half does not ask)."""
        return sorted(f for f, ps in self.mut_value.items() if section in ps)

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
        if isinstance(target, (Link, Foreign)):
            # A helper's object, extended here (`signed_pair_of`'s `neg` beside
            # `nat_pair_of`'s pair; W-40): a copy of the helper's keys, then this one.
            got = self.resolve(target)
            if isinstance(got, dict):
                target = env[var] = dict(got)
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

    def resolve(self, v, seen=()):
        """A tree with every `Link`, `Foreign` and `Text` resolved."""
        if isinstance(v, Text):
            if ("text", id(v)) in seen:
                return None
            inner = seen + (("text", id(v)),)

            def hole(f, members):
                # Where a KEY is due, `&rest[1..]` is the members of `rest`'s object.
                if members:
                    tk = [x.val for x in f[2] if x.val != "&"]
                    if len(tk) >= 2 and "".join(tk[1:]) == "[1..]" and tk[0] in v.enc._env.get(v.fn, {}):
                        return v.enc.resolve(v.enc._env[v.fn][tk[0]], inner)
                    return None
                return v.enc.resolve(f[1], inner)
            return skeleton(v, hole)
        if isinstance(v, Foreign):
            if (v.enc.module, v.fn) in seen:
                return None
            return v.enc.resolve(v.enc.output(v.fn), seen + ((v.enc.module, v.fn),))
        if isinstance(v, Link):
            if (self.module, v.fn) in seen:
                return None
            return self.resolve(self.output(v.fn), seen + ((self.module, v.fn),))
        if isinstance(v, dict):
            return {k: self.resolve(x, seen) for k, x in v.items()}
        return None

    def tree(self, name, seen=()):
        """`name`'s output with every `Link` and `Foreign` resolved."""
        return self.resolve(self.output(name), seen + ((self.module, name),))


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
    for w in enc.writers(section):
        if w == root:
            continue
        out = enc.output(w)
        sub = out.get("__param__" + section) if isinstance(out, dict) else None
        if not isinstance(sub, dict) or not sub:
            enc.complaints.append("UNPLACEABLE: `%s` takes the %s section as `&mut Value` and "
                                  "writes nothing this reader can see" % (w, section))
            continue
        merge(tree, enc.resolve(sub, ((enc.module, w),)))
    return sorted(set(flatten(tree, section))), enc.complaints


# ===========================================================================
# EVERY PLACE A REQUEST GAINS A SECTION KEY (W-40 track E, README gap 3717)
#
# `host_paths` asks ONE function of ONE module -- `planwire::planner_json` -- and
# check 13 said so in every line it printed ("the other sections' encoders are not
# asked", gap 3081).  `day.rs`' `call_the_walls` wrote `emit.walls.week` for W-39's
# week grid with nothing asking whether a kernel reader decodes it.  The class is
# "every place a request JSON object gains a section key", and this is its reader:
#
#   * THE PROGRAM is every `.rs` file of the `tm` binary and of every crate it links
#     by path (`program_roots`, read off `tm/Cargo.toml`: `tm/src`, `tm-core/src`,
#     `kernel/tm-kernel-ffi/src`), one `RustEncoder` per module, each able to follow
#     a call written `<module>::<fn>(..)` into another (`Foreign`).
#   * A SITE is a `json!({..})` object any function of the program builds that
#     carries `docs` -- `sections.sent_sections`' rule for a request, the scan check
#     12 roots itself on -- and EVERY top-level key of it is a section key whose
#     value is read as `host_paths` reads a codec function's (helpers by call,
#     `Value::Array`, `.map(..).collect()`, `Vec::new()` and `.push`).  Test items
#     are not the program (`test_spans`).
#   * A section's host side is the union of its sites' values, any module's
#     `<section>_json` that its own module does not compose (the only host side of a
#     section no shipped request carries yet: `planner`), and every function taking
#     the section as `&mut Value` (`add_worked_min(planner ..)`,
#     `add_batch_max_min(capacity ..)`).
#
# A REQUEST BUILT AS TEXT IS READ TOO: `kernel_log::log_section` builds the `log`
# section by `push_str`, `kernel_log::request` builds its whole request so, and the
# capacity and walls requests splice the section in with `format!("{{\"log\":{log},
# {}", &rest[1..])`, because a `serde_json::Value` would sort the checkpoint's keys.
# A `Text` keeps the fragments in source order and `skeleton` lexes the literals as
# JSON, each hole a value (and, where a KEY is due, `&rest[1..]`'s members).  And the
# sites are held to check 12's scan of `tm/src` (`sections.sent_sections`), so a
# request this reader cannot see is a failure by name, not a key compared with
# nothing.
#
# WHAT IT CANNOT SEE, declared: a key assembled from a variable (the weekdays of
# `capacity_json`'s week tables) is a leaf -- a map collected over a module's list of
# key LITERALS keyed by the element (`LOCATIONS`) is read as those keys; a site whose
# section value is a caller's parameter (`kernel_log::request`'s `tz`) is read through
# the call only where the call is the program's own; a `return` inside a closure is
# read as the function's; text sliced any way but `[1..]` at a key is a hole; and a
# `match` whose arms each push text is read as every arm, one after another, so two
# arms' keys merge -- a key one arm writes and another omits reads as written.
# ===========================================================================

# The binary whose requests these are.
BINARY = "tm"


def program_roots(root):
    """The source directories of the `tm` binary and of every crate it links by PATH
    (`tm/Cargo.toml`'s `path = ..` dependencies: `tm-core`, `tm-kernel-ffi`) -- a
    property of the manifest, not a list: a crate the binary starts to link is read
    without an edit here."""
    root = pathlib.Path(root)
    manifest = (root / BINARY / "Cargo.toml").read_text()
    dirs = [root / BINARY / "src"]
    for m in re.finditer(r'path[ \t]*=[ \t]*"([^"]+)"', manifest):
        d = (root / BINARY / m.group(1)).resolve() / "src"
        if d.is_dir() and d not in dirs:
            dirs.append(d)
    return dirs


def program(root):
    """`{module name: RustEncoder}` over the program's files under repository `root`."""
    files = []
    for d in program_roots(root):
        files.extend(sorted(leanfiles.rust_files(d)))
    prog = {}
    for f in files:
        name = f.stem if f.stem != "mod" else f.parent.name
        if name in prog:
            continue
        prog[name] = RustEncoder(f.read_text(errors="replace"), module=name, program=prog)
        prog[name].path = f
    return prog


def has_docs(inner):
    """Does the `json!` object literal `inner` (its tokens, braces included) carry
    `docs` at its own top level -- `sections.sent_sections`' rule for a request?"""
    return any(len(part) >= 2 and part[0].kind == "str" and part[0].val == "docs" and part[1].val == ":"
               for part in split_top(inner[1:-1]))


def host_sections(root, sections):
    """`({section: sorted key paths}, {section: [site]}, complaints)` -- every key path
    the program writes under each of `sections`, read at every request site, the
    codec's `<section>_json` and its `&mut Value` writers.

    A SITE is a request the program builds: a `json!` object carrying `docs`, wherever
    it is written -- bound, returned, or a call's own argument (`call(&json!({"docs":
    ..}))`, which a binding-only read missed: `kernel_bridge`'s tree check) -- or a
    `Text` whose skeleton carries `docs` (`kernel_log::request`, and the capacity and
    walls requests once their `format!` splices the `log` section in).  AND THE SITES
    ARE HELD TO CHECK 12'S OWN SCAN (`sections.sent_sections`, over `tm/src`): a region
    that scan reads as a request sending a section, outside a test, is a line some site
    here must hold -- or this reader missed a request, and that FAILS by name."""
    import sections as reqsec
    prog = program(root)
    for enc in prog.values():
        for fn in list(enc.fns):
            enc.output(fn)
    # A request written where no binding takes it is read against its function's
    # bindings: every outermost `json!` object of every body that carries `docs`.
    for enc in prog.values():
        seen = {at for _, _, at in enc.sites}
        for fn, (_, body) in enc.fns.items():
            env = enc._env.get(fn, {})
            i = 0
            while i < len(body) - 2:
                if body[i].val == "json" and body[i + 1].val == "!" and body[i + 2].val == "(":
                    c = close_of(body, i + 2)
                    inner = body[i + 3:c]
                    if inner and inner[0].val == "{" and close_of(inner, 0) == len(inner) - 1 \
                            and inner[0].at not in seen and has_docs(inner):
                        enc.json_value(inner, env, fn)
                        seen.add(inner[0].at)
                    i = c + 1
                    continue
                i += 1
    trees = {sec: {} for sec in sections}
    where = collections.defaultdict(list)
    held = collections.defaultdict(set)   # file -> the lines a site holds
    complaints = []

    def take(enc, fn, line_label, members, lines):
        for key, val in members.items():
            if key not in trees:
                if key != "docs":
                    complaints.append("UNKNOWN SECTION: %s (`%s`) writes `%s` into a request and "
                                      "the kernel reads no such section" % (line_label, fn, key))
                continue
            where[key].append(line_label)
            sub = enc.resolve(val, ((enc.module, fn),))
            if isinstance(sub, dict):
                merge(trees[key], sub)
        held[enc.path.name].update(lines)

    for enc in prog.values():
        done = set()
        for fn, obj, at in enc.sites:
            if at in done:
                continue
            done.add(at)
            line = enc.text.count("\n", 0, at) + 1
            take(enc, fn, "%s:%d" % (enc.path.name, line), obj, {line})
        for fn, txt in enc.texts:
            tree = enc.resolve(txt, ((enc.module, fn),))
            if isinstance(tree, dict) and "docs" in tree:
                lines = txt.lines()
                take(enc, fn, "%s:%s (text)" % (enc.path.name, ",".join(map(str, lines))), tree, set(lines))
    # The floor: check 12's scan of what `tm/src` sends.
    src = pathlib.Path(root) / BINARY / "src"
    found, _ = reqsec.sent_sections(src, sections)
    for key, regs in sorted(found.items()):
        for fname, line, test in regs:
            if not test and line not in held.get(fname, ()):
                complaints.append("UNREAD REQUEST: %s:%d sends `%s` (check 12's scan, "
                                  "`sections.sent_sections`) and this reader built no request "
                                  "there -- its keys are compared with nothing" % (fname, line, key))
    # A section's ROOT, in any module of the program, is its `<section>_json` that no
    # function of that module composes: `planwire::planner_json`, `capacity_json`.
    # `plan_json` is the candidate record's `plan` object, composed by `cand_json`, and
    # the top-level `plan` section (W-24's rows) has no host encoder -- its name is a
    # collision, not a root (W-40).  Every function taking the section as `&mut Value`
    # joins it (`add_worked_min(planner ..)`, `add_batch_max_min(capacity ..)`).
    roots_seen = []
    for enc in prog.values():
        composed = set()
        for f, (_, body) in enc.fns.items():
            for i in range(len(body)):
                if enc.is_call(body, i) and body[i].val != f:
                    composed.add(body[i].val)
        for sec in sections:
            root_fn = sec + "_json"
            if root_fn in enc.fns and root_fn not in composed:
                where[sec].append("%s `%s`" % (enc.path.name, root_fn))
                roots_seen.append(enc)
                t = enc.tree(root_fn)
                if isinstance(t, dict):
                    merge(trees[sec], t)
            for w in enc.writers(sec):
                if w == root_fn:
                    continue
                out = enc.output(w)
                sub = out.get("__param__" + sec) if isinstance(out, dict) else None
                if isinstance(sub, dict) and sub:
                    where[sec].append("%s `%s`" % (enc.path.name, w))
                    roots_seen.append(enc)
                    merge(trees[sec], enc.resolve(sub, ((enc.module, w),)))
    paths = {sec: sorted(set(flatten(trees[sec], sec))) for sec in sections}
    for enc in dict.fromkeys(roots_seen):
        complaints.extend(enc.complaints)
    return paths, dict(where), complaints


def merge(into, tree):
    """`tree`'s keys into `into`, recursively."""
    for k, v in tree.items():
        if isinstance(v, dict) and isinstance(into.get(k), dict):
            merge(into[k], v)
        elif k not in into or into[k] is None:
            into[k] = v


# ---------------------------------------------------------------------------
# Lean: the section's reader, followed
# ---------------------------------------------------------------------------

# THE GETTERS ARE A PROPERTY, NOT A LIST (W-40 track E, README gap 3717).  Until W-40 this
# was three hand-kept sets -- SCALAR, SUB and LISTY, eighteen names -- and three of the
# eighteen (objAt, optBoolAt and optStrAt) named nothing in the library, while fourteen
# definitions the property below reads as getters were in none of them -- `need`,
# `pairAt`, `clockAt`, `posAt`, `signedAt`, `optSignedAt`, `optDateAt`, `optClockAt` and
# `optNatWith`, every getter the capacity section is read through, among them -- so the
# walk lost `capacity` at its first `need` (3 key paths of the 98 it reads now).  A
# getter is now any definition whose first two EXPLICIT binders are a `JVal` and a
# `String` key: it reads that key of that value.  It hands the key's VALUE on when its
# result type mentions `JVal`, a LIST of values when `List JVal`, and reads a leaf
# otherwise (`LeanReader` derives its getters from the signatures; the old sets are gone).
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


WHERE_HEAD = re.compile(r"(?m)^([ \t]+)(%s)\b" % r"[A-Za-z_][A-Za-z0-9_'!?]*")


def where_defs(st, raw, end):
    """`[(name, signature, body start, body end)]` of the `where` clause that begins at
    offset `end` of the stripped text `st` -- a line that is `where` alone at column 0
    -- up to the next column-0 line: each local definition is a line at the clause's
    first indentation that opens with a name and reaches `:=`."""
    if not re.match(r"where[ \t]*(?:\n|$)", st[end:]):
        return []
    start = st.find("\n", end)
    if start < 0:
        return []
    stop = leanfiles.NEXT_COMMAND.search(st, start + 1)
    stop = stop.start() if stop else len(st)
    block = st[start + 1:stop]
    heads = [m for m in WHERE_HEAD.finditer(block)]
    if not heads:
        return []
    col = len(heads[0].group(1))
    heads = [m for m in heads if len(m.group(1)) == col]
    out = []
    for k, m in enumerate(heads):
        b_end = heads[k + 1].start() if k + 1 < len(heads) else len(block)
        chunk = block[m.end():b_end]
        if ":=" not in chunk:
            continue
        sig = chunk.partition(":=")[0]
        a = start + 1 + m.end() + len(sig) + 2
        out.append((m.group(2), sig, a, start + 1 + b_end))
    return out


def result_type(sig):
    """The result type of a signature: the text after its last depth-0 `:`."""
    depth, cut = 0, None
    for i, c in enumerate(sig):
        if c in "({[\u2983":
            depth += 1
        elif c in ")}]\u2984":
            depth -= 1
        elif c == ":" and depth == 0:
            cut = i
    return sig[cut + 1:].strip() if cut is not None else ""


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
                # Its `where` helpers (W-40): a `where` at column 0 ends the body above
                # and opens local definitions the body calls by their short names --
                # `readWant`'s two local definitions read `want.headersFrom` and
                # `want.render`, which the walk could not see while they were nobody's.
                for local in where_defs(st, raw, end):
                    nm, lsig, la, lb = local
                    self.defs[nm].append(Def(str(p), "%s.%s" % (q, nm), binders(lsig), st[la:lb], raw[la:lb], lsig))
        self.reads = set()
        self._seen = set()
        # The getters, by property (the comment above this class): `{short name: kind}`, kind
        # `sub`, `list` or `scalar`.  A short name two definitions share with two kinds takes
        # the one that hands a value on, the conservative reading (a binding too many is a
        # read attributed to a name nothing reads through; a binding too few loses reads).
        self.getters = {}
        rank = {"scalar": 0, "sub": 1, "list": 2}
        for short, ds in self.defs.items():
            for d in ds:
                if len(d.binders) >= 2 and d.binders[0][1] == "JVal" and d.binders[1][1] == "String":
                    ret = result_type(d.sig)
                    kind = "list" if re.search(r"\bList[ \t]+JVal\b", ret) else \
                        "sub" if re.search(r"\bJVal\b", ret) else "scalar"
                    if rank[kind] >= rank.get(self.getters.get(short), -1):
                        self.getters[short] = kind
        # PASS-THROUGHS, by property: a definition returning one of its own `JVal`
        # parameters unchanged (`needObj v p` checks that `v` is an object and hands `v`
        # back), `{short name: binder index}`.  `let t ← needObj t0 p` is `t0` under another
        # name, so the walk keeps reading through it -- it lost `capacity` there until W-40.
        self.passthrough = {}
        for short, ds in self.defs.items():
            for d in ds:
                if short in self.getters:
                    continue
                for i, (nm, ty) in enumerate(d.binders):
                    if ty == "JVal" and re.search(r"(?:\.ok|\bpure|\breturn)[ \t]+%s\b(?![.'\w])" % re.escape(nm), d.body) \
                            and "JVal" in result_type(d.sig):
                        self.passthrough[short] = i
                        break

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
        pat = re.compile(r"(?<![\w'.])(?:%s\.)?(jget|getArr)[ \t]+(%s)[ \t]+\"" % (QIDENT, IDENT))
        for ds in list(self.defs.values()):
            for d in ds:
                for m in pat.finditer(d.body):
                    close = d.body.find('"', m.end())
                    if d.raw[m.end():close] != section:
                        continue
                    env = collections.defaultdict(list)
                    # `getArr j "docs"` hands a LIST on (W-40: it was bound as an object,
                    # so `runLoad`'s documents were read by nothing this walk could see).
                    self.bind(d, m, (section,), self.getters.get(m.group(1)) == "list", env)
                    self.scan(d, env, after=m.end())
        return self.reads

    def analyze(self, d, index, path, kind, keys=()):
        """Follow `d` with its `index`-th binder bound to the value at `path`, and each
        `(binder index, literal)` of `keys` -- a KEY handed in as a `String` argument
        (`readTables sec "pLounge" ..`) -- bound to its literal for the whole body."""
        key = (d.file, d.qualified, index, path, kind, keys)
        if key in self._seen or index >= len(d.binders):
            return
        self._seen.add(key)
        env = collections.defaultdict(list)
        env[d.binders[index][0]].append((path, kind, 0, len(d.body)))
        kenv = {d.binders[i][0]: lit for i, lit in keys if i < len(d.binders)}
        self.scan(d, env, kenv=kenv)

    @staticmethod
    def lookup(env, var, at):
        best = None
        for b in env.get(var, []):
            if b[2] <= at <= b[3] and (best is None or b[3] - b[2] < best[3] - best[2]):
                best = b
        return best

    def scan(self, d, env, after=0, kenv=None):
        """Every key read on a bound value, in text order (a binding a read makes
        is in scope for the reads after it), then every call a binding is handed to.
        A key is a literal, or a `String` binder `kenv` bound to one; a getter is any
        definition `getters` derives (the property, not a list)."""
        kenv = kenv or {}
        names = sorted(self.getters, key=len, reverse=True)
        keyalt = r"\"" if not kenv else r"(?:\"|(%s)\b)" % "|".join(re.escape(k) for k in kenv)
        pat = re.compile(r"(?<![\w'.])(?:%s\.)?(%s)[ \t\r\n]+(%s)[ \t\r\n]+%s"
                         % (QIDENT, "|".join(re.escape(n) for n in names), IDENT, keyalt))
        # A binding a pass-through makes (`let v ← needObj d0 ..`) is in scope for reads
        # BEFORE it in this loop's text order only on the next round, so the reads and
        # the bindings run to a fixpoint; reads are a set and a binding is added once.
        done = set()
        for _ in range(8):
            size = sum(len(b) for b in env.values())
            for m in pat.finditer(d.body, after):
                g, var = m.group(1), m.group(2)
                hit = self.lookup(env, var, m.start())
                if hit is None or hit[1] != "obj":
                    continue
                if kenv and m.lastindex and m.lastindex >= 3 and m.group(3):
                    lit = kenv[m.group(3)]
                else:
                    close = d.body.find('"', m.end())
                    lit = d.raw[m.end():close]
                path = hit[0] + (lit,)
                self.reads.add(path)
                if self.getters.get(g) != "scalar" and (m.start(), path) not in done:
                    done.add((m.start(), path))
                    self.bind(d, m, path, self.getters.get(g) == "list", env)
            self.passes(d, env, after)
            self.matches(d, env)
            self.loops(d, env)
            if sum(len(b) for b in env.values()) == size:
                break
        self.calls(d, env, kenv)

    def loops(self, d, env):
        """`for dj in docsJ do ..` over a bound LIST: the loop variable is an element
        (`runLoad`'s documents and commands, W-40)."""
        for m in re.finditer(r"\bfor[ \t]+(%s)[ \t]+in[ \t]+(%s)[ \t]+do\b" % (IDENT, IDENT), d.body):
            hit = self.lookup(env, m.group(2), m.start())
            if hit is None or hit[1] != "list":
                continue
            bnd = (hit[0] + ("[]",), "obj", m.end(), len(d.body))
            if bnd not in env[m.group(1)]:
                env[m.group(1)].append(bnd)

    def matches(self, d, env):
        """`match w0 with | some wv => ..` over a BOUND name: each arm's value is the
        name's (`readState`'s `window`, read as an `Option` and matched on)."""
        for m in re.finditer(r"\bmatch[ \t]+(%s)[ \t]+with\b" % IDENT, d.body):
            hit = self.lookup(env, m.group(1), m.start())
            if hit is None:
                continue
            for pat, a, b in arm_spans(d.body, m.end()):
                one = re.search(r"some[ \t]+(%s)\b" % IDENT, pat)
                if one and one.group(1) != "_":
                    bnd = (hit[0], hit[1], a, b)
                    if bnd not in env[one.group(1)]:
                        env[one.group(1)].append(bnd)

    def passes(self, d, env, after=0):
        """`let x ← P .. v ..` where `P` is a pass-through on `v`'s position: `x` holds
        `v`'s value, for the rest of the body (`needObj`, by property)."""
        if not self.passthrough:
            return
        pat = re.compile(r"let[ \t]+(%s)[ \t]*←[ \t]*(?:%s\.)?(%s)((?:[ \t]+(?:[^\s()\[\]\u27e8\u27e9,]+|\([^()]*\)))+)"
                         % (IDENT, QIDENT, "|".join(re.escape(n) for n in sorted(self.passthrough, key=len, reverse=True))))
        for m in pat.finditer(d.body, after):
            args = re.findall(r"\([^()]*\)|[^\s()\[\]\u27e8\u27e9,]+", m.group(3))
            i = self.passthrough[m.group(2)]
            if i >= len(args):
                continue
            hit = self.lookup(env, args[i], m.start())
            b = (hit[0], hit[1], m.end(), len(d.body)) if hit is not None else None
            if b is not None and b not in env[m.group(1)]:
                env[m.group(1)].append(b)

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
                # `.ok xs` -- the getter's value itself, for a getter that hands a value or
                # a list on without an `Option` (`arrAt`'s list, `need`'s value; W-40).
                okv = re.search(r"\.ok[ \t]+(%s)\b" % IDENT, pat)
                if arr:
                    env[arr.group(1)].append((path, "list", a, b))
                elif one and one.group(1) != "_":
                    env[one.group(1)].append((path, "obj", a, b))
                elif okv and okv.group(1) not in ("none", "_"):
                    env[okv.group(1)].append((path, "list" if listy else "obj", a, b))
            let = re.search(r"let[ \t]+(%s)[ \t]*←[ \t]*match\b" % IDENT, line)
            if not let:
                # `let docsJ ←` on its own line, the `match` on the next (`runLoad`'s
                # documents, W-40): the binding is the line above's.
                if line.strip() == "match":
                    # The nearest non-blank line above (a comment is blanked to spaces).
                    above = body[:head].rstrip().rsplit("\n", 1)[-1]
                    let = re.search(r"let[ \t]+(%s)[ \t]*←[ \t]*$" % IDENT, above.rstrip())
            if let and arms:
                for pat, a, b in arms:
                    arr = re.search(r"\.arr[ \t]+(%s)" % IDENT, pat)
                    okv = re.search(r"\.ok[ \t]+(%s)\b" % IDENT, pat)
                    got = arr or (okv if listy else None)
                    if got and re.match(r"[ \t\r\n]*pure[ \t]+%s\b" % re.escape(got.group(1)), body[a:b]):
                        env[let.group(1)].append((path, "list", arms[-1][2], len(body)))
            return
        let = re.search(r"let[ \t]+(%s)[ \t]*←[ \t]*$" % IDENT, line)
        if let:
            env[let.group(1)].append((path, "list" if listy else "obj", m.end(), len(body)))

    def calls(self, d, env, kenv=None):
        """Every definition a bound value is handed to, by position; a list's
        elements through `xs.mapM (F ..)` and `xs.zipIdx.mapM (fun p => F .. p.1 ..)`.
        A `String` argument beside it -- a literal, or a key this definition was itself
        handed -- goes with it as a KEY (W-40): `readTables sec "pLounge" ..` reads
        `pLounge` of `sec` inside `readTables`, and `pairAt v "safety" ..` reads `num`
        and `den` under `safety` inside `pairWith`."""
        kenv = kenv or {}
        # An argument token stops at `⟨`, `⟩` and `,` as well as at a bracket: a call
        # written as an anonymous constructor's field -- `pure ⟨.., ← readOptWorked sec⟩`,
        # `PlanWire.readState`'s sixth field -- read `sec⟩` as its argument, so the value
        # was never followed and `state.active.workedMin` was decoded by no reader this
        # module could see (W-36 repair, README gap 3131: the auditor's gap-3124 exit
        # FAILED check 13 on a key the kernel reads).
        call = re.compile(r"(?<![\w'.])(%s)((?:[ \t]+(?:[^\s()\[\]\u27e8\u27e9,]+|\([^()]*\)))+)" % QIDENT)
        for var, bs in list(env.items()):
            for path, kind, a, b in bs:
                seg = d.body[a:b]
                if kind == "list":
                    for m in re.finditer(r"(?<![\w'.])%s\.mapM[ \t]*\([ \t]*(%s)((?:[ \t]+[^\s()]+)*)[ \t]*\)"
                                         % (re.escape(var), QIDENT), seg):
                        for f in self.resolve(m.group(1), d.file):
                            self.analyze(f, len(m.group(2).split()), path + ("[]",), "obj")
                    # `xs.foldl F init` (`readEmitSection`'s items, W-40): `F`'s second
                    # argument is an element, `List.foldl`'s own order.
                    for m in re.finditer(r"(?<![\w'.])%s\.foldl[ \t]+\(?[ \t]*(%s)\b" % (re.escape(var), QIDENT), seg):
                        for f in self.resolve(m.group(1), d.file):
                            self.analyze(f, 1, path + ("[]",), "obj")
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
                    # A string literal is ONE argument: the stripped body blanks its
                    # content to spaces, which split it in two and shifted every
                    # argument after it by one.
                    argpat = r"\"[^\"\n]*\"|\([^()]*\)|[^\s()\[\]\u27e8\u27e9,]+"
                    args = re.findall(argpat, m.group(2))
                    if var not in args:
                        continue
                    # The same arguments over the RAW text (the stripped body blanks a
                    # string's content): a literal is a key, and so is a name this
                    # definition holds bound to one.
                    raw_args = re.findall(argpat, d.raw[a + m.start(2):a + m.end(2)])
                    for f in self.resolve(fname, d.file):
                        if f.qualified == d.qualified:
                            continue
                        keys = []
                        if len(raw_args) == len(args):
                            for j, x in enumerate(raw_args):
                                if j >= len(f.binders) or f.binders[j][1] != "String":
                                    continue
                                if len(x) >= 2 and x[0] == x[-1] == '"':
                                    keys.append((j, x[1:-1]))
                                elif x in kenv:
                                    keys.append((j, kenv[x]))
                        self.analyze(f, args.index(var), path, kind, tuple(keys))


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


def kernel_paths(files, section, codes=None, reader=None):
    """Every key path the kernel's reader decodes under `section`, as
    `section.k1.k2` with `[]` for an array's elements.  `reader` is a `LeanReader`
    to reuse (its definitions are read once; each section's walk starts afresh)."""
    r = reader or LeanReader(files, codes)
    r.reads, r._seen = set(), set()
    reads = r.run(section)
    out = set()
    for p in reads:
        # Prefix-closed: reading an element's field reads the element.
        s = p[0]
        for seg in p[1:]:
            s = s + "[]" if seg == "[]" else "%s.%s" % (s, seg)
            out.add(s)
    return out


def normalized(paths, section):
    """`paths`, PREFIX-CLOSED under `section` and with an array of scalars read as the
    key it is under (W-40): `x[]` with nothing under it -- `tz.then`'s pairs,
    `emit[].at`'s four numbers -- says how a value is shaped, not which keys it has,
    and the kernel reads such an array positionally, so its walk ends at `x`.  The
    host's `flatten` names `docs[].path` and not `docs[]`; the kernel's walk names
    both: closing both sides makes them say the same thing."""
    out = set()
    for p in paths:
        if not (p.startswith(section + ".") or p.startswith(section + "[")):
            continue
        # Every prefix that ends at a key or at an array marker: `a.b[].c` is `a.b`,
        # `a.b[]`, `a.b[].c`.
        for k in range(len(section) + 1, len(p) + 1):
            if k == len(p) or p[k] == "." or p.startswith("[]", k):
                out.add(p[:k])
            if p.startswith("[]", k - 2) and k >= len(section) + 2:
                out.add(p[:k])
    out.discard(section)
    return {p for p in out
            if not (p.endswith("[]") and not any(q != p and q.startswith(p) for q in out))}
