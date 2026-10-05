#!/usr/bin/env python3
"""A Rust call graph BY NAME over a set of source trees (stage 6 W-46 track C;
kernel/README.md gap 4752, restated as a class there) -- the second instrument
beside `class.sh`'s symbol table, read off the sources instead of the binary.

Tokenizes each .rs file (comments, strings, chars and raw strings stripped),
finds every `fn NAME` with its body by brace matching, qualifies it by its
enclosing `impl ... TYPE` (the last path segment before `{` / `for`), marks
`#[cfg(test)]` items (a module, a fn, an impl) and `#[test]` fns as TEST, and
records, for every fn, the set of identifiers its body mentions and whether it
sits in a trait impl (dispatch a by-name graph cannot follow).

`python3 rsgraph.py ROOT...` prints JSON: {"fns":[{file,line,end,name,qual,test,timpl,refs,mod}]}.

BY NAME is its blind spot, declared: two functions of one name are one node,
so a name another type also uses (`minutes`, `empty`, `none`, `wall`,
`sort_key`, `from_minutes`, `worked_min_at` at W-46) reads as reached -- the
symbol table settles those, and every difference between the two instruments
is read by hand (README "W-46 track C" section 1).
"""
import json, os, re, sys

def strip(src):
    out = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if src.startswith('//', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        if src.startswith('/*', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith('/*', j): depth += 1; j += 2
                elif src.startswith('*/', j): depth -= 1; j += 2
                else: j += 1
            out.append(re.sub(r'[^\n]', ' ', src[i:j])); i = j; continue
        m = re.match(r'b?r(#*)"', src[i:i+300])
        if m and (i == 0 or not (src[i-1].isalnum() or src[i-1] == '_')):
            hashes = m.group(1)
            close = '"' + hashes
            j = src.find(close, i + m.end())
            j = n if j < 0 else j + len(close)
            out.append(re.sub(r'[^\n]', ' ', src[i:j])); i = j; continue
        if c == '"' or (c == 'b' and i + 1 < n and src[i+1] == '"' and (i == 0 or not (src[i-1].isalnum() or src[i-1] == '_'))):
            j = i + (2 if c == 'b' else 1)
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            j += 1
            out.append(re.sub(r'[^\n]', ' ', src[i:j])); i = j; continue
        if c == "'":
            m = re.match(r"'(\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'])'", src[i:i+16])
            if m:
                out.append(' ' * m.end()); i += m.end(); continue
        out.append(c); i += 1
    return ''.join(out)

TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_]*|#!?\[|::|[{}()\[\];,.<>=!&|+*/%^-]|'[A-Za-z_]+|\S")

def tokens(s):
    line = 1; pos = 0
    for m in TOK.finditer(s):
        line += s.count('\n', pos, m.start()); pos = m.start()
        yield m.group(0), line, m.start()

def parse(path):
    raw = open(path, encoding='utf-8').read()
    s = strip(raw)
    toks = list(tokens(s))
    fns = []
    # scope stack: entries (kind, name, test, close_depth[, is a trait impl])
    stack = []
    depth = 0
    pending_attr = []   # attribute texts seen before the next item
    i = 0
    while i < len(toks):
        t, line, off = toks[i]
        if t in ('#[', '#!['):
            # read the attribute to its matching ]
            d = 1; j = i + 1; parts = []
            while j < len(toks) and d:
                if toks[j][0] in ('[', '#[', '#!['): d += 1
                elif toks[j][0] == ']': d -= 1
                if d: parts.append(toks[j][0])
                j += 1
            a = ' '.join(parts)
            if t == '#[':
                pending_attr.append(a)
            i = j; continue
        intest = any(e[2] for e in stack)
        if t == 'mod' and i + 2 < len(toks) and toks[i+2][0] == '{':
            istest = any(re.search(r'\bcfg\s*\(\s*test\s*\)', a) for a in pending_attr)
            stack.append(('mod', toks[i+1][0], istest or intest, depth))
            depth += 1; pending_attr = []; i += 3; continue
        if t == 'impl':
            # find the `{` that opens the impl body
            j = i + 1; angle = 0; head = []
            while j < len(toks) and not (toks[j][0] == '{' and angle == 0):
                if toks[j][0] == '<': angle += 1
                elif toks[j][0] == '>': angle -= 1
                head.append(toks[j][0]); j += 1
            # the type: after `for` if present, else the head; last identifier before generics
            htxt = ' '.join(head)
            if ' for ' in ' ' + htxt + ' ':
                ty_part = htxt.split(' for ', 1)[1] if ' for ' in htxt else htxt
            else:
                ty_part = htxt
            ty_part = re.sub(r'\bwhere\b.*', '', ty_part)
            # strip leading generic params of impl<...>
            ty_part = re.sub(r'^<[^{]*?>\s', '', ty_part.strip()) if ty_part.strip().startswith('<') and ' for ' not in htxt else ty_part
            ids = re.findall(r"[A-Za-z_][A-Za-z0-9_]*", re.sub(r'<.*', '', ty_part.replace(' :: ', '::').replace(' ', '')))
            ty = ids[-1] if ids else '?'
            istest = any(re.search(r'\bcfg\s*\(\s*test\s*\)', a) for a in pending_attr)
            stack.append(('impl', ty, istest or intest, depth, (' for ' in ' '+htxt+' ')))
            depth += 1; pending_attr = []; i = j + 1; continue
        if t == 'trait' and i + 1 < len(toks):
            j = i + 1
            while j < len(toks) and toks[j][0] not in ('{', ';'):
                j += 1
            if j < len(toks) and toks[j][0] == '{':
                istest = any(re.search(r'\bcfg\s*\(\s*test\s*\)', a) for a in pending_attr)
                stack.append(('trait', toks[i+1][0], istest or intest, depth))
                depth += 1; pending_attr = []; i = j + 1; continue
        if t == 'fn' and i + 1 < len(toks) and re.match(r'[A-Za-z_]', toks[i+1][0]):
            name = toks[i+1][0]
            istest = intest or any(re.search(r'\bcfg\s*\(\s*test\s*\)|^test$', a) for a in pending_attr)
            # find body `{` or `;` at paren/angle depth 0
            j = i + 2; par = 0
            while j < len(toks):
                x = toks[j][0]
                if x in ('(', '['): par += 1
                elif x in (')', ']'): par -= 1
                elif x == '{' and par == 0: break
                elif x == ';' and par == 0: break
                j += 1
            if j < len(toks) and toks[j][0] == '{':
                # body: brace-match
                d = 1; k = j + 1
                while k < len(toks) and d:
                    if toks[k][0] == '{': d += 1
                    elif toks[k][0] == '}': d -= 1
                    k += 1
                body = toks[j:k]
                refs = sorted({b[0] for b in body if re.match(r'[A-Za-z_][A-Za-z0-9_]*$', b[0])})
                encl = [e for e in stack if e[0] in ('impl', 'trait')]
                qual = encl[-1][1] if encl else None
                timpl = bool(encl) and (encl[-1][0] == 'trait' or (len(encl[-1]) > 4 and encl[-1][4]))
                fns.append({'file': path, 'line': line, 'end': toks[k-1][1], 'name': name, 'qual': qual,
                            'test': bool(istest), 'refs': refs, 'timpl': timpl,
                            'mod': [e[1] for e in stack if e[0] == 'mod']})
                # nested fns inside are parsed as part of the body only; skip body
                pending_attr = []; i = k; continue
            pending_attr = []; i = j + 1; continue
        if t == '{':
            depth += 1
        elif t == '}':
            depth -= 1
            while stack and stack[-1][3] == depth:
                stack.pop()
        elif t == ';':
            pending_attr = []
        i += 1
    return fns

def main():
    out = []
    for root in sys.argv[1:]:
        for dp, dn, fn in os.walk(root):
            dn[:] = [d for d in dn if d not in ('target', '.git', 'snapshots')]
            for f in fn:
                if f.endswith('.rs'):
                    out.extend(parse(os.path.join(dp, f)))
    json.dump({'fns': out}, sys.stdout)

if __name__ == '__main__':
    main()
