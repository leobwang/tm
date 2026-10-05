#!/usr/bin/env python3
"""Delete named fns (with their doc comments and attributes) from Rust sources --
the deletion R3 makes, as `simulate.py` drives it (stage 6 W-46 track C).

usage: delete_fns.py LIST ROOT
LIST lines: a file relative to ROOT, then a function -- `name`, the name qualified by
its type with two colons, or `test:name`; '#' starts a comment.  The first two match
non-test fns; `test:name` a `#[test]` fn
or a `#[cfg(test)]` one, else any fn of that name (a helper of an integration
test file).  Each is located by rsgraph.py's parser, its span widened upward
over the contiguous `///` doc and `#[..]` attribute lines above it.  Prints
`file start end lines name` for each deletion and the total; FAILS when a name
is not found exactly once, so a list that drifted from the tree is loud."""
import sys, os, json, importlib.util
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('rsgraph', os.path.join(here, 'rsgraph.py'))
rg = importlib.util.module_from_spec(spec); spec.loader.exec_module(rg)
lst, root = sys.argv[1], sys.argv[2]
want = []
for l in open(lst):
    l = l.split('#', 1)[0].strip()
    if l:
        f, q = l.split()
        want.append((f, q))  # q: a name, Type and name with two colons, or test:name for a test fn (or a test file's helper)
byfile = {}
for f, q in want:
    byfile.setdefault(f, []).append(q)
total = 0
for f, qs in byfile.items():
    path = os.path.join(root, f)
    allfns = rg.parse(path)
    lines = open(path, encoding='utf-8').read().split('\n')
    spans = []
    for q in qs:
        if q.startswith('test:'):
            name, qual = q[5:], None
            hits = [x for x in allfns if x['name'] == name and x['test']]
            if not hits:  # a helper or test in an integration-test file: rsgraph marks only cfg(test) code as test
                hits = [x for x in allfns if x['name'] == name]
        else:
            qual, name = (q.split('::') if '::' in q else (None, q))
            hits = [x for x in allfns if not x['test'] and x['name'] == name and (qual is None or x['qual'] == qual)]
        if len(hits) != 1:
            sys.exit(f"{f}: {q}: found {len(hits)} non-test definitions")
        x = hits[0]
        s, e = x['line'] - 1, x['end'] - 1      # 0-based inclusive
        # the fn keyword line may be preceded by `pub` on the same line; widen up over docs/attrs
        while s > 0 and (lines[s-1].lstrip().startswith('///') or lines[s-1].lstrip().startswith('#[')):
            s -= 1
        spans.append((s, e, q))
    spans.sort()
    for a, b in zip(spans, spans[1:]):
        if b[0] <= a[1]:
            sys.exit(f"{f}: overlapping spans {a} {b}")
    for s, e, q in reversed(spans):
        n = e - s + 1
        total += n
        print(f"{f} {s+1} {e+1} {n} {q}")
        # also drop one blank line after, if the line before is blank too
        del lines[s:e+1]
        if s < len(lines) and s > 0 and lines[s].strip() == '' and lines[s-1].strip() == '':
            del lines[s]
    open(path, 'w', encoding='utf-8').write('\n'.join(lines))
print(f"TOTAL {total} lines")
