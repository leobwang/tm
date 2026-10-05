#!/usr/bin/env python3
"""Reachability over rsgraph.py's JSON, by name (stage 6 W-46 track C): roots are
every non-test fn of the binary crate (tm/src) and every trait-impl method
(dispatch the by-name graph cannot see); an edge f -> g when g's NAME is an
identifier in f's body.  Prints the tm-core non-test fns NOT reached, as
`file:line Type::name`.  Over-approximates reach (a name collision is an edge),
so what it prints is a SUBSET of what `class.sh`'s symbol table finds.

    python3 rsgraph.py <tree>/tm-core/src <tree>/tm/src > g.json
    python3 reach_grep.py g.json"""
import json, sys, collections
g = json.load(open(sys.argv[1]))['fns']
core = lambda f: '/tm-core/src/' in f['file']
nontest = [f for f in g if not f['test']]
byname = collections.defaultdict(list)
for i, f in enumerate(nontest):
    byname[f['name']].append(i)
roots = [i for i, f in enumerate(nontest) if (not core(f)) or f.get('timpl')]
seen = set(roots); stack = list(roots)
while stack:
    i = stack.pop()
    for r in nontest[i]['refs']:
        for j in byname.get(r, ()):
            if j not in seen:
                seen.add(j); stack.append(j)
for i, f in enumerate(nontest):
    if core(f) and i not in seen:
        q = (f['qual'] + '::' if f['qual'] else '') + f['name']
        print(f"{f['file'].split('/src/')[1]}:{f['line']} {q}")
