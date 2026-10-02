"""The exemption ratchets' second comparand: the file's COMMITTED HISTORY.

**THE FINDING** (W-41's verifier; the W-41 repair, README gap 4132).  Every
exemption file under `kernel/` "may only SHRINK" (the owner's D51, strict since
the campaign's D81 call on README gap 3953), and every gate that reads one held
it against the file at HEAD -- `reach.committed_exemptions`, and its copies in
`fields.py`, `twins.py` and `totality.py`.  HEAD is the right comparand for a
working copy and the wrong one for a commit: once the growth is COMMITTED, HEAD
holds it, and the next run compares the file with itself.  Driven by the
verifier in a clone: a `def` no export reaches, added to `reach-exempt.txt` and
committed on a throwaway branch, gave `reach.py` rc=0 and `EXEMPT 1200` (was
1199) -- so an auditor, or the next `check.sh` on the committed tree, could not
see the growth the working-copy run refused.

**THE RULE THIS ADDS.**  Since `BASE` -- `17a13c2` (`122e153` before D88), the commit W-41's four
tracks branched from, before the strict rule took effect -- every commit on HEAD's FIRST-PARENT line that
changed the file is held against its own first parent by the gate's own key
reader: a key the commit's file holds and its parent's did not is growth, and
FAILS, naming the commit.  First-parent, so a track merged in is judged by the
merge (the net change it brought to the line); every commit, so it does not
matter whether the growth arrived in the commit that changed the gate or in a
later one.  A commit whose growth the owner grants is the owner's to grant by
moving `BASE` past it, in the commit that does -- a line in a diff, as a
heading never was.

**WHAT IT CANNOT SEE, declared.**  A step BEFORE `BASE`, when growth under a
dated section was the rule (W-31 to W-40).  A track's own commit off the line
(it is judged by the merge that brings it, the net change).  A history git
cannot read (a `git archive` copy, a shallow clone without `BASE`) answers
`None`, and every gate then FAILS as UNCHECKED rather than passing on nothing,
exactly as its HEAD comparand already did.
"""

import subprocess

#: `17a13c2`, the commit every W-41 track branched from: the strict rule (D81, gap
#: 3953) took effect inside W-41, so the walk covers the whole of it.  It was
#: `122e153` until the owner's D88 rewrote W-40's and W-41's lands into single
#: measured commits (2026-10-02): `17a13c2` is that commit with its tree
#: byte-identical, at the same place on the first-parent line, so the walk is the
#: one it was -- the base is RE-POINTED, not moved past anything.
BASE = "17a13c234547a409a352d1ac15d2d62d2110f01c"


def _git(path, *args):
    try:
        out = subprocess.run(["git", "-C", str(path.parent)] + list(args),
                             capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError):
        return None
    return out.stdout if out.returncode == 0 else None


def show(path, rev):
    """`path`'s text at `rev`: `""` when the file is not in that commit, `None`
    when git cannot say."""
    listed = _git(path, "ls-tree", rev, "--", path.name)
    if listed is None:
        return None
    if not listed.strip():
        return ""
    return _git(path, "show", "%s:./%s" % (rev, path.name))


def history(path):
    """`[(sha, parent_text, text)]` for every commit after `BASE` on HEAD's
    first-parent line whose `path` differs from its first parent's, oldest
    first; `None` when git cannot say (no repository, or `BASE` is not an
    ancestor of HEAD)."""
    if _git(path, "merge-base", "--is-ancestor", BASE, "HEAD") is None:
        return None
    revs = _git(path, "rev-list", "--first-parent", "--reverse", "%s..HEAD" % BASE)
    if revs is None:
        return None
    out = []
    for sha in revs.split():
        cur = show(path, sha)
        prev = show(path, sha + "^1")
        if cur is None or prev is None:
            return None
        if cur != prev:
            out.append((sha, prev, cur))
    return out


def grown(path, keys, allowed=None):
    """The complaints for every key a committed step ADDED: `keys(text)` is the
    gate's own reader of the file's entries as a set; `allowed(sha, key, prev)`,
    when given, answers a key the gate's rule lets a commit add (a field the
    structure did not have, a key under one already exempt).  `None` when git
    cannot say -- the caller fails as UNCHECKED."""
    steps = history(path)
    if steps is None:
        return None
    out = []
    for sha, prev, cur in steps:
        held = keys(prev)
        for key in sorted(keys(cur) - held, key=str):
            if allowed is not None and allowed(sha, key, held):
                continue
            out.append("RATCHET (committed): %s grew at %s -- `%s` is held by no entry of its "
                       "first parent, and this file may only SHRINK (D51; README gap 4132: "
                       "growth that reached a commit is growth HEAD can no longer see)"
                       % (path.name, sha[:9], key))
    return out
