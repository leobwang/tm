#!/usr/bin/env python3
"""check.sh's check 9 (D40): every definition a step ADDS is CONSTANT-FOLDED.

Three times in this campaign a definition shipped whose body nothing could tell
from a constant, and all three were found by a human reading code, never by a
gate:

  * W-17's P4 sort key -- the two halves swapped, 1,342 tests green.
  * W-18's nine candidate facts -- invert one, the whole suite green, and
    `tm plan` visibly re-ranks.
  * W-19's `Planner.Ranked.gatherable` -- `:= true`, and 168 build targets,
    every theorem in `Planner.lean`, all nineteen `PlannerWit` `decide`
    witnesses and check.sh 8/8 stay green.

That is README gap 577's class, and D40 is the gate that ends it: replace a
definition's body with a CONSTANT OF ITS TYPE, one constant at a time, and
something must FAIL.  If nothing fails, no theorem, witness or test in the
package distinguishes the definition from that constant, and the definition is
unwitnessed no matter how carefully it is written.

WHAT IS MUTATED.  Every `def` and `abbrev` in kernel/TmKernel/TmKernel/*.lean --
the library -- that is NEW OR CHANGED since the baseline commit named on the
first line of `mutations.txt`.  Scoped that way because D40 scoped it that way:
a full sweep of the existing kernel was DECLINED as producing a backlog rather
than preventing new instances, and the moment a definition is introduced is when
its distinguishing witness is cheapest to write.  "Changed" is by the sha1 of
the body text, so a step that rewrites an existing body owes a mutation for it
too, and a step that only re-indents one does not.

THE CONSTANTS, by the declared return type -- the text between the last
depth-zero `:` of the header and the `:=` that opens the body:

    Bool          true   and   false      (AGENTS 5.8: both directions)
    Prop          True   and   False
    Nat           0      and   1
    anything else default

`default` is a constant of ANY inhabited type, arrow types included -- for
`def f (a : A) : B -> C`, `:= default` is the constant function -- so the table
needs no per-type knowledge and does not go stale as the kernel grows types.

HOW A MUTATION IS APPLIED, and why the line numbers do not move.  The body's
characters, from just after the header's `:=` to the end of the declaration
(`termination_by` and `decreasing_by` included), are replaced by the constant
followed by exactly as many newlines as were removed.  The file keeps its line
count and every other declaration keeps its line number, so an error's location
is comparable against the mutated declaration's own line range.

THE FOUR VERDICTS, and the reason each of the last two exists:

    PINNED      the build FAILED, and no error is inside the mutated
                declaration.  Something in the package can tell this definition
                from that constant.  This is the verdict a definition must earn.
    SURVIVED    the build SUCCEEDED.  Nothing distinguishes it.  check 9 FAILS.
    INVALID     the build failed WITH an error inside the mutated declaration
                that is NOT the one below.  check 9 FAILS, because a build that
                fails for the wrong reason is exactly the false PINNED this gate
                would otherwise hand out for free.
    UNFOLDABLE  the build failed inside the mutated declaration with exactly
                `failed to synthesize ... Inhabited T`: the type has NO constant
                to fold to, so D40's mutation does not exist for this
                definition.  ROSTERED BY NAME with the type in the reason
                column, counted on every run, and NOT fatal.

WHY UNFOLDABLE EXISTS, AND WHY IT IS NOT A FREE PASS.  This verdict was added at
the W-20 LAND step, where check 9 met its first real step output -- 46 new or
changed definitions from tracks P and G -- and reported **23 PINNED, 23 INVALID,
0 SURVIVED**.  Every one of the 23 INVALID was the same error, and none was a
defect in the definition: `Look.Slot`, `Planner.Placed`, `Planner.Assign`'s
products, `Planner.Diagnostics`, `Planner.PlanReq`, `Capped _` and `WfPlan` have
no `Inhabited` instance, and `deriving instance Inhabited` was tried and Lean
answered "failed to generate" for four of the five.  THAT IS AGENTS 5.1 WORKING:
the kernel's types are `Bool` + `Subtype`, and a bounded type deliberately has no
inhabitant anybody can name without a proof.  Adding those instances to make the
gate green would hand out bounded values without their smart constructors, which
is a weakening of the kernel to suit a checker.

So the fold is UNREPRESENTABLE for such a definition, and this file says so by
name rather than by pattern.  THE SHAPE IS CHECK 8'S ALLOW-LIST, deliberately:
exact names, never a class; the reason recorded per name; the count printed on
every run so it cannot grow unnoticed.  **It narrows D40's letter** -- "the step
must show something FAILING for each" -- for the definitions in question, and the
W-20 land block puts that to the owner as a decision to confirm or reverse
(README gap 980).  Reversing it is one line: delete the UNFOLDABLE branch in
`mutate_one` and the gate fails again on all 23.

THE ROSTER.  `mutations.txt` holds the baseline commit and one row per audited
definition: the body's sha1, the file, the name, the constants tried, and the
first error the build reported for each.  check.sh's check 9 RUNS the mutation
for any new-or-changed definition with no matching row, and TRUSTS a row whose
sha1 matches -- otherwise every run of check.sh would re-build the kernel once
per audited definition forever, and the steady-state cost has to be ~0.

WHAT THIS CANNOT SEE.  Measured or argued, never guessed:
  * AN UNFOLDABLE DEFINITION IS NOT AUDITED AT ALL.  It is named and counted,
    and that is the whole of what it gets: nothing here says any theorem reads
    it.  At the W-20 land step that is HALF of what the step added -- 23 of 46.
  * A ROW IS A CLAIM.  check 9 does not re-run a mutation whose sha1 matches, so
    a row written by hand, with a plausible error string, passes.  What makes it
    not a bare claim: `mutate.py --write` appends a row only after watching the
    build fail, the row names the definition and the constants, and it lands in
    a diff.  `mutate.py --verify` re-runs every row and is what an auditor or a
    repair step uses; it is not in check.sh because it costs one kernel build
    per row.
  * ONLY `def` and `abbrev`, and only in the library.  `theorem` has no body to
    fold (its "constant" is a different proof of the same statement, which is
    not this defect class); `structure`, `inductive` and `instance` are not
    mutated; `Check.lean`, `Negative.lean` and `Goals.lean` are outside the
    scope, and so is every line of Rust -- a constant-folded `fn` in
    `tm-core/src/planner.rs` is invisible to this (README gap 936).
  * A CONSTANT IS NOT AN INVERSION.  `gatherable := true` is caught here;
    `gatherable` with two of its five clauses swapped is NOT -- the body is
    still not a constant.  D40 buys the constant-fold class, which is the one
    that has actually shipped three times, and no more (README gap 937).
  * TWO CONSTANTS, NOT ALL.  A `Nat`-valued definition that every witness pins
    at 7 survives neither `0` nor `1`, but one that nothing reads except through
    `if n > 0` is pinned by `0` and says nothing about the rest of its range.
  * THE EXTENT RULE IS TEXTUAL.  A declaration runs to the next line that starts
    at column zero with a declaration keyword, an attribute, a comment opener,
    `namespace`/`section`/`end`/`open`/`set_option`/`mutual` or `#`.  A
    definition laid out some other way is reported UNPARSED and fails the gate
    rather than being skipped silently.
  * A KILLED RUN.  The mutation is restored in a `finally`, which covers an
    exception but not a SIGKILL, so the original bytes go to a `.mutate-in-flight`
    sidecar first and every run begins by putting back whatever it finds.  A
    machine that loses power between the two writes still leaves a mutated file,
    and `git status` is what catches that.
  * IT PROVES A WITNESS EXISTS, NOT THAT IT IS THE RIGHT ONE.  A definition
    whose only distinguishing witness is a `#print axioms` line, or a
    `Negative.lean` cheat, is PINNED by this gate and may still be under-stated.
"""

import collections
import hashlib
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
PKG = os.path.join(HERE, "TmKernel")
LIB = os.path.join(PKG, "TmKernel")
ROSTER = os.path.join(HERE, "mutations.txt")
LAKE = os.path.expanduser("~/.elan/bin/lake")

DECL_KW = ("theorem", "lemma", "def", "abbrev", "structure", "inductive",
           "instance", "class", "example", "opaque", "axiom", "namespace",
           "section", "end", "open", "set_option", "mutual", "deriving",
           "attribute", "macro", "notation", "syntax", "@[", "/--", "/-!",
           "/-", "--", "#", "private", "protected", "noncomputable",
           "partial", "unsafe", "scoped", "local", "variable", "universe",
           "import", "where", "termination_by", "decreasing_by")

BODY_KW = ("termination_by", "decreasing_by")

HEAD = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)[ \t]+)*"
    r"(def|abbrev)[ \t]+([^\s(){}\[\],:]+)")

CONSTANTS = {"Bool": ["true", "false"], "Prop": ["True", "False"],
             "Nat": ["0", "1"]}


def read(path):
    with open(path, encoding="utf-8") as handle:
        return handle.read()


def lib_files():
    """The library's .lean files, as relative paths under kernel/."""
    return sorted("TmKernel/TmKernel/" + n for n in os.listdir(LIB)
                  if n.endswith(".lean"))


def starts_declaration(line):
    if not line or line[0] in (" ", "\t"):
        return False
    head = line.split("(")[0]
    return any(line.startswith(k) for k in DECL_KW) or head.strip() in DECL_KW


def split_header(text, start):
    """Offsets of the header's `:=` and of the return type, from `start`.

    Returns (body_at, type_text) with body_at the offset just past the
    depth-zero `:=`, or (None, None) if the declaration has no such `:=`
    (equation-style `| a => ...`, which this cannot fold)."""
    depth = 0
    i = start
    colon = None
    n = len(text)
    while i < n:
        c = text[i]
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
        elif text.startswith("--", i):
            i = text.find("\n", i)
            if i < 0:
                return None, None
        elif text.startswith("/-", i):
            j = text.find("-/", i)
            if j < 0:
                return None, None
            i = j + 1
        elif c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            depth -= 1
        elif depth == 0 and text.startswith(":=", i):
            kind = text[colon + 1:i].strip() if colon is not None else ""
            return i + 2, kind
        elif depth == 0 and c == ":" and not text.startswith("::", i):
            colon = i
        elif depth == 0 and c == "|" and colon is not None \
                and not text.startswith("||", i) and text[i - 1] != "|":
            # Equation style: `def f : A -> B` then `| a => …`, whether the
            # first `|` opens its own line or follows the type on the head
            # line.  The header ends at that `|`, and the constant is written
            # with its own `:=`, which the signature does not have.
            kind = text[colon + 1:i].strip() if colon is not None else ""
            return -(i), kind
        i += 1
    return None, None


def declarations(text, path):
    """Every `def`/`abbrev` in one file: name, body text, char span, type."""
    out = []
    lines = text.split("\n")
    starts = []
    for n, line in enumerate(lines):
        m = HEAD.match(line)
        if m:
            starts.append((n, m.group(2)))
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line) + 1)
    for n, name in starts:
        end = len(lines)
        for j in range(n + 1, len(lines)):
            line = lines[j]
            if starts_declaration(line) and not line.startswith(BODY_KW):
                end = j
                break
        head_at = offsets[n]
        stop = offsets[end] - 1 if end < len(lines) else len(text)
        body_at, kind = split_header(text, head_at)
        lead = ""
        if body_at is not None and body_at < 0:
            body_at, lead = -body_at, ":= "
        if body_at is None or body_at > stop:
            out.append({"name": name, "file": path, "line": n + 1,
                        "last": end, "body": None, "type": None,
                        "at": None, "stop": stop, "lead": ""})
            continue
        out.append({"name": name, "file": path, "line": n + 1, "last": end,
                    "body": text[body_at:stop], "type": kind.strip(),
                    "at": body_at, "stop": stop, "lead": lead})
    return out


def digest(body):
    return hashlib.sha1(" ".join(body.split()).encode("utf-8")).hexdigest()[:12]


def roster():
    """(baseline sha, {(file, name): row}) from mutations.txt."""
    base, rows = None, {}
    if not os.path.exists(ROSTER):
        return None, {}
    for line in read(ROSTER).split("\n"):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        parts = line.split(None, 1)
        if parts[0] == "baseline":
            base = parts[1].strip()
            continue
        fields = line.split(None, 4)
        if len(fields) < 4:
            print("mutate.py: bad roster line: %s" % line)
            return None, None
        sha, path, name, consts = fields[0], fields[1], fields[2], fields[3]
        rows[(path, name)] = {"sha": sha, "consts": consts,
                              "why": fields[4] if len(fields) > 4 else ""}
    return base, rows


def at_commit(sha, path):
    got = subprocess.run(["git", "show", "%s:kernel/%s" % (sha, path)],
                         cwd=ROOT, capture_output=True, text=True)
    return got.stdout if got.returncode == 0 else None


def touched(base):
    """Library files whose BYTES differ from `base` -- git, one call.

    A file identical to the baseline cannot hold a new or changed definition,
    and at a settled tree that is all of them, which is what keeps check 9 at
    ~0.05 s instead of one `git show` per module."""
    got = subprocess.run(
        ["git", "diff", "--name-only", base, "--", "kernel/TmKernel/TmKernel"],
        cwd=ROOT, capture_output=True, text=True)
    if got.returncode != 0:
        raise SystemExit("mutate.py: git diff against %s failed: %s"
                         % (base, got.stderr.strip()))
    return {line[len("kernel/"):] for line in got.stdout.split("\n") if line}


def new_or_changed(base):
    """Library defs that do not exist at `base`, or whose body differs there."""
    out = []
    moved = touched(base)
    for path in lib_files():
        if path not in moved:
            continue
        now = read(os.path.join(HERE, path))
        was = at_commit(base, path)
        # A multiset, not a dict: one file may declare the same SHORT name in
        # two namespaces (`Replay.HMap.get` and `Replay.KMap.get` are both
        # spelled `get`), and keying by name alone reported four such pairs as
        # changed when nothing had changed.
        old = collections.Counter()
        if was is not None:
            for d in declarations(was, path):
                if d["body"] is not None:
                    old[(d["name"], digest(d["body"]))] += 1
        for d in declarations(now, path):
            d["sha"] = digest(d["body"]) if d["body"] is not None else None
            if d["sha"] is not None and old[(d["name"], d["sha"])] > 0:
                old[(d["name"], d["sha"])] -= 1
                continue
            out.append(d)
    return out


def build():
    got = subprocess.run([LAKE, "build", "TmKernel:static"], cwd=PKG,
                         capture_output=True, text=True,
                         env=dict(os.environ, LEAN_NUM_THREADS="4"))
    return got.returncode, (got.stdout or "") + (got.stderr or "")


# lake v4.33.1 prints `error: TmKernel/PlannerWit.lean:3167:26: Type mismatch`
# -- the word `error` comes FIRST, before the location.  A regex written the
# other way round (location, then `error`) matches NOTHING, which is how the
# first version of this file reported every failing build as PINNED with "no
# located error" and could never have raised INVALID at all.  Both orders are
# accepted so that a `lean` invocation's own format works too.
ERR = re.compile(r"^(?:error: )?(?:\./)?(\S+\.lean):(\d+):\d+:(?: error)?", re.M)

# The one error that is NOT the definition's fault and NOT a free PINNED: the
# constant `default` does not exist, because the return type has no `Inhabited`
# instance.  AGENTS 5.1 is why -- the kernel's types are `Bool` + `Subtype`, and
# a bounded type has NO inhabitant you can name without a proof, deliberately.
# `deriving instance Inhabited` does not rescue it either: it was tried at the
# W-20 land step on `Look.Slot`, `Planner.Placed`, `Planner.Diagnostics` and
# `Planner.PlanReq` and Lean answered "failed to generate `Inhabited` instance"
# for all four.  See UNFOLDABLE in the verdict table above.
INHAB = re.compile(r"failed to synthesize[^\n]*\n\s*Inhabited ([^\n]+)")


SIDECAR = os.path.join(HERE, ".mutate-in-flight")


def restore_in_flight():
    """Put back a file a KILLED run left mutated.

    `mutate_one` restores in a `finally`, which covers an exception but not a
    SIGKILL -- and a mutated library file left in the tree is the one outcome
    this gate must never produce, because it is a constant-folded kernel that
    looks like a commit.  So the original bytes go to a sidecar BEFORE the file
    is written, and every run starts by putting back whatever it finds."""
    if not os.path.exists(SIDECAR):
        return
    with open(SIDECAR, encoding="utf-8") as handle:
        rel, text = handle.read().split("\n", 1)
    with open(os.path.join(HERE, rel), "w", encoding="utf-8") as handle:
        handle.write(text)
    os.remove(SIDECAR)
    print("mutate.py: restored %s from a killed run" % rel, flush=True)


def mutate_one(decl, const):
    """Apply one constant, build, restore.  -> (verdict, first error line)."""
    full = os.path.join(HERE, decl["file"])
    text = read(full)
    span = text[decl["at"]:decl["stop"]]
    new = " " + decl.get("lead", "") + const + "\n" * span.count("\n")
    with open(SIDECAR, "w", encoding="utf-8") as handle:
        handle.write(decl["file"] + "\n" + text)
    with open(full, "w", encoding="utf-8") as handle:
        handle.write(text[:decl["at"]] + new + text[decl["stop"]:])
    try:
        code, out = build()
    finally:
        with open(full, "w", encoding="utf-8") as handle:
            handle.write(text)
        os.remove(SIDECAR)
    if code == 0:
        return "SURVIVED", "build completed"
    first = None
    hits = list(ERR.finditer(out))
    for idx, m in enumerate(hits):
        where, line = m.group(1), int(m.group(2))
        if first is None:
            first = "%s:%d" % (os.path.basename(where), line)
        if os.path.basename(where) == os.path.basename(decl["file"]) \
           and decl["line"] <= line <= decl["last"]:
            stop = hits[idx + 1].start() if idx + 1 < len(hits) else len(out)
            want = INHAB.search(out[m.end():stop])
            if want:
                return "UNFOLDABLE", "no Inhabited %s" % want.group(1).strip()
            return "INVALID", "%s:%d is inside the declaration" % (
                os.path.basename(where), line)
    return "PINNED", first or "build failed with no located error"


def constants_for(decl):
    return CONSTANTS.get((decl["type"] or "").strip(), ["default"])


def run(decls, write, verbose=True):
    """Mutate each declaration with each of its constants.

    -> (bad, soft).  `bad` fails the gate; `soft` is the UNFOLDABLE roster --
    named, counted and printed on every run, never silent."""
    rows, bad, soft = [], [], []
    for decl in decls:
        tag = "%s:%s" % (decl["file"], decl["name"])
        if decl["body"] is None:
            bad.append((tag, "UNPARSED", "no depth-zero `:=` (equation-style?)"))
            if verbose:
                print("  %-58s UNPARSED" % tag, flush=True)
            continue
        verdicts = []
        for const in constants_for(decl):
            if verbose:
                # BEFORE the build, flushed: one mutation is a whole kernel
                # build, and a gate with no progress output looks like a hang.
                print("  %-58s %-9s building…" % (tag, ":= " + const),
                      end="\r", flush=True)
            verdict, why = mutate_one(decl, const)
            if verbose:
                print("  %-58s %-9s %-8s %-38s" % (tag, ":= " + const, verdict, why),
                      flush=True)
            verdicts.append((const, verdict, why))
            if verdict == "UNFOLDABLE":
                soft.append((tag, verdict, ":= %s -- %s" % (const, why)))
            elif verdict != "PINNED":
                bad.append((tag, verdict, ":= %s -- %s" % (const, why)))
        if all(v in ("PINNED", "UNFOLDABLE") for _, v, _ in verdicts):
            rows.append("%s %s %s %s %s" % (
                decl["sha"], decl["file"], decl["name"],
                ",".join(c if v == "PINNED" else "unfoldable"
                         for c, v, _ in verdicts),
                "; ".join(w for _, _, w in verdicts)))
    if write and rows:
        with open(ROSTER, "a", encoding="utf-8") as handle:
            handle.write("\n".join(rows) + "\n")
        print("%d row(s) appended to mutations.txt" % len(rows))
    return bad, soft


FLAGS = ("--gate", "--write", "--verify", "--only", "--since")


def main(argv):
    # An unrecognised flag is REFUSED, not ignored.  A typo used to fall through
    # to the default path, which mutates every new definition -- one kernel
    # build per constant, minutes of it, for a misspelling.
    known = set(FLAGS)
    skip = False
    for i, arg in enumerate(argv):
        if skip:
            skip = False
            continue
        if arg not in known:
            print("mutate.py: unknown argument %r; flags are %s"
                  % (arg, " ".join(FLAGS)))
            return 2
        skip = arg in ("--only", "--since")
    restore_in_flight()
    base, rows = roster()
    if rows is None:
        return 2
    if base is None:
        print("mutate.py: mutations.txt has no `baseline <sha>` line")
        return 2
    gate = "--gate" in argv
    write = "--write" in argv
    verify = "--verify" in argv
    only = None
    if "--only" in argv:
        only = argv[argv.index("--only") + 1]
    if "--since" in argv:
        base = argv[argv.index("--since") + 1]

    if verify:
        decls = [d for path in lib_files()
                 for d in declarations(read(os.path.join(HERE, path)), path)
                 if (d["file"], d["name"]) in rows]
        for d in decls:
            d["sha"] = digest(d["body"]) if d["body"] is not None else None
        print("re-running %d rostered mutation(s)" % len(decls))
        bad, soft = run(decls, False)
        print("%d rostered definition(s) failed re-verification, "
              "%d unfoldable" % (len(bad), len(soft)))
        return 1 if bad else 0

    decls = new_or_changed(base)
    if only:
        decls = [d for d in decls if d["name"] == only
                 or "%s:%s" % (d["file"], d["name"]) == only]
        if not decls:
            for path in lib_files():
                for d in declarations(read(os.path.join(HERE, path)), path):
                    if d["name"] == only:
                        d["sha"] = digest(d["body"]) if d["body"] else None
                        decls.append(d)
    rostered = [d for d in decls
                if rows.get((d["file"], d["name"]), {}).get("sha") == d["sha"]]
    owed = [d for d in decls if d not in rostered]

    # The UNFOLDABLE count is printed on EVERY run, owed or not: a definition the
    # fold cannot reach is an exemption, and check 8's allow-list is the precedent
    # -- an exemption nobody counts is how a gate goes quietly useless.
    unfold = sum(1 for d in decls
                 if "unfoldable" in rows.get((d["file"], d["name"]),
                                             {}).get("consts", ""))
    if gate:
        if not owed:
            print("%d new or changed since %s, %d rostered (%d unfoldable), 0 owed"
                  % (len(decls), base[:7], len(rostered), unfold))
            return 0
        print("%d new or changed since %s, %d rostered, %d OWED A MUTATION"
              % (len(decls), base[:7], len(rostered), len(owed)))
    bad, soft = run(owed, write)
    if soft:
        print("%d definition(s) UNFOLDABLE -- no constant of the type exists:"
              % len(soft))
        for tag, verdict, why in soft:
            print("  %-58s %-11s %s" % (tag, verdict, why))
    if bad:
        print("%d definition(s) not pinned by a constant:" % len(bad))
        for tag, verdict, why in bad:
            print("  %-58s %-9s %s" % (tag, verdict, why))
        return 1
    if owed:
        print("%d definition(s) audited (%d pinned, %d unfoldable)"
              % (len(owed), len(owed) - len(soft), len(soft)))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
