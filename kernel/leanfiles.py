#!/usr/bin/env python3
"""The kernel's .lean files: ONE enumeration, four consumers.

check.sh's checks 2, 3, 8 and 9 all have to answer the same question -- which
files ARE the kernel -- and until the W-22 repair step each of them answered it
separately.  That is AGENTS 5.3 (two definitions of one concept is the bug)
applied to a gate, and it has now cost two findings in two consecutive runs:

  * W-21: three of the four enumerated the library ONE LEVEL DEEP while check.sh
    stated the swept set as a recursion, so a module in a SUBDIRECTORY was
    invisible to checks 2, 8 and 9 at once and a partial def -- a HARD RULE --
    passed all three.  Repaired by making three of them recursive.
  * W-22: the FOURTH was never repaired, because nothing named it.  check.sh's
    check-3 roster grep was still TmKernel/*.lean, so a theorem in a
    subdirectory was never required to have a #print axioms line.  And the three
    that WERE repaired shared a hard-coded prune list holding the name "target",
    which is a legal Lean module path component: a library module under
    kernel/TmKernel/TmKernel/target/ was invisible to checks 2, 8 AND 9 again,
    through the prune list instead of through the non-recursion.  Both DRIVEN at
    the W-22 repair step; the drives are in kernel/README.md's block.

So the enumeration lives here, once, and the four consumers import it (check.sh
runs this file as a command).  A future disagreement between two checkers about
whether a file exists now needs someone to write a second walk.

WHAT IS PRUNED, and why it is a property and not a name.  A build directory is
pruned; a source directory is not.  The old rule was a name list, and a name
list cannot tell a cargo build directory called target from a Lean namespace
called Tm.Target.  The rule here is two properties, both of them things a build
directory HAS and a Lean module directory does not:

  * its name begins with a dot -- .lake and .git, and a leading dot is not a
    legal Lean module path component, so this can never hide a module;
  * it holds a CACHEDIR.TAG file -- the cache-directory marker cargo writes into
    its target directory (and which rustc, Bazel and others write too).  A
    directory holding one is declaring itself derived output.

AND SINCE W-29 IT IS ASKED OF EVERY ENTRY AND NOT ONLY OF DIRECTORIES, because
a leading dot is a property of a NAME: in a linked worktree `.git` is a FILE,
the walk returned it, and check 8 -- whose population is this walk union git
since W-28 -- failed on it in every worktree this campaign tells a track to use.
`is_derived` carries the drive.

WHAT IT CANNOT SEE.  A build directory that is neither dot-prefixed nor tagged
is walked, and a .lean file inside it is read as a source.  That direction is
the safe one -- a gate scanning too much fails loudly on a generated file rather
than falling silent on a real one -- but it is not free: a vendored toolchain
unpacked under kernel/ would be scanned as if it were this kernel.  Measured at
the W-22 repair step: 0 .lean files live under any pruned directory of this
repository today, so pruning changes nothing here and exists for a future
layout.
"""
import os
import re
import pathlib
import subprocess
import sys

# The cache-directory marker.  Its content is a fixed signature line; this
# checker tests for the file's existence only, because a directory that carries
# the name at all is claiming to be derived output.
CACHE_TAG = "CACHEDIR.TAG"


def is_derived(path):
    """Is this entry the tooling's rather than the repository's?

    **IT WAS NAMED FOR DIRECTORIES AND ASKED ONLY OF DIRECTORIES**
    (W-29, README gap 1953).  `source_files` asked it about a directory and
    never about a file, and in a LINKED WORKTREE -- the checkout every track of
    this campaign is told to work in -- `.git` is a FILE holding one `gitdir:`
    line, not a directory.  So the walk returned it, check 8's population is the
    walk union git since W-28, `git ls-files` does not list it, and no reader
    claims the extension: **check.sh was 9/10 in every worktree**, reporting
    `1 unaccounted file(s): .git  (no reader for this extension and no
    exclusion)`.  DRIVEN by running `check.sh` in `.claude/worktrees/w29-a`
    before the repair, and the walk measured at 595 files with `.git` and
    `.gitignore` in it.

    A LEADING DOT IS A PROPERTY OF A NAME, not of a directory, so the test is
    the entry's and the CACHEDIR.TAG half stays the directory's (a file cannot
    hold a marker file).  Pruning a dot-named FILE cannot lose anything the
    repository tracks: `repo_files` unions this walk with `git ls-files`, and a
    dot-named path git tracks -- `.gitignore`, `.claude/API-NOTES.md`,
    `kernel/corpus/*/.tm/state.json` -- comes back through git with its
    exclusion and its reason in the gate that excludes it."""
    return path.name.startswith(".") or (path.is_dir() and (path / CACHE_TAG).is_file())


def ignored_paths(root):
    """The paths GIT ITSELF declares derived output, relative to `root`.

    **THE PRUNE RULE WAS A PROPERTY, BUT NOT THIS REPOSITORY'S** (W-29 repair
    step, README gap 2010).  `is_derived` prunes a dot-named entry and a
    CACHEDIR.TAG directory; `kernel/.gitignore` line 3 declares `__pycache__/`
    derived output and `is_derived(pathlib.Path("kernel/__pycache__"))` is
    False, so the walk swept it.  MEASURED before the repair:
    `repo_files(".")` was **608** in the shared tree and **605** in a `git
    archive HEAD` clone, the three extra being
    `kernel/__pycache__/{citations,mutate,parity}.cpython-312.pyc` -- so
    `citations.py`'s "264 files swept, 344 excluded" and check 10's "608 files
    swept" were counts of the *checkout's* state and were not reproducible from
    the committed tree.  Neither gate broke (a `.pyc` carries no citation and no
    parity row), which is why it stayed invisible: a counts-drift, and a class
    miss.

    The property that states it is GIT'S OWN, and `repo_files` was already
    relying on half of it: `--others --exclude-standard` distinguishes
    not-yet-added from ignored.  This is the other half, asked of the walk.
    `--directory` collapses a wholly ignored directory to one entry, which is
    why `is_ignored` walks a path's ANCESTORS rather than looking it up.

    **AND IT PRUNED THE DESCENT, WHICH MADE `.gitignore` A SECOND EXCLUDED LIST
    AGAIN** (W-30 track A, README gap 2092).  That is the whole of W-28's own
    finding -- `tracked()` carries it -- reached through this function nine days
    later: `.gitignore` carries `**/target`, a bare directory NAME matching at
    any depth, and pruning the descent on it put back in front of all five gates
    exactly the name list the W-22 repair deleted.  DRIVEN in a `git
    archive HEAD` clone, three one-line plants, before the repair:

      * `kernel/w30probe.md` citing a dead name -- check 8 rc=1, NAMED;
      * `kernel/target/w30probe.md`, byte-identical -- check 8 **rc=0**;
      * `kernel/TmKernel/TmKernel/target/Probe.lean` holding `partial def`, a
        HARD RULE -- check 2 **rc=0, no output**.

    So the ignore answer no longer prunes a DIRECTORY at all.  It prunes an
    ignored FILE, and only one whose extension no gate reads (`READ_SUFFIXES`):
    a `.pyc` is derived output nothing can be stale in, and gap 2010 stays
    closed, while an ignored `.md`, `.lean` or `.rs` is SWEPT and `EXCLUDED`
    -- the adjudicated list, with a reason beside each entry -- is again the
    only thing that can exempt one.

    WHAT IT COSTS, declared: an ignored directory that is neither dot-named nor
    CACHEDIR.TAG-marked is now DESCENDED.  Measured here today that is
    `kernel/__pycache__` and nothing else (3 files); `target/` and
    `kernel/tm-kernel-ffi/target/` both carry the tag and are pruned by the
    property, so the 19 GB this machine holds under them is not walked.

    Returns a set of `root`-relative paths, directories WITHOUT their trailing
    slash.  A `git` that cannot answer returns the EMPTY set, which prunes
    nothing extra: a gate scanning too much fails loudly on a generated file
    rather than falling silent on a real one, and `repo_files` -- the caller
    that publishes counts -- hard-errors on `git` before it ever gets here."""
    r = subprocess.run(
        ["git", "ls-files", "-z", "--others", "--ignored", "--exclude-standard", "--directory"],
        cwd=str(root), capture_output=True, text=True)
    if r.returncode != 0:
        return set()
    return {q.rstrip("/") for q in r.stdout.split("\0") if q}


# THE EXTENSIONS SOME GATE READS.  An ignored file with one of these is SWEPT;
# an ignored file without one is derived output nothing can be stale in.  It
# lives here rather than in `citations.py` for this file's own reason -- two
# definitions of one concept is the bug -- and `citations.READERS` is reconciled
# against it on every run, so a reader added there without a line here fails
# loudly instead of quietly shrinking this walk.
READ_SUFFIXES = frozenset({".lean", ".rs", ".c", ".md", ".txt", ".sh", ".py", ".toml", ".patch"})


def is_ignored(rel, ignored):
    """Does `ignored` cover this `root`-relative path, or a directory above it?

    `ignored_paths` asks git with `--directory`, which COLLAPSES a wholly
    ignored directory to one entry, so a file inside one is not listed by name.
    The ancestor walk is what reads that answer correctly."""
    here = rel
    while here:
        if here in ignored:
            return True
        cut = here.rfind("/")
        if cut < 0:
            return False
        here = here[:cut]
    return False


def source_files(root, suffix, ignored=None):
    """Every `suffix` file under `root`, recursively, sorted, build dirs pruned.

    `suffix=None` means EVERY file, which is what check 10's parity sweep asks
    for: a suffix list is itself a name list, and at the W-25 repair step a
    `**Parity P41 taken**` line planted in `design/stage6/notes.txt`, in
    `notes.org`, in `mutations.txt` and in `check.sh` went GREEN through a
    three-suffix walk.  The prune rule is unchanged; the caller decodes with
    `errors="replace"`, because a whole-file walk reaches `.pyc` and `.snap`.

    THE PRUNE RULE IS TWO PROPERTIES SINCE W-29: the NAME property `is_derived`
    states, and the REPOSITORY'S OWN -- a path `git` declares ignored, which
    `ignored_paths` asks git for once per walk.  `ignored` may be passed in by a
    caller that has already asked.

    `root` is a pathlib.Path or a string; the results are pathlib.Path objects
    under it, so a caller that wants relative or absolute strings converts.
    The walk is explicit rather than a glob because pruning has to stop the
    DESCENT: a glob that filters its results still reads every file name under
    a build directory.

    THE SUFFIX IS AN ARGUMENT SINCE README GAP 1418, and that is the whole of
    the Rust side's repair: `citations.py` enumerated the Rust with a hard-coded
    list of seven directory names, which is the exact shape this file's header
    says cannot work, and `tm/examples` was not on it -- two compiled
    `--example` targets of a crate whose `src` and `tests` ARE swept, holding
    live prose, invisible to check 8.  One walk, one prune rule, both
    languages."""
    root = pathlib.Path(root)
    if ignored is None:
        ignored = ignored_paths(root)
    out = []
    stack = [root]
    while stack:
        here = stack.pop()
        try:
            entries = sorted(here.iterdir())
        except (FileNotFoundError, NotADirectoryError, PermissionError):
            continue
        for entry in entries:
            # ONE TEST FOR BOTH KINDS OF ENTRY (W-29).  It used to be asked of
            # directories only, and `.git` is a FILE in a linked worktree.
            if is_derived(entry):
                continue
            rel = str(entry.relative_to(root))
            if entry.is_dir():
                # **A DIRECTORY IS PRUNED BY THE PROPERTY AND NOT BY THE PATTERN
                # FILE** (W-30, README gap 2092).  `.gitignore` used to prune
                # the DESCENT here, which put the name `target` back in front of
                # this walk -- the exact name list the W-22 repair deleted, one
                # layer over.  The descent is now the property's alone.
                stack.append(entry)
            elif is_ignored(rel, ignored) and entry.suffix not in READ_SUFFIXES:
                continue  # derived output no gate reads: pruned, and counted by nobody
            elif suffix is None or entry.suffix == suffix:
                out.append(entry)
    return sorted(out)


def repo_files(root):
    """Every file THIS REPOSITORY holds: the WALK union what git knows.

    **ONE POPULATION, TWO GATES** (W-29, README gap 1954).  check 8 and check 10
    both have to answer "which files are this repository", and they answered it
    separately: `citations.py`'s `tracked` was this union since W-28, and
    `parity.py`'s `swept` was the WALK ALONE.  The walk prunes dot-directories,
    and eleven files this repository TRACKS live under one -- `.claude/API-
    NOTES.md` and the six `.tm/` fixture directories.  DRIVEN in a clone before
    the repair: `**Parity P41 taken**` appended to `.claude/API-NOTES.md`, a
    tracked file, left `python3 parity.py` at **rc=0** still printing
    `next free P41` -- the register handing the next block a number the tree
    already spells, which is README gap 1417's own failure reached through the
    POPULATION instead of through the idioms.  That is this file's own header
    (§5.3: two definitions of one concept is the bug) one gate over, and the
    W-21/W-22 repairs are the same shape in the other direction.

    Neither enumeration may shrink the population alone:

      * the WALK reaches a file that is not added yet, because acceptance runs
        BEFORE the commit and a new module must be swept the moment it exists;
      * `git ls-files` (tracked, plus `--others --exclude-standard` for the
        added-but-not-committed) reaches what the walk's prune property hides,
        which is every tracked path under a dot-directory.

    `git` is a DEPENDENCY of this walk and a failing `git` is a HARD ERROR --
    never a silently smaller population.  A `git archive` clone used for a plant
    therefore needs a `git init && git add -A` before either gate will run in
    it; that is the cost check 8 took at W-28 and check 10 takes now.

    Returns repository-relative paths, sorted and deduplicated."""
    root = pathlib.Path(root)
    out = []
    for args in (["ls-files", "-z"], ["ls-files", "-z", "--others", "--exclude-standard"]):
        r = subprocess.run(["git"] + args, cwd=str(root), capture_output=True, text=True)
        if r.returncode != 0:
            raise SystemExit("leanfiles.repo_files: `git %s` failed in %s -- the "
                             "file population would be silently smaller"
                             % (args[0], root))
        out += [p for p in r.stdout.split("\0") if p]
    out += [os.path.relpath(str(q), str(root)) for q in source_files(root, None)]
    return sorted(set(out))


def lean_files(root):
    """Every .lean file under `root` (`source_files`, at this kernel's suffix)."""
    return source_files(root, ".lean")


def rust_files(root):
    """Every .rs file under `root`, by the same walk and the same prune rule.

    check 8's Rust sweep was a NAME LIST -- seven directories, written out --
    and the list's own blind-spot sentence named only the two `build.rs` files
    and "a future crate".  `tm/examples` was neither, and was unswept: README
    gap 1418, the fifth enumeration disagreement of this campaign and the first
    on the Rust side.  DRIVEN at the W-24 repair step, in a scratch copy: the
    same `//! plant` prepended to tm/examples/windowbench.rs and to
    tm/examples/tzprobe.rs left check 8 GREEN with byte-identical counts, while
    the identical plant in tm/src/main.rs and in
    kernel/tm-kernel-ffi/examples/oneshot.rs was named.

    WHAT IT CANNOT SEE, and it is the same sentence as `lean_files`': a build
    directory that is neither dot-prefixed nor CACHEDIR.TAG-marked is walked and
    a .rs file inside it is read as a source.  `target/` carries the tag and
    `.claude/`'s worktrees are dot-prefixed, which is why a whole-repository
    walk is 146 files here and not the 291 a bare `find` returns."""
    return source_files(root, ".rs")


def library_files(pkg):
    """Every .lean file Lake compiles into the LIBRARY target of `pkg`.

    THE ROOT MODULE IS ONE OF THEM, and that is the whole reason this function
    exists (README gap 1314, the W-23 repair step).  A Lake library named
    `TmKernel` is `TmKernel/TmKernel/**.lean` PLUS `TmKernel/TmKernel.lean`, the
    root module beside the directory -- and four consumers sharing one walk
    still disagreed, because two of them called it on the DIRECTORY:

      * check.sh 19  totality.py TmKernel/TmKernel TmKernel   (both)
      * citations.py sweeps lean_files(kernel/TmKernel)       (the package)
      * check.sh 59  leanfiles.py TmKernel/TmKernel           (the subdir ONLY)
      * mutate.py    LIB = PKG/TmKernel                       (the subdir ONLY)

    So a `theorem` in the root module was never required to carry a `#print
    axioms` line and a `def` there was never constant-folded, while `lake`
    compiled both.  DRIVEN in a scratch copy of kernel/ with check.sh's own
    lines 58-62: `theorem w23_probe_root_theorem : True := trivial` appended to
    `TmKernel/TmKernel.lean` left `unaudited: []`; the identical theorem in
    `TmKernel/TmKernel/Emit.lean` gave `unaudited: [w23_probe_lib_theorem]`.
    Same class as the subdirectory (W-21), the roster grep (W-22) and the PRUNE
    list (W-22), one level UP instead of one level down.

    "The one enumeration all four share" was true and not sufficient: they
    shared the walk and not the ROOT.  This names the root, once."""
    pkg = pathlib.Path(pkg)
    out = lean_files(pkg / pkg.name)
    root = pkg / (pkg.name + ".lean")
    if root.is_file():
        out.append(root)
    return sorted(out)


# The R8 pin, and the sources elan unpacks beside it.  ONE resolution and TWO
# readers since W-30: `citations.py`'s source 7 (`_core_scan`, every declaration
# and namespace the core library spells) and `totality.py`'s command residue
# (`command_keywords`, every keyword Lean's own grammar declares a command by).
# It is here rather than in either of them for this file's own reason: two
# definitions of one concept is the bug, and "where the pinned toolchain's
# sources are" is one concept.
TOOLCHAIN = pathlib.Path(__file__).resolve().parent / "TmKernel" / "lean-toolchain"


def toolchain_src():
    """The `src/lean` tree of the PINNED toolchain, as a pathlib.Path.

    The pin is `kernel/TmKernel/lean-toolchain` (R8 forbids moving it) and elan
    unpacks `leanprover/lean4:v4.33.1` at
    `~/.elan/toolchains/leanprover--lean4---v4.33.1`.  A pin this cannot read,
    or a toolchain whose sources are not unpacked, is a HARD ERROR and never a
    silently empty answer: both readers here are residues, and a residue over an
    empty declaration set reports everything, while a residue over an empty
    KEYWORD set reports nothing at all.  The second is the direction that goes
    quiet, which is the failure this campaign keeps paying for."""
    pin = TOOLCHAIN.read_text(encoding="utf-8").strip()
    if ":" not in pin:
        raise SystemExit("leanfiles.toolchain_src: unreadable lean-toolchain: %s" % pin)
    channel, version = pin.split(":", 1)
    src = pathlib.Path(os.path.expanduser("~/.elan/toolchains")) / (
        channel.replace("/", "--") + "---" + version) / "src" / "lean"
    if not src.is_dir():
        raise SystemExit("leanfiles.toolchain_src: no toolchain sources under %s "
                         "-- the readers of this tree would be silently empty" % src)
    return src


# STRIPPING COMMENTS IS A SCAN, NOT TWO REGEXES (the W-27 repair step).
# It lives HERE, beside the walk, because it has TWO callers: `totality.py`'s
# ban and `check.sh`'s check-3 roster.  Both used to strip comments with their
# own regex -- or, in the roster's case, with nothing at all -- and both were
# wrong in their own direction.
#
# The old stripper was `line.split("--")[0]` per line plus a non-greedy
# `/-.*?-/` over the file, and BOTH were blind to string literals, so a `--` or
# a `/-` inside a STRING silently discarded the rest of the line (or of the
# file) before any rule ran.  DRIVEN, and both plants elaborate against the
# pinned toolchain:
#
#     def critBangB (xs : List Nat) : Nat := ("a--b").length + xs.head!   -- rc=0
#     def w27PlantM : String := "/-"  /  def w27PlantN .. := xs.head!     -- rc=0
#
# `xs.head!` alone is named.  So "every `!`-accessor" was true of the regex and
# false of the scanner feeding it -- the same shape as the name-list holes this
# campaign keeps finding, one layer lower down.
#
# `strip` walks the text once, tracking three states Lean itself distinguishes:
# a NESTING block comment (`/- /- -/ -/` is one comment, which the non-greedy
# regex also got wrong, in the over-stripping direction), a line comment, and a
# string literal.  Comment bytes become spaces and newlines stay newlines, so
# line numbers survive.  STRING BODIES become spaces too -- prose is not code --
# EXCEPT inside `{...}` interpolation, which IS code and is passed through, so
# `s!"{xs.head!}"` is still caught.  Character literals are matched with the
# same `CHAR_LIT` shape as before and passed through whole, because `'"'` is a
# char literal and there are 60-odd of them in `Boundary.lean`; blanking them
# for the `!` rule happens afterwards, as it always did.
#
# WHAT IT CANNOT SEE: a string literal nested inside an interpolation brace
# (`s!"{f "a"}"`) is scanned as code with its inner quotes intact, which can
# shift the string/code boundary for the rest of that line; and Lean's raw
# string syntax `r#"..."#` is not modelled (the library uses none -- grepped).
# Lean's character literal -- one character, or one backslash escape, between
# apostrophes.  The apostrophe matters because `'` is an identifier character in
# Lean (`h'`, `foo'`), which is why the two `'`s must be exactly two characters
# apart.  `strip_comments` needs it because `'"'` is a char literal and
# `Boundary.lean` writes sixty-odd of them; `totality.py` needs the same shape
# to blank `'!'` before its `!`-accessor rule, and imports this one.
CHAR_LIT = re.compile(r"'(?:\\.|[^'\\])'")


def strip_comments(src: str) -> str:
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        c = src[i]
        if depth:
            if src.startswith("/-", i):
                depth += 1; out.append("  "); i += 2; continue
            if src.startswith("-/", i):
                depth -= 1; out.append("  "); i += 2; continue
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if src.startswith("/-", i):
            depth = 1; out.append("  "); i += 2; continue
        if src.startswith("--", i):
            while i < n and src[i] != "\n":
                out.append(" "); i += 1
            continue
        if c == "'":
            m = CHAR_LIT.match(src, i)
            if m:
                out.append(m.group(0)); i = m.end(); continue
        if c == '"':
            out.append('"'); i += 1
            braces = 0
            while i < n:
                d = src[i]
                if d == "\\":
                    out.append("  " if braces == 0 else src[i:i + 2]); i += 2; continue
                if braces == 0:
                    if d == '"':
                        out.append('"'); i += 1; break
                    if d == "{":
                        braces = 1; out.append("{"); i += 1; continue
                    out.append("\n" if d == "\n" else " "); i += 1; continue
                if d == "{": braces += 1
                elif d == "}": braces -= 1
                out.append(d); i += 1
            continue
        out.append(c); i += 1
    return "".join(out)


# THE ROSTER IS A KEYWORD TOKEN AND NOT A LINE SHAPE (the W-28 repair step).
#
# W-27 widened this from a bash grep to a Python pattern and the widening was a
# LONGER LIST OF PREFIXES -- attributes, then `private|protected|nonrec`, then
# indentation -- each one a spelling somebody had thought of.  A list of
# spellings is the pattern this campaign has now broken eight times, and it was
# still wrong one layer up: the pattern was anchored at `^`, so it saw only a
# `theorem` whose LINE it started.  Lean's `in` combinators put a declaration
# after a term on the same line, and the library writes three of them --
# `set_option maxRecDepth 20000 in` (EmitWire.lean twice, Json.lean's
# `linter.unusedSimpArgs` once).  Each is on its own line today; written on ONE
# line, which elaborates identically, the theorem left the roster.  DRIVEN in a
# `git archive HEAD` clone: `set_option maxRecDepth 400 in theorem w28_.. :=
# trivial` and `open Nat in theorem w28_.. := trivial` appended to Emit.lean
# both ELABORATE (lake build rc=0) and both left `unaudited` EMPTY, while the
# same two theorems written on two lines were named at once.
#
# SO THE RULE IS A PROPERTY OF THE TOKEN, not of the line it sits on.  `theorem`
# is a RESERVED keyword in Lean 4 -- it cannot be part of any identifier -- so
# in source that has been comment- and string-stripped, EVERY occurrence of it
# as a token declares a theorem, wherever on the line it falls and whatever
# stands in front of it.  Nothing has to be added to this pattern for
# `noncomputable theorem`, for a fourth attribute block, for a modifier Lean
# gains in a later toolchain, or for an `in` combinator nobody has written yet.
# Measured over the library at the repair step: the old pattern and this one
# agree EXACTLY, 5,102 names each, no name in either difference.
#
# WHAT IT CANNOT SEE: a `theorem` produced by a macro or a `syntax` extension
# (the kernel defines none); a guillemet-quoted identifier that SPELLS the word
# with a space in front of it (`«a theorem»` -- the library's seven guillemet
# identifiers are `«matches»` and `«meta»`, greppable and neither); and the
# blind spots `strip_comments` lists.  The lookbehind is the identifier
# alphabet -- a word character, `'`, `?`, `!`, `.` or `«` -- so a name that ENDS
# in the word (free_theorem) and one that is qualified by it are not tokens of it.
THEOREM = re.compile(r"(?<![\w'?!.\u00AB])theorem[ \t\r\n]+([^\s(){}:]+)")


def theorem_names(path):
    """Every theorem DECLARED in `path`, as written (`Foo.bar` keeps its prefix).

    THE SHAPE IS THE THIRD PLACE THIS CAMPAIGN'S ENUMERATION WAS WRONG.  The
    walk was fixed at W-21, the library ROOT at W-23, and `check.sh`'s roster
    still asked bash for `theorem` at COLUMN ZERO with at most ONE attribute in
    front of it.  `private theorem` (four live: `Arith.cancelR`,
    `Look.scaled_le`, `Look.convex_between`, `Look.dayLeft_scale`), `protected`,
    `nonrec`, a second attribute block and anything INDENTED inside a `section`
    were all outside it -- declared, compiled and audited by nobody.

    AND WIDENING THE GREP ALONE WOULD HAVE BEEN WRONG IN THE OTHER DIRECTION,
    which is why this is a function and not a longer regex.  `Planner.lean` 6333
    writes an indented `theorem plan_reserves_one_block_at_a_time ..` inside a
    ```lean fence inside a `/-! -/` module docstring -- PROSE, quoting the goal
    it goes on to refute.  A column-zero grep missed it by luck; an indented
    grep would have demanded an audit line for a theorem that does not exist.
    So the source is comment-stripped first, by the same scanner the ban uses.

    AND W-27'S FIX WAS STILL A LIST OF PREFIXES, which is the W-28 repair step:
    the pattern was anchored at the line head, so a `theorem` that does not
    START its line -- `open Nat in theorem ..`, `set_option .. in theorem ..`,
    both of which elaborate and both of which this library writes on two lines
    today -- was outside the roster.  `THEOREM` above is now the KEYWORD TOKEN
    and its blind spots are listed there."""
    return THEOREM.findall(strip_comments(pathlib.Path(path).read_text()))


# **THE RECONCILIATION'S KEY IS THE FULL NAME, NOT THE SHORT ONE** (W-29 repair
# step, README gap 2008).  check 3 reconciled `theorem_names` against
# `Check.lean`'s `#print axioms` lines with BOTH sides put through
# `sed 's/.*\.//'`, so the comparison was a multiset over SHORT names: it saw a
# name that had been LOST and could not see a name that had been SWAPPED.
# DRIVEN in a clone before the repair: `Check.lean`'s
# `#print axioms Tm.PlanWire.the_refusals_spell_themselves` replaced by a second
# copy of `Tm.EmitWire.the_refusals_spell_themselves` left `lean Check.lean` at
# rc=0 with 5,220 axioms lines and check 3 saying `ok`, while
# `Tm.PlanWire.the_refusals_spell_themselves` was audited ZERO times.  25 short
# names are declared in more than one namespace at HEAD and 57 theorems sit on
# them, so the exposure was real and latent.
#
# The scanner below is the same token discipline one level up: `namespace`,
# `section`, `mutual` and `end` are keyword tokens in stripped source, and a
# declaration's full name is the `namespace` stack that encloses it, dotted,
# with the name AS WRITTEN after it.  `section` and `mutual` push a frame that
# contributes nothing and `end` pops one, which is exactly Lean's own rule.
#
# **The argument of `end`/`namespace` is read ON ITS OWN LINE**, never across a
# newline: `end` alone followed by a `theorem` on the next line would otherwise
# swallow the word `theorem` as the frame's name and lose the declaration.  The
# `theorem` name itself IS read across a newline, because `THEOREM` above does.
#
# MEASURED at the repair step: the qualified roster is 5,215 names, `Check.lean`
# holds 5,220 `#print axioms` lines, every roster name is audited at least once,
# and the five extra lines are the five `def`s the file audits deliberately.
#
# WHAT IT CANNOT SEE: a namespace opened by a macro; `end` in a construct this
# library does not write that is closed by `end` and is neither a namespace, a
# section nor a `mutual` block (the stack would be popped once too often, which
# makes a name SHORTER and so UNAUDITED -- the loud direction); and the blind
# spots `strip_comments` and `THEOREM` list.  A leftover frame at end of file is
# reported by `--theorems` rather than silently dropped.
# **AND THE SCANNER TOOK THE KEYWORD `theorem` AS PART OF ITS OWN SHAPE**, which
# made it answerable for one population out of the two that need it (W-31 track
# A).  Check 12 asks the same question of every `def` -- what does `lean` call
# this declaration, so that the emitted symbol can be computed from it -- and
# `twins.py` was answering it with a THIRD scanner of its own, a line walk that
# read `words[0] == "def"` and so could not see the three `private def`s of
# `Plan.lean` or the two `@[reducible] def`s beside them: it returned the
# namespace stack AT END OF FILE for each, which is a name that is not the
# declaration's.  The keyword is a PARAMETER now and the scanner is one.
_SCOPE_KW = {}


def scope_kw(kw):
    """`namespace`/`section`/`mutual`/`end` and one DECLARATION keyword, as tokens."""
    if kw not in _SCOPE_KW:
        _SCOPE_KW[kw] = re.compile(
            r"(?<![\w'?!.\u00AB])(namespace|section|mutual|end|%s)(?![\w'?!])" % kw)
    return _SCOPE_KW[kw]


SCOPE_KW = scope_kw("theorem")
SCOPE_ARG = re.compile(r"[ \t]*([^\s(){}:]*)")
THEOREM_ARG = re.compile(r"[ \t\r\n]*([^\s(){}:]+)")


def qualified_names(path, kw, code=None):
    """Every `kw` declaration in `path`, as `(written, as lean names it)` pairs.

    Returns `(pairs, leftover)` -- `leftover` is the namespace stack still open
    at end of file, which is a malformed source this walk must not answer for.
    The first half of a pair is the name AS WRITTEN (`PlanReq.assignFold`),
    which is the key a reader that found the declaration by its own regex has;
    the second is what `lean` calls it, which is what an axiom audit reconciles
    against and what a C symbol is computed from.

    `code` is the file's comment-stripped text when the caller already holds
    it (`twins.py` strips every module once and reads three things off the
    result); stripping is a character walk and was a third of check 11's wall
    when done twice per file (W-33)."""
    if code is None:
        code = strip_comments(pathlib.Path(path).read_text())
    stack, out, i = [], [], 0
    pat = scope_kw(kw)
    while True:
        m = pat.search(code, i)
        if not m:
            return out, [f for f in stack if f]
        word, i = m.group(1), m.end()
        if word == kw:
            n = THEOREM_ARG.match(code, i)
            if not n:
                continue
            i = n.end()
            prefix = ".".join(f for f in stack if f)
            out.append((n.group(1),
                        f"{prefix}.{n.group(1)}" if prefix else n.group(1)))
        else:
            n = SCOPE_ARG.match(code, i)
            i = n.end()
            if word == "namespace":
                stack.append(n.group(1))
            elif word in ("section", "mutual"):
                stack.append("")
            elif stack:
                stack.pop()
            else:
                out.append(("<end without a scope in %s>" % path,
                            "<end without a scope in %s>" % path))


# Where a command begins again: a non-space character in column zero.  ONE
# spelling, read by `twins.py`'s body scanner and by `constructors` below.
NEXT_COMMAND = re.compile(r"(?m)^\S")
# A declaration that OPENS a block of constructors or fields, with any
# attributes and modifiers in front of it.  `class` without `inductive` is a
# structure and has a constructor too.
BLOCK_HEAD = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+"
    r"|unsafe[ \t]+)*(structure|class[ \t]+inductive|inductive|class)\b[ \t]*([^\s(){}:]*)")
# A structure's own constructor name, `mk ::` or `intro ::` on its own line;
# without one the constructor is `mk`.
STRUCT_CTOR = re.compile(r"(?m)^[ \t]+([A-Za-z_][A-Za-z0-9_'!?]*)[ \t]*::")
# One field of a structure: `name : T` at the field indentation.
STRUCT_FIELD = re.compile(r"(?m)^[ \t]+([A-Za-z_][A-Za-z0-9_'!?]*)[ \t]*:[^=:]")
_OPENERS, _CLOSERS = "([{⟨⦃", ")]}⟩⦄"


def _depth0_bars(text):
    """The offsets of every `|` at bracket depth zero of `text` that is not `||`."""
    out, depth = [], 0
    for i, c in enumerate(text):
        if c in _OPENERS:
            depth += 1
        elif c in _CLOSERS:
            depth -= 1
        elif c == "|" and depth <= 0 and text[i - 1:i] != "|" and text[i + 1:i + 2] != "|":
            out.append(i)
    return out


def _ctor_arity(arm):
    """`(name, explicit arity)` of one constructor arm, `name (a b : T) {c} : X -> Y`.

    The explicit arity is what an APPLICATION of the constructor spells: every
    name in a `(..)` binder group, plus every depth-zero arrow in the declared
    type.  Implicit and instance groups are not spelled by an application."""
    m = re.match(r"\s*([^\s(){}:|]+)", arm)
    if not m:
        return None, 0
    name, i, n, arity, depth = m.group(1), m.end(), len(arm), 0, 0
    while i < n:
        c = arm[i]
        if depth == 0 and c in "({[⦃":
            close = _CLOSERS[_OPENERS.index(c)]
            d, j = 0, i
            while j < n:
                if arm[j] in _OPENERS:
                    d += 1
                elif arm[j] in _CLOSERS:
                    d -= 1
                    if d == 0:
                        break
                j += 1
            if c == "(":
                group = arm[i + 1:j]
                names = group.split(":", 1)[0] if ":" in group else group
                arity += sum(1 for t in names.split() if t)
            i = j + 1
            continue
        if depth == 0 and c == ":":
            rest = arm[i + 1:]
            d = 0
            k = 0
            while k < len(rest):
                ch = rest[k]
                if ch in _OPENERS:
                    d += 1
                elif ch in _CLOSERS:
                    d -= 1
                elif d == 0 and (ch == "→" or rest.startswith("->", k)):
                    arity += 1
                k += 1
            break
        if c in _OPENERS:
            depth += 1
        elif c in _CLOSERS:
            depth -= 1
        i += 1
    return name, arity


def constructors(text, stripped=True, structures=None):
    """Every constructor `text` declares, as a pair of tables.

    The first is {constructor short name: {explicit arities}} and the second is
    {(type short name, constructor): {arities}}, over every
    `inductive`, `class inductive`, `structure` and `class` in `text` -- the
    multi-line form (`| name` under the head) AND the one-line form
    (`inductive Weekday | monday | tuesday ..`), which check 8's block walk
    skipped: it matched the head line and `continue`d past the constructors
    written on it.  A structure's constructor is its `name ::` line or `mk`,
    with one explicit argument per field it declares itself (`extends` parents
    are not counted, which under-counts and so never collapses too much).

    THIS IS THE ONE SCANNER OF THAT CONCEPT (W-33 track A): check 11's second
    key reads it to know which names are constructors, and check 8's source 1
    reads it to know which names are declared.  Two walks of one declaration
    set would be AGENTS 5.3's defect inside the two gates that exist to catch
    it.

    With `structures` (a set), every (type short name, constructor) a
    `structure` or `class` declares is added to it -- the constructors an
    anonymous `⟨..⟩` spells, which check 11 re-spells to (W-34 repair, README
    gap 2733).  One walk still: the set is filled by the loop below."""
    code = strip_comments(text) if stripped else text
    by_short, by_qual = {}, {}
    for m in BLOCK_HEAD.finditer(code):
        kind, tname = m.group(1), m.group(2).split(".")[-1]
        stop = NEXT_COMMAND.search(code, m.end())
        chunk = code[m.end():stop.start() if stop else len(code)]
        if kind in ("structure", "class"):
            mm = STRUCT_CTOR.search(chunk)
            name = mm.group(1) if mm else "mk"
            arity = len(STRUCT_FIELD.findall(chunk))
            by_short.setdefault(name, set()).add(arity)
            by_qual.setdefault((tname, name), set()).add(arity)
            if structures is not None:
                structures.add((tname, name))
            continue
        bars = _depth0_bars(chunk)
        for k, at in enumerate(bars):
            arm = chunk[at + 1:bars[k + 1] if k + 1 < len(bars) else len(chunk)]
            name, arity = _ctor_arity(arm)
            if name:
                by_short.setdefault(name, set()).add(arity)
                by_qual.setdefault((tname, name), set()).add(arity)
    return by_short, by_qual


# The pinned toolchain's PRELUDE, read once: `Init/Prelude.lean` is the module
# every Lean file has before its first line, and it is where every core
# constructor this library spells by name is declared -- measured (W-33):
# Option's some and none, Except's ok and error, List's cons, Prod's mk, Or's
# inl and inr, And's intro, and bare some, none, true and false.  The whole
# `Init` tree was measured too and declined: 190 constructor short names
# against Prelude's 47, and the 143 it adds -- `line`, `text`, `node`, `day`,
# and `/--` out of an unstripped comment -- are English words a projection or
# a field spells, so a key that collapsed them would erase structure.
_CORE_CTORS = []


def core_constructors():
    """The two constructor tables of the pinned toolchain's `Init/Prelude.lean`."""
    if _CORE_CTORS:
        return _CORE_CTORS[0]
    path = toolchain_src() / "Init" / "Prelude.lean"
    if not path.is_file():
        raise SystemExit("leanfiles.core_constructors: no %s -- the constructor set "
                         "would be silently empty" % path)
    _CORE_CTORS.append(constructors(path.read_text(encoding="utf-8", errors="replace")))
    return _CORE_CTORS[0]


def qualified_theorem_names(path):
    """Every theorem declared in `path`, as `lean` names it (namespaces dotted on)."""
    pairs, leftover = qualified_names(path, "theorem")
    return [q for _, q in pairs], leftover


def main(argv):
    """Print every .lean file under each directory named, one per line.

    check.sh's check 3 is the caller: bash cannot express the prune rule above
    without repeating it, and repeating it is the defect this file exists to
    remove.

    `--library <pkg>` prints the library target of `pkg` -- its module
    directory AND its root module (`library_files`).

    `--theorems <pkg>` prints the check-3 ROSTER of that library: every theorem
    declared in it, comment-stripped, one per line, QUALIFIED by the namespace
    that encloses it (`qualified_theorem_names`) -- so check 3 reconciles by the
    name `lean` prints, and a SWAPPED audit line cannot hide behind a short name
    another namespace also spells."""
    if not argv:
        print("usage: leanfiles.py [--library|--theorems] <dir> [<dir> ...]", file=sys.stderr)
        return 2
    if argv[0] == "--theorems":
        for name in argv[1:]:
            for path in library_files(name):
                names, leftover = qualified_theorem_names(path)
                if leftover:
                    raise SystemExit("leanfiles: %s leaves %r open -- the roster would be "
                                     "qualified by the wrong namespace" % (path, leftover))
                for thm in names:
                    print(thm)
        return 0
    library = argv[0] == "--library"
    argv = argv[1:] if library else argv
    seen = set()
    for name in argv:
        for path in (library_files(name) if library else lean_files(name)):
            text = str(path)
            if text not in seen:
                seen.add(text)
                print(text)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
