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

WHAT IT CANNOT SEE.  A build directory that is neither dot-prefixed nor tagged
is walked, and a .lean file inside it is read as a source.  That direction is
the safe one -- a gate scanning too much fails loudly on a generated file rather
than falling silent on a real one -- but it is not free: a vendored toolchain
unpacked under kernel/ would be scanned as if it were this kernel.  Measured at
the W-22 repair step: 0 .lean files live under any pruned directory of this
repository today, so pruning changes nothing here and exists for a future
layout.
"""
import re
import pathlib
import sys

# The cache-directory marker.  Its content is a fixed signature line; this
# checker tests for the file's existence only, because a directory that carries
# the name at all is claiming to be derived output.
CACHE_TAG = "CACHEDIR.TAG"


def is_build_dir(path):
    """Is this directory derived output rather than source?"""
    return path.name.startswith(".") or (path / CACHE_TAG).is_file()


def source_files(root, suffix):
    """Every `suffix` file under `root`, recursively, sorted, build dirs pruned.

    `suffix=None` means EVERY file, which is what check 10's parity sweep asks
    for: a suffix list is itself a name list, and at the W-25 repair step a
    `**Parity P41 taken**` line planted in `design/stage6/notes.txt`, in
    `notes.org`, in `mutations.txt` and in `check.sh` went GREEN through a
    three-suffix walk.  The prune rule is unchanged; the caller decodes with
    `errors="replace"`, because a whole-file walk reaches `.pyc` and `.snap`.

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
    out = []
    stack = [root]
    while stack:
        here = stack.pop()
        try:
            entries = sorted(here.iterdir())
        except (FileNotFoundError, NotADirectoryError, PermissionError):
            continue
        for entry in entries:
            if entry.is_dir():
                if not is_build_dir(entry):
                    stack.append(entry)
            elif suffix is None or entry.suffix == suffix:
                out.append(entry)
    return sorted(out)


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


def main(argv):
    """Print every .lean file under each directory named, one per line.

    check.sh's check 3 is the caller: bash cannot express the prune rule above
    without repeating it, and repeating it is the defect this file exists to
    remove.

    `--library <pkg>` prints the library target of `pkg` -- its module
    directory AND its root module (`library_files`).

    `--theorems <pkg>` prints the check-3 ROSTER of that library: every theorem
    declared in it, comment-stripped, one per line (`theorem_names`)."""
    if not argv:
        print("usage: leanfiles.py [--library|--theorems] <dir> [<dir> ...]", file=sys.stderr)
        return 2
    if argv[0] == "--theorems":
        for name in argv[1:]:
            for path in library_files(name):
                for thm in theorem_names(path):
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
