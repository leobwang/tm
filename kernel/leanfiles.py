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
import pathlib
import sys

# The cache-directory marker.  Its content is a fixed signature line; this
# checker tests for the file's existence only, because a directory that carries
# the name at all is claiming to be derived output.
CACHE_TAG = "CACHEDIR.TAG"


def is_build_dir(path):
    """Is this directory derived output rather than source?"""
    return path.name.startswith(".") or (path / CACHE_TAG).is_file()


def lean_files(root):
    """Every .lean file under `root`, recursively, sorted, build dirs pruned.

    `root` is a pathlib.Path or a string; the results are pathlib.Path objects
    under it, so a caller that wants relative or absolute strings converts.
    The walk is explicit rather than a glob because pruning has to stop the
    DESCENT: a glob that filters its results still reads every file name under
    a build directory."""
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
            elif entry.suffix == ".lean":
                out.append(entry)
    return sorted(out)


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


def main(argv):
    """Print every .lean file under each directory named, one per line.

    check.sh's check 3 is the caller: bash cannot express the prune rule above
    without repeating it, and repeating it is the defect this file exists to
    remove.

    `--library <pkg>` prints the library target of `pkg` -- its module
    directory AND its root module (`library_files`)."""
    if not argv:
        print("usage: leanfiles.py [--library] <dir> [<dir> ...]", file=sys.stderr)
        return 2
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
