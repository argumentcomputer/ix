#!/usr/bin/env python3
"""Vendor con-leche's checker into `Ix/Kernel/**`: the mechanical rewrite.

Ix's certified kernel is con-leche (https://github.com/leanprover/con-leche),
vendored in place under `Ix/Kernel/**` with namespace `Ix.Kernel`
(`docs/kernel.md`, "Vendored con-leche"). A vendored file is exactly
`rewrite(source, path)` of con-leche's file `path` at the revision its
provenance row records (`Tests/Ix/Kernel/ImportManifest.lean`,
`Transformation.rewritten`), and nothing else:

* paths: `ConLeche/Kernel/X` becomes `Ix/Kernel/X`, any other `ConLeche/X`
  becomes `Ix/Kernel/X`, and the umbrella `ConLeche.lean` becomes
  `Ix/Kernel.lean`;
* names: the namespace and module prefix `ConLeche.Kernel` and `ConLeche`
  become `Ix.Kernel` (so `import ConLeche.Kernel.Core` is
  `import Ix.Kernel.Core` and `ConLeche.Expr` is `Ix.Kernel.Expr`), as a whole
  word only: `ConLecheCapsWall`, `ConLechePinCerts`, `tests/ConLecheTests`
  keep their spelling;
* one comment line in front, naming the source file and this script.

The rewrite is deterministic and depends only on the file and its upstream
path, so `kernel-provenance --source-git <checkout>` re-derives every
vendored file from the upstream revision through this script (`hash`) and
compares it with the recorded hash. Adapted files (a port header, their own
row summary) and Ix-authored files inside the vendored tree are not produced
by it; `sync` leaves them alone.

Subcommands (run from the repository root; stdlib only):

  dest PATH...                 the destination of each upstream path
  upstream DEST...             the upstream path of each file of the vendored
                               tree (the inverse of `dest`)
  rewrite PATH [IN [OUT]]      rewrite IN (default stdin), con-leche's PATH,
                               to OUT (default stdout)
  hash CHECKOUT REV:PATH...    for each, `git -C CHECKOUT show REV:PATH`, then
                               print "source-sha256 rewritten-sha256 dest REV:PATH"
  rows CHECKOUT REV PATH...    provenance TSV rows (`scripts/provenance-rows.py`)
                               for rewritten files: the hashes, from upstream
  sync CHECKOUT REV [PATH...]  write the rewrite of each upstream file at REV to
                               its destination (default: every file under
                               `ConLeche/` at REV whose destination exists and
                               is vendored, not adapted or Ix-authored), and
                               list upstream files that have no destination
  list                         the Lean files of the vendored tree: every
                               `Ix/Kernel/**.lean` except Ix's boundary
  lake-globs                   the vendored library's globs, for the lakefiles
  check-lake LAKEFILE...       each lakefile's vendored-library globs (between
                               the markers) are exactly `lake-globs`

An upstream sync is: `sync` at the new revision, review the diff, merge the
adapted files by hand, `rows` for the changed files, re-splice the manifest
with `scripts/provenance-rows.py`, and run `kernel-provenance --source-git`.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import re
import subprocess
import sys

UPSTREAM = "ConLeche/"
UPSTREAM_KERNEL = "ConLeche/Kernel/"
DEST = "Ix/Kernel/"

# Ix's own modules under `Ix/Kernel/` (the boundary between Ixon and the
# vendored checker). A destination never lands here; everything else under
# `Ix/Kernel/` is the vendored tree.
BOUNDARY_FILES = ("Ix/Kernel/Ref.lean", "Ix/Kernel/Search.lean")
BOUNDARY_DIRS = ("Ix/Kernel/Audit/", "Ix/Kernel/Ingress/", "Ix/Kernel/Egress/", "Ix/Kernel/Ixon/")

# The entries of upstream's `ConLeche/` other than `Kernel/` (stems, at
# ae0c0c4e, 3ca9e2fe and master as of 2026-10-01). `ConLeche/Kernel/X` is
# flattened to `Ix/Kernel/X`, so its entries must never share a stem with
# these; `dest_path` refuses a path that would, and a top-level entry not
# listed here, so that `upstream_path` stays the inverse of `dest_path`.
UPSTREAM_TOP = frozenset({
    "Accepts", "Cached", "Challenge", "Complete", "Denotes", "Frontend", "MainTheorem", "Model",
    "PinGen", "Rules", "Semantics", "SetModel", "SetTheory", "Term", "Verify"})

PORT_HEADER = "/-\nPorted from con-leche at "
LAKE_BEGIN = "-- BEGIN vendored kernel modules (scripts/vendor-conleche.py check-lake)"
LAKE_END = "-- END vendored kernel modules"

# A path component (`ConLeche/…`, also inside a longer path such as
# `.lake/build/ir/ConLeche/…`) or a whole name (`ConLeche`, `_root_.ConLeche`;
# not the tail of a longer name such as `Tests.ConLeche`, nor a longer word).
_PATH_START = r"(?<![A-Za-z0-9_.])"
_WORD_START = r"(?:(?<=_root_\.)|(?<![A-Za-z0-9_./]))"
REWRITES = [
    (re.compile(_PATH_START + r"ConLeche/Kernel/"), "Ix/Kernel/"),
    (re.compile(_PATH_START + r"ConLeche/Kernel(?![A-Za-z0-9_])"), "Ix/Kernel"),
    (re.compile(_PATH_START + r"ConLeche/"), "Ix/Kernel/"),
    (re.compile(_PATH_START + r"ConLeche\.lean(?![A-Za-z0-9_])"), "Ix/Kernel.lean"),
    (re.compile(_WORD_START + r"ConLeche\.Kernel(?![A-Za-z0-9_'])"), "Ix.Kernel"),
    (re.compile(_WORD_START + r"ConLeche(?![A-Za-z0-9_'/])"), "Ix.Kernel"),
]


def fail(message: str) -> None:
    raise SystemExit(f"vendor-conleche: {message}")


def is_boundary(dest: str) -> bool:
    return dest in BOUNDARY_FILES or dest.startswith(BOUNDARY_DIRS)


def _stem(rest: str) -> str:
    head = rest.split("/", 1)[0]
    return head[: -len(".lean")] if head.endswith(".lean") else head


def dest_path(path: str) -> str:
    """The destination of con-leche's `path` (upstream, repository-relative)."""
    if path == "ConLeche.lean":
        return "Ix/Kernel.lean"
    if path.startswith(UPSTREAM_KERNEL):
        rest = path[len(UPSTREAM_KERNEL):]
        if _stem(rest) in UPSTREAM_TOP:
            fail(f"{path} would collide with upstream's ConLeche/{_stem(rest)} in Ix/Kernel")
    elif path.startswith(UPSTREAM):
        rest = path[len(UPSTREAM):]
        if _stem(rest) not in UPSTREAM_TOP:
            fail(f"{path}: a new top-level entry of upstream's ConLeche/; add {_stem(rest)!r} "
                 f"to UPSTREAM_TOP once it is known not to collide with ConLeche/Kernel/")
    else:
        fail(f"not a con-leche source path under {UPSTREAM}: {path}")
    dest = DEST + rest
    if is_boundary(dest):
        fail(f"{path} would land in Ix's boundary ({dest})")
    return dest


def upstream_path(dest: str) -> str:
    """Where a file of the vendored tree sits upstream (or would, for the
    Ix-authored modules inside it): the inverse of `dest_path`."""
    if not dest.startswith(DEST) or is_boundary(dest):
        fail(f"not in the vendored tree: {dest}")
    rest = dest[len(DEST):]
    return (UPSTREAM if _stem(rest) in UPSTREAM_TOP else UPSTREAM_KERNEL) + rest


def header(path: str) -> str:
    return (f"-- con-leche's {path}, vendored by scripts/vendor-conleche.py "
            f"(paths and namespace ConLeche → Ix.Kernel); see Ix/Kernel/NOTICE.\n")


def rewrite(source: bytes, path: str) -> bytes:
    dest_path(path)  # refuse paths outside the vendored tree
    text = source.decode("utf-8")
    for pattern, replacement in REWRITES:
        text = pattern.sub(replacement, text)
    return (header(path) + text).encode("utf-8")


def git_show(checkout: str, rev: str, path: str) -> bytes:
    shown = subprocess.run(["git", "-C", checkout, "show", f"{rev}:{path}"],
                           capture_output=True, check=False)
    if shown.returncode != 0:
        fail(f"cannot read {path} at {rev}: {shown.stderr.decode(errors='replace').strip()}")
    return shown.stdout


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def split_item(item: str) -> tuple[str, str]:
    rev, sep, path = item.partition(":")
    if not sep or not rev or not path:
        fail(f"expected REV:PATH, found {item!r}")
    return rev, path


def vendored_tree() -> list[str]:
    root = Path(DEST)
    files = [p.as_posix() for p in root.rglob("*.lean")] if root.is_dir() else []
    return sorted(f for f in files if not is_boundary(f))


def module(path: str) -> str:
    return path[: -len(".lean")].replace("/", ".")


def lake_globs() -> list[str]:
    """One glob per top-level entry of the vendored tree: `.one` for a lone
    file, `.andSubmodules` for a directory with a same-named module,
    `.submodules` for a directory without one."""
    tops: dict[str, set[str]] = {}
    for f in vendored_tree():
        rest = f[len(DEST):]
        head, sep, _ = rest.partition("/")
        if sep:
            tops.setdefault(head, set()).add("dir")
        else:
            tops.setdefault(head[: -len(".lean")], set()).add("file")
    globs = []
    for name in sorted(tops):
        kinds = tops[name]
        target = f"`Ix.Kernel.{name}"
        if kinds == {"file"}:
            globs.append(f".one {target}")
        elif kinds == {"dir"}:
            globs.append(f".submodules {target}")
        else:
            globs.append(f".andSubmodules {target}")
    return globs


GLOB = re.compile(r"\.(one|submodules|andSubmodules)\s+`([A-Za-z0-9_.]+)")


def check_lake(lakefile: str) -> None:
    text = Path(lakefile).read_text(encoding="utf-8")
    if text.count(LAKE_BEGIN) != 1 or text.count(LAKE_END) != 1:
        fail(f"{lakefile}: expected one vendored-module region between the markers")
    region = text[text.index(LAKE_BEGIN) + len(LAKE_BEGIN): text.index(LAKE_END)]
    found = sorted(f".{kind} `{name}" for kind, name in GLOB.findall(region))
    expected = sorted(lake_globs())
    if found != expected:
        missing = [g for g in expected if g not in found]
        extra = [g for g in found if g not in expected]
        fail(f"{lakefile}: vendored globs differ from the tree; missing {missing}, unexpected {extra}")


def is_adapted_or_authored(dest: str) -> bool:
    path = Path(dest)
    if not path.exists():
        return False
    head = path.read_bytes()[:200].decode("utf-8", errors="replace")
    return head.startswith(PORT_HEADER) or not head.startswith("-- con-leche's ")


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__, file=sys.stderr)
        return 2
    command, args = argv[0], argv[1:]
    if command == "dest":
        for path in args:
            print(dest_path(path))
    elif command == "rewrite":
        if not 1 <= len(args) <= 3:
            fail("usage: rewrite PATH [IN [OUT]]")
        path = args[0]
        source = sys.stdin.buffer.read() if len(args) < 2 or args[1] == "-" else Path(args[1]).read_bytes()
        out = rewrite(source, path)
        if len(args) < 3 or args[2] == "-":
            sys.stdout.buffer.write(out)
        else:
            Path(args[2]).write_bytes(out)
    elif command == "hash":
        if not args:
            fail("usage: hash CHECKOUT REV:PATH...")
        checkout = args[0]
        for item in args[1:]:
            rev, path = split_item(item)
            source = git_show(checkout, rev, path)
            print(f"{sha256(source)} {sha256(rewrite(source, path))} {dest_path(path)} {item}")
    elif command == "rows":
        if len(args) < 2:
            fail("usage: rows CHECKOUT REV PATH...")
        checkout, rev = args[0], args[1]
        for path in args[2:]:
            source = git_show(checkout, rev, path)
            print("\t".join([path, sha256(source), dest_path(path), sha256(rewrite(source, path)), "rewritten"]))
    elif command == "sync":
        if len(args) < 2:
            fail("usage: sync CHECKOUT REV [PATH...]")
        checkout, rev = args[0], args[1]
        listed = subprocess.run(["git", "-C", checkout, "ls-tree", "-r", "--name-only", rev, UPSTREAM],
                                capture_output=True, text=True, check=True).stdout.split()
        paths = args[2:] or [p for p in listed if Path(dest_path(p)).exists()]
        written = unchanged = 0
        skipped = []
        for path in paths:
            dest = dest_path(path)
            if is_adapted_or_authored(dest):
                skipped.append(dest)
                continue
            out = rewrite(git_show(checkout, rev, path), path)
            target = Path(dest)
            if target.exists() and target.read_bytes() == out:
                unchanged += 1
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(out)
            written += 1
        print(f"{written} written, {unchanged} unchanged at {rev}")
        for dest in skipped:
            print(f"not rewritten (adapted or Ix-authored; merge by hand): {dest}")
        for path in listed:
            if path.endswith(".lean") and not Path(dest_path(path)).exists():
                print(f"upstream file not vendored: {path}")
    elif command == "upstream":
        for dest in args:
            print(upstream_path(dest))
    elif command == "list":
        for f in vendored_tree():
            print(f)
    elif command == "lake-globs":
        for g in lake_globs():
            print(g)
    elif command == "check-lake":
        if not args:
            fail("usage: check-lake LAKEFILE...")
        for lakefile in args:
            check_lake(lakefile)
        print(f"vendored globs of {', '.join(args)} match the tree ({len(lake_globs())} globs, "
              f"{len(vendored_tree())} modules)")
    else:
        fail(f"unknown command {command!r}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
