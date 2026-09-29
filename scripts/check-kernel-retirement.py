#!/usr/bin/env python3
"""Reject active dependencies on the retired checker proof system.

Run from a checkout or a Nix source export. Historical documentation and
legal attribution are intentionally outside this check; Lean comments are
ignored, including nested comments. The guard's own negative controls are
the sole source-file exemption. This does not establish kernel correctness:
the strict Lean, model, provenance, and differential gates remain separate.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys


SELF = "scripts/check-kernel-retirement.py"
RETIRED = re.compile(
    r"Lean4Lean|lean4ix|Ix[./]Tc[./]Verify|Ix[./]Compile[./]Verify|"
    r"IxTcVerify|IxCompileVerify|ix_native_decide_dynlib|ix_ffi_dyn|"
    r"ix-ffi-dyn|crates/ffi-dyn",
    re.IGNORECASE,
)
RETIRED_TREES = ("Ix/Tc/Verify/", "Ix/Compile/Verify/", "crates/ffi-dyn/")
RETIRED_FILES = {
    "Benchmarks/Lean4Lean.lean",
    "Benchmarks/Lean4LeanMain.lean",
    "Benchmarks/TruthMines/Drivers/Lean4Lean.lean",
    "Benchmarks/Compile/TruthMines/Members/Lean4Lean.lean",
    "Tests/Ix/Lean4Lean.lean",
}
CONFIG_SUFFIXES = {".nix", ".toml", ".yml", ".yaml", ".sh", ".py"}
EXCLUDED_DIRS = {".git", ".jj", ".lake", "target", "__pycache__"}


def lean_without_comments(source: str) -> str:
    """Keep code and strings; blank comments without changing line numbers."""
    result = list(source)
    i = 0
    depth = 0
    string = False
    while i < len(source):
        pair = source[i : i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result[i : i + 2] = "  "
                i += 2
            elif pair == "-/":
                depth -= 1
                result[i : i + 2] = "  "
                i += 2
            else:
                if source[i] != "\n":
                    result[i] = " "
                i += 1
        elif string:
            if source[i] == "\\":
                i += 2
            else:
                if source[i] == '"':
                    string = False
                i += 1
        elif pair == "/-":
            depth = 1
            result[i : i + 2] = "  "
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            if end == -1:
                end = len(source)
            result[i:end] = " " * (end - i)
            i = end
        else:
            if source[i] == '"':
                string = True
            i += 1
    return "".join(result)


def inspect(path: str, content: str) -> list[str]:
    if path.startswith(RETIRED_TREES) or path in RETIRED_FILES:
        return [f"{path}: retired source path"]
    if path == SELF:
        return []
    file = Path(path)
    if file.name == "lake-manifest.json":
        try:
            packages = json.loads(content)["packages"]
            if not isinstance(packages, list):
                raise ValueError("packages must be an array")
            errors = []
            for package in packages:
                if not isinstance(package, dict):
                    raise ValueError("package must be an object")
                # Check all fields: aliases must not hide a retired URL/path.
                if RETIRED.search(json.dumps(package)):
                    errors.append(f"{path}: retired dependency {package.get('name', '?')}")
            return errors
        except (ValueError, KeyError, TypeError) as error:
            return [f"{path}: invalid Lake manifest: {error}"]
    if path.startswith(("docs/", "plans/")):
        return []
    if file.suffix == ".lean":
        content = lean_without_comments(content)
    elif file.suffix not in CONFIG_SUFFIXES and file.name != "Cargo.lock":
        return []
    return [
        f"{path}:{content.count(chr(10), 0, match.start()) + 1}: "
        f"retired active reference {match.group()}"
        for match in RETIRED.finditer(content)
    ]


def source_paths(root: Path) -> list[str]:
    if (root / ".jj").is_dir():
        command = ["jj", "file", "list"]
        separator = "\n"
    elif (root / ".git").exists():
        command = ["git", "ls-files", "-z"]
        separator = "\0"
    else:
        # Nix exports have no VCS metadata. Never descend into caches/refs.
        paths = []
        for directory, dirs, files in os.walk(root):
            relative = Path(directory).relative_to(root)
            dirs[:] = [d for d in dirs if d not in EXCLUDED_DIRS
                       and not (relative == Path("plans") and d == "refs")]
            paths.extend((relative / file).as_posix() for file in files)
        return sorted(paths)
    output = subprocess.run(command, cwd=root, check=True, capture_output=True, text=True)
    return [path for path in output.stdout.split(separator) if path]


def controls() -> None:
    """Adversarial controls for import syntax, aliases, and preserved history."""
    for source in (
        "import Lean4Lean.Environment",
        "public import all Ix.Tc.Verify.Audit.Basic",
        "import\n  Ix.Compile.Verify.Codec",
        "public /- nested /- import Init -/ comment -/ import Lean4Lean",
        'require replacement from git "https://github.com/argumentcomputer/lean4ix"',
        'def backend := "bench-lean4lean"',
        "lean_lib IxTcVerify",
    ):
        if not inspect("Fixture.lean", source):
            raise RuntimeError(f"negative control escaped: {source}")
    for source in (
        "/- Ported from Lean4Lean. /- Ix.Tc.Verify -/ Attribution. -/\nimport Init",
        "-- historical Ix.Compile.Verify.Codec\nimport Init",
        'def marker := "-- /- \\\""\n/- Lean4Lean attribution -/\nimport Init',
    ):
        if inspect("Fixture.lean", source):
            raise RuntimeError(f"historical comment rejected: {source}")
    for package in (
        {"name": "«lean4lean»"},
        {"name": "alias", "url": "https://github.com/digama0/lean4lean.git"},
        {"name": "alias", "url": "https://github.com/argumentcomputer/lean4ix"},
    ):
        if not inspect("Nested/lake-manifest.json", json.dumps({"packages": [package]})):
            raise RuntimeError(f"retired manifest dependency escaped: {package}")
    for path, content in (
        ("flake.nix", "depOverride.lean4lean = {};"),
        (".github/workflows/ci.yml", "run: lake build IxCompileVerify"),
        ("Cargo.lock", 'name = "ix-ffi-dyn"'),
        ("Ix/Tc/Verify/Empty.lean", ""),
        ("Nested/lake-manifest.json", "{}"),
    ):
        if not inspect(path, content):
            raise RuntimeError(f"retirement control escaped: {path}")
    if inspect("docs/history.md", "Lean4Lean attribution") or inspect("NOTICE", "lean4ix"):
        raise RuntimeError("historical documentation or legal attribution rejected")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    controls()
    root = args.root.resolve()
    errors = []
    paths = source_paths(root)
    for relative in paths:
        path = root / relative
        # Git lists staged deletions too; only current source is active.
        if not path.is_file():
            continue
        if (relative.startswith(RETIRED_TREES) or relative in RETIRED_FILES
                or path.suffix in CONFIG_SUFFIXES | {".lean"}
                or path.name in {"Cargo.lock", "lake-manifest.json"}):
            errors.extend(inspect(relative, path.read_text()))
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Kernel retirement: active references absent ({len(paths)} source paths); controls passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
