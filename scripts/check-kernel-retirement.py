#!/usr/bin/env python3
"""Reject active dependencies on retired checker code.

Two retirements are recorded: the lean4lean/lean4ix proof system and the
Ix.Tc verification machinery (`docs/kernel.md`, "Removal ledger"), and the intrinsic
proof-carrying kernel with its entry points, tests, census and benchmark
(2026-10-01, `docs/kernel.md`; `INTRINSIC` below). Run from a checkout or a Nix source
export. Historical documentation and legal attribution are intentionally
outside this check; Lean comments are ignored, including nested comments.
The guard's own negative controls are the sole source-file exemption. This
does not establish kernel correctness: the strict Lean, model, provenance,
and differential gates remain separate.
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
# The intrinsic kernel (retired 2026-10-01): its modules (syntax, checker, inductive
# routes, certified rules, model, ingress and egress over its own syntax,
# runtime, consistency), its entry points, the executables and scripts that
# ran it, and its test and benchmark modules. Case-sensitive. Kept names are
# not matched: `Ix.Kernel.Ref`, `Ix.Kernel.Search`, `Ix.Kernel.Audit`,
# `Ix.Kernel.Ixon` (until 2026-10-01 `Ix.Kernel.ConLeche`; its namespaces
# `Ix.Kernel.IxonReader` and `Ix.Kernel.IxonFold`), the record store
# `Ix.Kernel.Ingress.Records` and the projection writer
# `Ix.Kernel.Egress.Projection` (with their namespaces), and
# `certified-kernel-differential` (a CI artifact name).
#
# Names reused since 2026-10-01: con-leche's checker, vendored under
# `Ix/Kernel/**`, has modules named as four of the intrinsic kernel's
# (`Ix.Kernel.Env`, `Ix.Kernel.Expr`, `Ix.Kernel.Level`, and the directory
# `Ix.Kernel.Model`), and its axiom pin is `Tests/Ix/Kernel/Axioms.lean`, the
# intrinsic kernel's axiom test's path. Those names are no longer rejected
# here; the intrinsic `Model` modules still are, by their own names. The
# reused paths are guarded by provenance instead: `kernel-provenance` admits
# a Lean file under `Ix/Kernel` only as a hash-pinned vendored row or a
# listed Ix-authored module, and the axiom pin is an adapted row.
INTRINSIC_MODULES = (
    "Annotate|Arithmetic|Check|Claims|Consistency|Const|"
    "ExprSubstitution|Fidelity|Infer|Quot|Rename|Revalue|Store|"
    "StringLiteral|VLevel|VLevelLemmas|Certified|Inductive|Runtime|Std"
)
# The intrinsic kernel's `Ix/Kernel/Model/**` modules (none of whose names
# con-leche's `Model` directory uses).
INTRINSIC_MODEL = (
    "Annotated|BetaSpine|BetaSubstitution|Checking|Context|ContextTransport|"
    "Environment|Extension|Inductive|Instantiation|Interpret|Judgment|LetRules|"
    "LevelCongruence|PrimitiveValues|QuotientValues|ReferenceMap|SetModel|SetTheory|"
    "Signature|Substitution|Support|TelescopeSemantics|UniverseBounds|Value|WellDenoted"
)
INTRINSIC_TESTS = (
    "AnnotationContexts|ConversionSpines|Differential|Egress|Fidelity|"
    "Fixtures|Inductives|Ingress|IngressHost|Interleaved|LevelDifferential|"
    "Literals|ProofIrrelevance|Quotients|RuntimeStack|SearchOutcomes|"
    "Structures|SubstitutionSharing"
)
INTRINSIC = re.compile(
    r"checkBytesIntrinsic|kernel-census-intrinsic|kernel-census-probe|"
    r"bench-certified-kernel|count-certified-kernel|kernel-level-differential|"
    r"(?<![\w-])kernel-(?:differential|ingress)(?![\w-])|"
    r"Tests[./]Ix[./]Kernel[./](?:" + INTRINSIC_TESTS + r")\b|"
    r"Benchmarks[./]Kernel[./](?:Census|CensusMain|CensusProbe|Certified)\b|"
    r"Ix[./]Kernel[./](?:" + INTRINSIC_MODULES + r")\b|"
    r"Ix[./]Kernel[./]Model[./](?:" + INTRINSIC_MODEL + r")\b|"
    r"Ix[./]Kernel[./](?:Ingress[./](?:Reading|Expr|Constant)|Egress[./](?:Layout|Expr|Constant))\b|"
    r"Ix/Kernel/(?:Ingress|Egress)\.lean|"
    r"\bimport\s+(?:all\s+)?Ix\.Kernel\.(?:Ingress|Egress)(?![\w.])"
)
RETIRED_TREES = (
    "Ix/Tc/Verify/", "Ix/Compile/Verify/", "crates/ffi-dyn/",
    # The intrinsic kernel's wholly retired directories (its `Model/` is
    # retired module by module below: con-leche's is vendored there).
    "Ix/Kernel/Certified/", "Ix/Kernel/Inductive/", "Ix/Kernel/Model/Inductive/",
    "Ix/Kernel/Model/SetModel/", "Ix/Kernel/Model/SetTheory/",
    "Ix/Kernel/Runtime/", "Ix/Kernel/Std/",
)
RETIRED_FILES = {
    "Benchmarks/Lean4Lean.lean",
    "Benchmarks/Lean4LeanMain.lean",
    "Benchmarks/TruthMines/Drivers/Lean4Lean.lean",
    "Benchmarks/Compile/TruthMines/Members/Lean4Lean.lean",
    "Tests/Ix/Lean4Lean.lean",
    # The intrinsic kernel's census, benchmark and scripts.
    "Benchmarks/Kernel/Census.lean",
    "Benchmarks/Kernel/CensusMain.lean",
    "Benchmarks/Kernel/CensusProbe.lean",
    "Benchmarks/Kernel/Certified.lean",
    "scripts/bench-certified-kernel.py",
    "scripts/count-certified-kernel.py",
} | {f"Tests/Ix/Kernel/{name}.lean" for name in INTRINSIC_TESTS.split("|")} | {
    f"Ix/Kernel/{name}.lean" for name in INTRINSIC_MODULES.split("|")
    if name not in ("Certified", "Inductive", "Runtime", "Std")
} | {"Ix/Kernel/Model.lean"} | {
    f"Ix/Kernel/Model/{name}.lean" for name in INTRINSIC_MODEL.split("|")
    if name not in ("Inductive", "SetModel", "SetTheory")
} | {
    "Ix/Kernel/Ingress.lean", "Ix/Kernel/Ingress/Reading.lean", "Ix/Kernel/Ingress/Expr.lean",
    "Ix/Kernel/Ingress/Constant.lean", "Ix/Kernel/Egress.lean", "Ix/Kernel/Egress/Layout.lean",
    "Ix/Kernel/Egress/Expr.lean", "Ix/Kernel/Egress/Constant.lean",
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
    if path.startswith("docs/"):
        return []
    if file.suffix == ".lean":
        content = lean_without_comments(content)
    elif file.suffix not in CONFIG_SUFFIXES and file.name != "Cargo.lock":
        return []
    matches = sorted([*RETIRED.finditer(content), *INTRINSIC.finditer(content)],
                     key=lambda match: match.start())
    return [
        f"{path}:{content.count(chr(10), 0, match.start()) + 1}: "
        f"retired active reference {match.group()}"
        for match in matches
    ]


def source_paths(root: Path) -> list[str]:
    if (root / ".jj").is_dir():
        command = ["jj", "file", "list"]
        separator = "\n"
    elif (root / ".git").exists():
        command = ["git", "ls-files", "-z"]
        separator = "\0"
    else:
        # Nix exports have no VCS metadata. Never descend into caches, nor
        # into `plans/`, which is never versioned (`.gitignore`).
        paths = []
        for directory, dirs, files in os.walk(root):
            relative = Path(directory).relative_to(root)
            dirs[:] = [d for d in dirs if d not in EXCLUDED_DIRS
                       and not (relative == Path(".") and d == "plans")]
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
        # nothing under plans/ is versioned, so nothing there is exempt
        ("plans/Fixture.lean", "import Lean4Lean.Environment"),
    ):
        if not inspect(path, content):
            raise RuntimeError(f"retirement control escaped: {path}")
    if inspect("docs/history.md", "Lean4Lean attribution") or inspect("NOTICE", "lean4ix"):
        raise RuntimeError("historical documentation or legal attribution rejected")
    # The intrinsic kernel: its entries, executables and modules are
    # rejected in code and configuration; comments and kept names are not.
    for path, source in (
        ("Fixture.lean", "#eval Ix.Ixon.Admission.checkBytesIntrinsic"),
        ("Fixture.lean", "import Tests.Ix.Kernel.Fixtures"),
        ("Fixture.lean", "roots := #[`Benchmarks.Kernel.Census]"),
        ("Fixture.lean", 'run "lake" #["build", "kernel-differential"]'),
        ("scripts/run.sh", "lake exe bench-certified-kernel"),
        ("Tests/Ix/Kernel/Fixtures.lean", ""),
        ("Fixture.lean", "import Ix.Kernel.Check"),
        ("Fixture.lean", "public import Ix.Kernel.Model.SetTheory.Core"),
        ("Fixture.lean", "import Ix.Kernel.Ingress"),
        ("Fixture.lean", "import\n  Ix.Kernel.Egress\nimport Init"),
        ("Fixture.lean", "import Ix.Kernel.Ingress.Reading"),
        ("Fixture.lean", "theorem t : Ix.Kernel.Model.SetTheory V := x"),
        ("Fixture.lean", 'def p := "Ix/Kernel/Egress.lean"'),
        ("Ix/Kernel/Certified/Checker.lean", ""),
        ("Ix/Kernel/Check.lean", ""),
        ("Ix/Kernel/Egress/Layout.lean", ""),
        ("Ix/Kernel/Model/Judgment.lean", ""),
        ("Ix/Kernel/Model/SetTheory/Core.lean", ""),
        ("Fixture.lean", "import Ix.Kernel.Model.Interpret"),
        ("Fixture.lean", "import Tests.Ix.Kernel.Ingress"),
    ):
        if not inspect(path, source):
            raise RuntimeError(f"intrinsic negative control escaped: {path}: {source}")
    for source in (
        "/- `checkBytesIntrinsic` and `kernel-census-intrinsic` were retired. -/\nimport Init",
        "import Tests.Ix.Kernel.IxonFixtures\nimport Benchmarks.Kernel.CheckIxeMain",
        "import Benchmarks.Kernel.IxEnv\nimport Tests.Ix.Kernel.IngressFixturesNew",
        'def artifact := "certified-kernel-differential"',
        "import Ix.Kernel.Ingress.Records\nimport Ix.Kernel.Egress.Projection\nimport Ix.Kernel.Ref",
        "import Ix.KernelCheck\nimport Ix.Kernel.Ixon.Reader\nimport Ix.Kernel.Search",
        "namespace Ix.Kernel.Ingress\nend Ix.Kernel.Ingress\nopen Ix.Kernel.Egress",
        "def r : Ix.Kernel.ConstRef Address := x\n#check Ix.Kernel.Ingress.Constants",
        "/- retired at L6: Ix.Kernel.Check, Ix/Kernel/Model/SetTheory -/\nimport Init",
        # con-leche's vendored modules that reuse intrinsic names (2026-10-01)
        "import Ix.Kernel.Expr\nimport Ix.Kernel.Env\nimport Ix.Kernel.Level",
        "import Ix.Kernel.Model.Fold\nimport Ix.Kernel.Model.Claims\nimport Ix.Kernel.SetTheory.Core",
        "import Tests.Ix.Kernel.Axioms\nimport Ix.Kernel.Checker\nimport Ix.Kernel.Inductives.StructParts",
        # the certified entry's tools and tests under their current names (step 3)
        "import Tests.Ix.Kernel.LevelComparison\nimport Tests.Ix.Kernel.Reader\nimport Ix.Ixon.KernelAdmission",
        "open Ix.Kernel.IxonReader\nopen Ix.Kernel.IxonFold\nimport Benchmarks.Kernel.CheckIxeStep",
        'run "lake" #["build", "kernel-level-comparison", "kernel-check-ixe", "kernel-pin-gen"]',
    ):
        if inspect("Fixture.lean", source):
            raise RuntimeError(f"kept name or comment rejected: {source}")


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
