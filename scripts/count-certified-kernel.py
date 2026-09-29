#!/usr/bin/env python3
"""Count certified-kernel operations in an isolated diagnostic source copy.

The production workspace is read-only. The copy adds diagnostic trace markers to
selected operations, builds the native fixture runner, and counts markers.
These runs measure operations, not time or the certified runtime boundary.
Use bench-certified-kernel.py on the unmodified source for timings and RSS.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "IxKernel.count."
TRACE = "Ix.Kernel.Diagnostic.trace"
CASES = {"env": 16, "address": 16, "references": 16, "binders": 8,
         "beta": 8, "context": 16, "spine": 32, "ordinary": 1,
         "structure": 1, "quotient": 1}


def equation_counter(text: str, name: str, marker: str) -> str:
    """Wrap each outer equation, including exhausted calls, exactly once."""
    header = re.search(r"^def " + re.escape(name) + r"(?:\s|:)", text, re.M)
    if header is None:
        raise ValueError(f"missing definition {name}")
    start = header.start()
    end = text.index("\n\n", start)
    region = text[start:end]
    region, count = re.subn(
        r"^(  \| .+? =>)([^\n]*)$",
        lambda m: m.group(1) + f'\n    {TRACE} "{PREFIX}{marker}" fun _ =>'
        + ("\n   " + m.group(2) if m.group(2).strip() else ""),
        region, flags=re.M,
    )
    if count < 2:
        raise ValueError(f"expected outer equations for {name}, found {count}")
    if name == "applyTyped":
        anchor = "      if h : p = p' ∧ D = D' then do"
        if region.count(anchor) != 1:
            raise ValueError("rule argument checking anchor changed")
        region = region.replace(anchor,
            f'      if h : p = p\' ∧ D = D\' then {TRACE} "{PREFIX}ruleArgument" fun _ => do')
    return text[:start] + region + text[end:]


def instrument(destination: Path) -> dict:
    edits = {}
    # The trace has the same pure definition and runtime behavior as Init.dbgTrace,
    # but is reducible from its declaration. Existing proof tactics can therefore
    # see through it without changing any Lean reducibility settings or axioms.
    helper = destination / "Ix/Kernel/DiagnosticTrace.lean"
    helper.write_text('''import Init.Util

namespace Ix.Kernel.Diagnostic

set_option linter.unusedVariables.funArgs false in
@[reducible, never_extract, implemented_by dbgTrace]
def trace {α : Type u} (message : String) (next : Unit → α) : α := next ()

end Ix.Kernel.Diagnostic
''')
    edits[str(helper.relative_to(destination))] = [None, hashlib.sha256(helper.read_bytes()).hexdigest()]
    operations = {
        "Ix/Kernel/Infer.lean": ["inferA", "whnf", "step", "applyTyped", "isDefEq", "spine"],
        "Ix/Kernel/Annotate.lean": ["annotate"],
        "Ix/Kernel/Model/Annotated.lean": ["liftN"],
    }
    for relative, names in operations.items():
        path = destination / relative
        original = path.read_text()
        text = original
        for name in names:
            text = equation_counter(text, name, name)
        at = text.index("\nimport ")
        text = text[:at] + "\nimport Ix.Kernel.DiagnosticTrace\n" + text[at:]
        path.write_text(text)
        edits[relative] = [hashlib.sha256(s.encode()).hexdigest() for s in [original, text]]
    replacements = {
        "Benchmarks/Kernel/Certified.lean": [
            ("  let start ← IO.monoNanosNow",
             f'  IO.eprintln "{PREFIX}begin"\n  let start ← IO.monoNanosNow'),
            ("  let stop ← IO.monoNanosNow",
             f'  let stop ← IO.monoNanosNow\n  IO.eprintln "{PREFIX}end"')],
        "Ix/Kernel/Certified/Checker.lean": [
            ("    Search (TypedSort.{u,v} entries Γ e) := do",
             f'    Search (TypedSort.{{u,v}} entries Γ e) := {TRACE} "{PREFIX}checkSort" fun _ => do')],
        "Ix/Kernel/Model/Context.lean": [
            ("  A.liftN 1 :: Γ.map (AExpr.liftN 1 ·)",
             f'  {TRACE} "{PREFIX}contextPush" fun _ =>\n  A.liftN 1 :: Γ.map (AExpr.liftN 1 ·)')],
        "Ix/Kernel/Env.lean": [
            ("  (env.entries.find? fun e => e.1 == r).map (·.2)",
             f'  {TRACE} "{PREFIX}lookup" fun _ =>\n'
             f'  (env.entries.find? fun e => {TRACE} "{PREFIX}keyComparison" fun _ => e.1 == r).map (·.2)')],
    }
    for relative, pairs in replacements.items():
        path = destination / relative
        original = path.read_text()
        text = original
        for before, after in pairs:
            if text.count(before) != 1:
                raise ValueError(f"instrumentation anchor changed: {relative}: {before}")
            text = text.replace(before, after)
        if relative != "Benchmarks/Kernel/Certified.lean":
            at = text.index("\nimport ")
            text = text[:at] + "\nimport Ix.Kernel.DiagnosticTrace\n" + text[at:]
        path.write_text(text)
        edits[relative] = [hashlib.sha256(s.encode()).hexdigest() for s in [original, text]]
    return edits


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=ROOT)
    parser.add_argument("--workdir", type=Path, required=True, help="new directory for the diagnostic copy")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--case", choices=list(CASES), action="append", dest="cases")
    parser.add_argument("--size", type=int)
    parser.add_argument("--fuel", type=int, default=100000)
    args = parser.parse_args()
    source, destination = args.source.resolve(), args.workdir.resolve()
    if destination.exists() or source in destination.parents or destination in source.parents:
        parser.error("workdir must be a new directory outside the source tree")
    if args.fuel < 0 or (args.size is not None and args.size < 0):
        parser.error("fuel and size must be nonnegative")
    revision = subprocess.run(["jj", "-R", str(source), "log", "-r", "@", "--no-graph", "-T", "commit_id"],
                              check=True, capture_output=True, text=True).stdout.strip()
    destination.mkdir(parents=True)
    for relative in ["Ix/Kernel", "Ix/Kernel.lean", "Ix/Address/Core.lean", "IxKernel/lakefile.lean",
                     "Tests/Ix/Kernel", "Benchmarks/Kernel/Certified.lean", "lean-toolchain"]:
        src, dst = source / relative, destination / relative
        dst.parent.mkdir(parents=True, exist_ok=True)
        if src.is_dir():
            shutil.copytree(src, dst)
        else:
            shutil.copy2(src, dst)
    digest = hashlib.sha256()
    for path in sorted(destination.rglob("*.lean")):
        digest.update(str(path.relative_to(destination)).encode() + b"\0" + path.read_bytes() + b"\0")
    edits = instrument(destination)
    with (destination / "build.log").open("w") as log:
        subprocess.run(["lake", "-d", "IxKernel", "build", "bench-certified-kernel"],
                       cwd=destination, stdout=log, stderr=subprocess.STDOUT, check=True)
    binary = destination / "IxKernel/.lake/build/bin/bench-certified-kernel"
    metadata = {"schema": 1, "backend": "Ix.Kernel/diagnostic", "revision": revision,
                "toolchain": (source / "lean-toolchain").read_text().strip(),
                "source_sha256": digest.hexdigest(),
                "instrumenter_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
                "instrumented_files_sha256_before_after": edits,
                "scope": "benchmark action only; excludes startup, preparation, and spine typing precheck",
                "timing": "discarded: tracing changes execution cost"}
    with args.output.open("w") as output:
        for case in args.cases or CASES:
            size = args.size if args.size is not None else CASES[case]
            process = subprocess.Popen([str(binary), case, str(size), str(args.fuel)], cwd=destination,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            counts = Counter()
            unexpected = []
            active = False
            boundaries = []
            for line in process.stderr:
                line = line.strip()
                if line in [PREFIX + "begin", PREFIX + "end"]:
                    boundaries.append(line)
                    active = line == PREFIX + "begin"
                elif line.startswith(PREFIX) and active:
                    counts[line[len(PREFIX):]] += 1
                elif not line.startswith(PREFIX) and len(unexpected) < 10:
                    unexpected.append(line)
            stdout = process.stdout.read().strip()
            code = process.wait()
            fields = stdout.split("\t")
            if code != 0 or unexpected or len(fields) != 6 or fields[:3] != [case, str(size), str(args.fuel)] \
                    or boundaries != [PREFIX + "begin", PREFIX + "end"]:
                raise RuntimeError(f"diagnostic failed: {code}, {stdout!r}, {unexpected!r}")
            if not counts:
                raise RuntimeError("no operation markers were emitted")
            record = {**metadata, "case": case, "size": size, "fuel": args.fuel,
                      "checksum": int(fields[4]), "lean": fields[5], "outcome": "accept",
                      "counts": dict(sorted(counts.items()))}
            output.write(json.dumps(record, sort_keys=True) + "\n")
            output.flush()
            print(case, size, record["counts"], flush=True)


if __name__ == "__main__":
    main()
