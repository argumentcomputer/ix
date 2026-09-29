#!/usr/bin/env python3
"""Run native Ix.Kernel probes with isolated samples and peak process RSS.

Build with `lake -d IxKernel build --wfail bench-certified-kernel` first.
The native timer excludes input construction; process RSS includes setup.
No timing assertion is used as a correctness gate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
CASES = {
    "env": [1000, 2000, 4000, 8000],
    "address": [1000, 2000, 4000, 8000],
    "references": [1000, 2000, 4000, 8000],
    "binders": [16, 32, 64, 128],
    "beta": [16, 32, 64, 128],
    "context": [1000, 2000, 4000, 8000],
    "spine": [400, 800, 1600, 3200],
    "ordinary": [1, 4, 16],
    "structure": [1, 4, 16],
    "quotient": [1, 4, 16],
}


def fingerprint() -> str:
    digest = hashlib.sha256()
    paths = [ROOT / "Ix/Kernel.lean", ROOT / "Ix/Address/Core.lean",
             ROOT / "IxKernel/lakefile.lean", Path(__file__).resolve()]
    for directory in ["Ix/Kernel", "Tests/Ix/Kernel", "Benchmarks/Kernel"]:
        paths.extend((ROOT / directory).rglob("*.lean"))
    for path in sorted(paths):
        digest.update(str(path.relative_to(ROOT)).encode())
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def revision() -> str:
    result = subprocess.run(
        ["jj", "log", "-r", "@", "--no-graph", "-T", "commit_id"],
        cwd=ROOT, capture_output=True, text=True, check=True,
    )
    return result.stdout.strip()


def sample(binary: Path, timer: str, kind: str, size: int, fuel: int, timeout: float) -> dict:
    with tempfile.TemporaryDirectory(prefix="ix-kernel-bench-") as temporary:
        rss_path = Path(temporary) / "rss"
        result = subprocess.run(
            [timer, "-f", "%M", "-o", str(rss_path), str(binary), kind, str(size), str(fuel)],
            cwd=ROOT, capture_output=True, text=True, timeout=timeout, check=True,
        )
        fields = result.stdout.strip().split("\t")
        if len(fields) != 6 or fields[:3] != [kind, str(size), str(fuel)]:
            raise ValueError(f"unexpected benchmark output: {result.stdout!r}")
        return {
            "elapsed_ns": int(fields[3]), "checksum": int(fields[4]),
            "lean": fields[5], "peak_rss_kib": int(rss_path.read_text().strip()),
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=list(CASES), action="append", dest="cases")
    parser.add_argument("--size", type=int, action="append", dest="sizes")
    parser.add_argument("--fuel", type=int, default=100000)
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument("--timeout", type=float, default=180)
    parser.add_argument("--binary", type=Path, default=ROOT / "IxKernel/.lake/build/bin/bench-certified-kernel")
    parser.add_argument("--baseline-binary", type=Path, help="alternate samples with this uninstrumented baseline")
    parser.add_argument("--baseline-revision", help="revision used to build the baseline binary")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.runs < 1 or args.fuel < 0 or any(n < 0 for n in args.sizes or []):
        parser.error("runs must be positive; sizes and fuel must be nonnegative")
    binary = args.binary.resolve()
    if not binary.is_file():
        parser.error(f"build bench-certified-kernel first: {binary}")
    if bool(args.baseline_binary) != bool(args.baseline_revision):
        parser.error("baseline-binary and baseline-revision must be supplied together")
    baseline = args.baseline_binary.resolve() if args.baseline_binary else None
    if baseline and not baseline.is_file():
        parser.error(f"baseline binary does not exist: {baseline}")
    timer = shutil.which("time")
    if timer is None:
        parser.error("GNU time is required to measure each process's peak RSS")
    metadata = {
        "schema": 1, "backend": "Ix.Kernel/native", "revision": revision(),
        "source_sha256": fingerprint(), "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "machine": os.uname().machine, "runs": args.runs, "warmups": 1,
        "rss_scope": "whole process, including untimed fixture preparation",
    }
    baseline_metadata = {
        "revision": args.baseline_revision,
        "binary_sha256": hashlib.sha256(baseline.read_bytes()).hexdigest(),
    } if baseline else None
    output = args.output.open("w") if args.output else None
    try:
        for kind in args.cases or CASES:
            for size in args.sizes or CASES[kind]:
                sample(binary, timer, kind, size, args.fuel, args.timeout)
                if baseline:
                    sample(baseline, timer, kind, size, args.fuel, args.timeout)
                samples, baseline_samples = [], []
                for i in range(args.runs):
                    pair = [(binary, samples)]
                    if baseline:
                        pair.append((baseline, baseline_samples))
                        if i % 2 == 0:
                            pair.reverse()
                    for path, rows in pair:
                        rows.append(sample(path, timer, kind, size, args.fuel, args.timeout))
                if len({(s["checksum"], s["lean"]) for s in samples}) != 1:
                    raise ValueError("inconsistent results across benchmark samples")
                elapsed = [s["elapsed_ns"] for s in samples]
                record = {
                    **metadata, "case": kind, "size": size, "fuel": args.fuel,
                    "outcome": "accept", "median_ns": statistics.median(elapsed),
                    "min_ns": min(elapsed), "max_ns": max(elapsed),
                    "peak_rss_kib": max(s["peak_rss_kib"] for s in samples),
                    "samples": samples,
                }
                if baseline:
                    if {(s["checksum"], s["lean"]) for s in baseline_samples} != \
                            {(s["checksum"], s["lean"]) for s in samples}:
                        raise ValueError("baseline/current outcomes or Lean versions differ")
                    before = [s["elapsed_ns"] for s in baseline_samples]
                    record["sampling"] = "alternating before/after pairs in fresh processes"
                    record["baseline"] = {
                        **baseline_metadata, "outcome": "accept", "samples": baseline_samples,
                        "median_ns": statistics.median(before), "min_ns": min(before), "max_ns": max(before),
                        "peak_rss_kib": max(s["peak_rss_kib"] for s in baseline_samples),
                    }
                    record["current_over_baseline"] = record["median_ns"] / record["baseline"]["median_ns"]
                line = json.dumps(record, sort_keys=True)
                print(line, flush=True)
                if output:
                    output.write(line + "\n")
                    output.flush()
    finally:
        if output:
            output.close()


if __name__ == "__main__":
    main()
