#!/usr/bin/env python3
"""Alternate native environment-check runs and compare coverage separately from timing.

The environment check measures supported-profile coverage, not a checkEnv verdict. Run
under a memory cap and without concurrent builds or benchmark processes.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import signal
import statistics
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
OUTCOMES = {"accept", "decline", "reject", "blocked"}


def sha256(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def source_fingerprint(root: Path) -> str:
    """Hash local Lean sources and build pins; this does not verify a build."""
    paths = [root / name for name in
             ("Ix.lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain")]
    for directory in ("Ix", "Benchmarks/Kernel"):
        paths.extend((root / directory).rglob("*.lean"))
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(str(path.relative_to(root)).encode() + b"\0")
        digest.update(path.read_bytes() + b"\0")
    return digest.hexdigest()


def read_rows(path: Path) -> dict[str, dict]:
    rows = {}
    with path.open() as handle:
        for line_number, line in enumerate(handle, 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
                address = row["address"]
                if not isinstance(address, str) or not address:
                    raise ValueError("missing address")
                if address in rows:
                    raise ValueError(f"duplicate address {address}")
                if row["outcome"] not in OUTCOMES:
                    raise ValueError(f"unknown outcome {row['outcome']!r}")
                if not isinstance(row["reason"], str):
                    raise ValueError("reason must be a string")
                if not isinstance(row["names"], list) or not all(
                        isinstance(name, str) for name in row["names"]):
                    raise ValueError("names must be an array of strings")
                for field in ("micros", "readMicros"):
                    value = row[field] if field == "micros" else row.get(field, 0)
                    if type(value) is not int or value < 0:
                        raise ValueError(f"invalid {field}")
                rows[address] = row
            except (KeyError, TypeError, ValueError) as error:
                raise ValueError(f"{path}:{line_number}: {error}") from error
    if not rows:
        raise ValueError(f"{path}: no check rows")
    return rows


def row_summary(rows: dict[str, dict]) -> dict:
    return {
        "records": len(rows),
        "outcomes": dict(sorted(Counter(row["outcome"] for row in rows.values()).items())),
    }


def compare(before: dict[str, dict], after: dict[str, dict], top: int) -> dict:
    shared = before.keys() & after.keys()
    common_accepts = sorted(address for address in shared
                            if before[address]["outcome"] == after[address]["outcome"] == "accept")

    def change(address: str) -> dict:
        old, new = before.get(address), after.get(address)
        return {
            "address": address, "names": (new or old)["names"],
            "before": {field: old[field] for field in ("outcome", "reason")} if old else None,
            "after": {field: new[field] for field in ("outcome", "reason")} if new else None,
        }

    lost = sorted(address for address, row in before.items()
                  if row["outcome"] == "accept" and
                  (address not in after or after[address]["outcome"] != "accept"))
    gained = sorted(address for address, row in after.items()
                    if row["outcome"] == "accept" and
                    (address not in before or before[address]["outcome"] != "accept"))
    before_micros = sum(before[address]["micros"] for address in common_accepts)
    after_micros = sum(after[address]["micros"] for address in common_accepts)
    slowest = sorted(common_accepts, key=lambda address: (-after[address]["micros"], address))[:top]
    return {
        "baseline": row_summary(before), "current": row_summary(after),
        "transitions": dict(sorted(Counter(
            f"{before[address]['outcome']} -> {after[address]['outcome']}"
            for address in shared).items())),
        "baseline_only": [change(address) for address in sorted(before.keys() - after.keys())],
        "current_only": [change(address) for address in sorted(after.keys() - before.keys())],
        "lost_accepts": [change(address) for address in lost],
        "gained_accepts": [change(address) for address in gained],
        "changed_diagnostics": [change(address) for address in sorted(shared)
                                if before[address]["outcome"] == after[address]["outcome"]
                                and before[address]["reason"] != after[address]["reason"]],
        "common_accepted_records": len(common_accepts),
        "common_accepted_row_micros": {"baseline": before_micros, "current": after_micros},
        "common_accepted_row_ratio": after_micros / before_micros if before_micros else None,
        "timing_scope": "row diagnostics; family/recursor rows duplicate admission timings; not wall time",
        "slowest_common_accepts": [{
            "address": address, "names": after[address]["names"],
            "baseline_micros": before[address]["micros"], "current_micros": after[address]["micros"],
        } for address in slowest],
    }


def write_json(path: Path, value: dict) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def sample(binary: Path, timer: str, args: argparse.Namespace, stem: Path) -> dict:
    rows_path, log_path, metrics_path = (stem.with_suffix(suffix)
                                         for suffix in (".jsonl", ".log", ".resources"))
    command = [timer, "-q", "-f", "%M %U %S", "-o", str(metrics_path),
               str(binary), str(args.input), str(rows_path), str(args.limit), str(args.fuel)]
    # These diagnostic modes alter the checked population or timing behavior.
    environment = {key: value for key, value in os.environ.items() if not key.startswith("CHECK_IXE_")}
    started = time.monotonic_ns()
    timed_out = False
    with log_path.open("w") as log:
        process = subprocess.Popen(command, stdout=log, stderr=log, env=environment,
                                   start_new_session=True)
        try:
            process.wait(timeout=args.timeout)
        except (subprocess.TimeoutExpired, KeyboardInterrupt) as error:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            if isinstance(error, KeyboardInterrupt):
                raise
            timed_out = True
    result = {
        "rows": str(rows_path), "log": str(log_path), "exit_code": process.returncode,
        "timed_out": timed_out, "wall_ns": time.monotonic_ns() - started,
    }
    try:
        rss, user, system = metrics_path.read_text().split()
        result.update(peak_rss_kib=int(rss), user_seconds=float(user), system_seconds=float(system))
    except (OSError, ValueError) as error:
        result["resources_error"] = str(error)
    try:
        rows = read_rows(rows_path)
        result.update(row_summary(rows), rows_sha256=sha256(rows_path))
    except (OSError, ValueError) as error:
        result["rows_error"] = str(error)
    return result


def run(args: argparse.Namespace) -> int:
    args.output_dir.mkdir(parents=True, exist_ok=False)
    summary_path = args.output_dir / "summary.json"
    binaries = {"baseline": args.baseline_binary.resolve(), "current": args.binary.resolve()}
    timer = args.time_binary or shutil.which("time")
    if not timer:
        raise ValueError("GNU time is required (or pass --time-binary)")
    report = {
        "schema": 1, "completed": False,
        "scope": "environment-check supported-profile coverage; not a certified whole-environment verdict",
        "input": {"path": str(args.input), "sha256": sha256(args.input)},
        "source_sha256": source_fingerprint(args.source),
        "source_note": "local source at invocation; caller must build the binary from this source",
        "baseline_source_sha256": args.baseline_source_sha256,
        "toolchain": (args.source / "lean-toolchain").read_text().strip(),
        "runner_sha256": sha256(Path(__file__)),
        "machine": platform.uname()._asdict(),
        "limit": args.limit, "fuel": args.fuel, "runs": args.runs, "warmups": args.warmups,
        "timeout_seconds": args.timeout,
        "binaries": {side: {"path": str(path), "sha256": sha256(path),
                             "revision": args.baseline_revision if side == "baseline" else args.revision}
                     for side, path in binaries.items()},
        "samples": [], "pairs": [],
    }
    write_json(summary_path, report)
    signatures = {}
    for index in range(args.warmups + args.runs):
        warmup = index < args.warmups
        order = ["baseline", "current"] if index % 2 == 0 else ["current", "baseline"]
        paired = {}
        for side in order:
            stem = args.output_dir / f"{index:02d}-{'warmup' if warmup else 'sample'}-{side}"
            result = sample(binaries[side], timer, args, stem)
            result.update(side=side, warmup=warmup)
            report["samples"].append(result)
            write_json(summary_path, report)
            print(f"{side} {'warmup' if warmup else 'sample'}: exit {result['exit_code']}, "
                  f"{result['wall_ns'] / 1e9:.3f} s, {result.get('outcomes', {})}", flush=True)
            if result["timed_out"] or result["exit_code"] != 0 or any(
                    field in result for field in ("rows_error", "resources_error")):
                print(f"Incomplete run; retained evidence at {summary_path}", file=sys.stderr)
                return 1
            rows = read_rows(Path(result["rows"]))
            signature = {address: (row["outcome"], row["reason"]) for address, row in rows.items()}
            if side in signatures and signatures[side] != signature:
                report["error"] = f"{side} coverage or diagnostics changed between samples"
                write_json(summary_path, report)
                return 1
            signatures[side] = signature
            paired[side] = rows
        if not warmup:
            report["pairs"].append(compare(paired["baseline"], paired["current"], args.top))
            write_json(summary_path, report)
    for side, binary in binaries.items():
        if sha256(binary) != report["binaries"][side]["sha256"]:
            raise ValueError(f"{side} binary changed during the run")
    if sha256(args.input) != report["input"]["sha256"] or source_fingerprint(args.source) != report["source_sha256"]:
        raise ValueError("input or source changed during the run")
    report["wall"] = {}
    for side in binaries:
        measured = [sample for sample in report["samples"] if sample["side"] == side and not sample["warmup"]]
        wall = [sample["wall_ns"] for sample in measured]
        report["wall"][side] = {"median_ns": statistics.median(wall), "min_ns": min(wall), "max_ns": max(wall),
                                "peak_rss_kib": max(sample["peak_rss_kib"] for sample in measured)}
    same_coverage = ({address: outcome for address, (outcome, _) in signatures["baseline"].items()} ==
                     {address: outcome for address, (outcome, _) in signatures["current"].items()})
    report["identical_outcomes"] = same_coverage
    report["identical_outcomes_and_diagnostics"] = signatures["baseline"] == signatures["current"]
    report["wall_current_over_baseline"] = (report["wall"]["current"]["median_ns"] /
                                             report["wall"]["baseline"]["median_ns"])
    report["wall_comparison_note"] = ("identical coverage" if same_coverage else
                                       "coverage differs; inspect transitions before comparing wall times")
    report["completed"] = True
    write_json(summary_path, report)
    print(summary_path)
    return 1 if any(pair["lost_accepts"] for pair in report["pairs"]) else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    comparison = commands.add_parser("compare", help="compare existing rows, including partial runs")
    comparison.add_argument("baseline", type=Path)
    comparison.add_argument("current", type=Path)
    comparison.add_argument("--output", type=Path)
    comparison.add_argument("--top", type=int, default=15)
    benchmark = commands.add_parser("run", help="run alternating baseline/current fresh processes")
    benchmark.add_argument("--binary", type=Path, required=True)
    benchmark.add_argument("--baseline-binary", type=Path, required=True)
    benchmark.add_argument("--input", type=Path, required=True)
    benchmark.add_argument("--output-dir", type=Path, required=True, help="new directory for all evidence")
    benchmark.add_argument("--source", type=Path, default=ROOT)
    benchmark.add_argument("--revision", help="explicit revision used to build current binary")
    benchmark.add_argument("--baseline-revision", required=True)
    benchmark.add_argument("--baseline-source-sha256")
    benchmark.add_argument("--limit", type=int, default=4300, help="primary-record prefix (default: 4300)")
    benchmark.add_argument("--fuel", type=int, default=100000)
    benchmark.add_argument("--runs", type=int, default=3)
    benchmark.add_argument("--warmups", type=int, default=1)
    benchmark.add_argument("--timeout", type=float, default=180)
    benchmark.add_argument("--time-binary", help="path to GNU time")
    benchmark.add_argument("--top", type=int, default=15)
    args = parser.parse_args()
    if args.top < 0:
        parser.error("top must be nonnegative")
    try:
        if args.command == "compare":
            result = compare(read_rows(args.baseline), read_rows(args.current), args.top)
            result["completion_note"] = "standalone rows do not establish whether either process completed"
            if args.output:
                write_json(args.output, result)
            else:
                print(json.dumps(result, indent=2, sort_keys=True))
            return 1 if result["lost_accepts"] else 0
        if min(args.limit, args.runs) < 1 or min(args.fuel, args.warmups) < 0 or args.timeout <= 0:
            parser.error("limit/runs/timeout must be positive; fuel/warmups must be nonnegative")
        args.input, args.output_dir, args.source = args.input.resolve(), args.output_dir.resolve(), args.source.resolve()
        return run(args)
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
