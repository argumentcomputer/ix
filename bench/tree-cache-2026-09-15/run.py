#!/usr/bin/env python3
"""Measure backend overhead and Merkle retention on a frozen Init fixture."""

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import statistics
import subprocess
import time


CASES = ("old-regenerate", "fixed-regenerate", "fixed-trees")
STATS = (
    "admitted", "reused", "rejected_budget", "rejected_incompatible",
    "rejected_backend", "evicted_workspace", "evicted_explicit",
    "queued_bytes", "peak_queued_bytes", "lde_spills", "lde_spilled_bytes",
)


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def stop(process):
    if process.poll() is not None:
        return
    os.killpg(process.pid, signal.SIGTERM)
    try:
        process.wait(timeout=15)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.wait()


def parse_stats(log):
    batches = []
    for line in log.splitlines():
        if "tree cache summary" not in line:
            continue
        fields = dict(re.findall(r"\b(\w+)=(\d+)\b", line))
        if missing := set(STATS) - fields.keys():
            raise ValueError(f"incomplete cache summary: {sorted(missing)}")
        row = {key: int(fields[key]) for key in STATS}
        if row["queued_bytes"] != 0:
            raise ValueError("completed batch still has queued trees")
        completed = sum(row[key] for key in (
            "reused", "rejected_incompatible", "evicted_workspace", "evicted_explicit",
        ))
        if row["admitted"] != completed:
            raise ValueError(f"unaccounted checkpoint outcome: {row}")
        batches.append(row)
    return batches


def parse_time(path):
    values = {}
    for line in path.read_text().splitlines():
        for label, key in (
            ("User time (seconds):", "user_seconds"),
            ("System time (seconds):", "system_seconds"),
            ("Maximum resident set size (kbytes):", "max_rss_kib"),
        ):
            if line.strip().startswith(label):
                values[key] = float(line.split(label, 1)[1])
    return values


def run_trial(args, case, block, binary, environment):
    directory = args.output / f"{block:02}-{case}"
    directory.mkdir()
    (directory / "cache").mkdir()
    settings = {
        "AIUR_GPU_TRACE": "blake3",
        "AIUR_TREE_CACHE_BYTES": str(args.tree_budget_mib * 1024**2 if case == "fixed-trees" else 0),
        "AIUR_LANES_CACHE_DIR": str(directory / "cache"),
    }
    env = dict(environment, **settings)
    command = [
        str(binary), "prove", "--ixe", str(args.fixture / "init.ixe"),
        "--ixes", str(args.fixture / "init-mincut-8.ixes"),
        "--trace-shards", "--lanes", "4", "--exec-jobs", "2", "--max-ram", "200",
    ]
    write_json(directory / "command.json", {"command": command, "environment": settings})
    print(f"Starting block {block}, {case}: {directory}", flush=True)
    result = {"case": case, "block": block, "valid": False,
              "tree_budget_bytes": int(settings["AIUR_TREE_CACHE_BYTES"])}
    process = None
    monitor = None
    with (directory / "stdout.log").open("w") as stdout, \
            (directory / "stderr.log").open("w") as stderr, \
            (directory / "gpu.csv").open("w") as gpu, \
            (directory / "gpu-monitor.err").open("w") as gpu_errors:
        try:
            monitor = subprocess.Popen([
                "nvidia-smi",
                "--query-gpu=timestamp,index,memory.used,utilization.gpu,power.draw",
                "--format=csv,noheader,nounits", "--loop-ms=1000",
            ], stdout=gpu, stderr=gpu_errors, start_new_session=True)
            started = time.monotonic()
            process = subprocess.Popen([
                "/usr/bin/time", "-v", "-o", str(directory / "time.txt"), *command,
            ], env=env, cwd=directory, stdout=stdout, stderr=stderr, start_new_session=True)
            result["returncode"] = process.wait(timeout=args.timeout)
            result["wall_seconds"] = time.monotonic() - started
        except subprocess.TimeoutExpired:
            result["error"] = f"trial exceeded {args.timeout} seconds"
        finally:
            if process is not None:
                stop(process)
            if monitor is not None:
                stop(monitor)
            write_json(directory / "result.json", result)

    try:
        if "error" in result:
            raise ValueError(result["error"])
        log = (directory / "stderr.log").read_text()
        root = re.search(
            r"root ([0-9a-f]{64}) verified; composed verdict OK; end to end (\d+)s", log,
        )
        cold = re.search(
            r"8 claims \(0 reused from the index, 0 retired under cached joins"
            r"(?: without an indexed proof)?\), 7 joins \(0 cached\)", log,
        )
        if result["returncode"] != 0 or not root or not cold:
            raise ValueError("trial did not finish eight fresh claims and seven joins with a verified root")
        result["root"] = root[1]
        result["proving_seconds"] = int(root[2])
        if args.expected_root and result["root"] != args.expected_root:
            raise ValueError("verified root differs from the frozen fixture's reference")
        generated = re.findall(
            r"prepared GPU BLAKE3 trace.*?row_count=(\d+).*?seed_bytes=(\d+).*?main_bytes=(\d+)", log,
        )
        if not generated:
            raise ValueError("GPU trace generation was not observed")
        result["generated_sources"] = len(generated)
        result["generated_rows"] = sum(int(row[0]) for row in generated)
        result["seed_preparation_bytes"] = sum(int(row[1]) for row in generated)
        result.update(parse_time(directory / "time.txt"))
        result["cpu_seconds"] = result["user_seconds"] + result["system_seconds"]
        peaks = {}
        with (directory / "gpu.csv").open() as stream:
            for row in csv.reader(stream):
                if len(row) == 5 and row[1].strip().isdigit():
                    device = row[1].strip()
                    peaks[device] = max(peaks.get(device, 0), float(row[2]))
        if set(peaks) != {"0", "1", "2", "3"}:
            raise ValueError("missing GPU memory samples")
        result["sampled_peak_gpu_mib"] = peaks
        if case != "old-regenerate":
            batches = parse_stats(log)
            if not batches:
                raise ValueError("fixed backend did not emit cache statistics")
            if args.expected_batches is not None and len(batches) != args.expected_batches:
                raise ValueError("batch statistics count differs from the reference pilot")
            write_json(directory / "batches.json", batches)
            result["batches"] = len(batches)
            result["cache"] = {
                key: sum(row[key] for row in batches)
                for key in STATS if key not in ("queued_bytes", "peak_queued_bytes")
            }
            result["maximum_batch_cache_bytes"] = max(row["peak_queued_bytes"] for row in batches)
            if case == "fixed-trees" and result["cache"]["reused"] == 0:
                raise ValueError("cache trial had no reuse hits")
        result["valid"] = True
    except (ValueError, KeyError) as error:
        result["error"] = str(error)
    write_json(directory / "result.json", result)
    print(json.dumps(result), flush=True)
    if not result["valid"]:
        raise RuntimeError(f"invalid trial: {directory}: {result.get('error')}")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--old", type=Path, required=True)
    parser.add_argument("--fixed", type=Path, required=True)
    parser.add_argument("--fixture", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--case", choices=CASES)
    parser.add_argument("--tree-budget-mib", type=int, default=512,
                        help="per-batch allowance for fixed-trees (default: 512 MiB)")
    parser.add_argument("--blocks", type=int, default=3, choices=(1, 2, 3))
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--diagnostics", action="store_true")
    parser.add_argument("--expected-root")
    parser.add_argument("--expected-batches", type=int)
    args = parser.parse_args()
    if args.tree_budget_mib <= 0:
        parser.error("--tree-budget-mib must be positive")
    args.output = args.output.resolve()
    args.fixture = args.fixture.resolve(strict=True)
    args.old = args.old.resolve(strict=True)
    args.fixed = args.fixed.resolve(strict=True)
    args.output.mkdir(parents=True)
    shutil.copy2(__file__, args.output / "run.py")
    env = {
        key: value for key, value in os.environ.items()
        if not key.startswith(("AIUR_", "MULTI_STARK_", "RAYON_", "CUDA_"))
    }
    settings = {
        "LC_ALL": "C",
        "AIUR_TRACE_ONLY_LOOKUPS": "1",
        "AIUR_MAX_PIECE_LOG_HEIGHT": "24",
        "AIUR_TRACE_SHARD_MAX_CELLS": "1500000000",
        "RUST_LOG": "aiur::gpu_trace=debug,multi_stark::batch=debug",
    }
    if args.diagnostics:
        settings["RUST_LOG"] += ",multi_stark::cuda::witness=debug,multi_stark::tree_cache=debug"
    env.update(settings)
    orders = [CASES[index:] + CASES[:index] for index in range(args.blocks)]
    if args.case:
        orders = [(args.case,)]
    metadata = {
        "schema": 1,
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "binaries": {"old": {"path": str(args.old), "sha256": digest(args.old)},
                     "fixed": {"path": str(args.fixed), "sha256": digest(args.fixed)}},
        "fixtures": {name: digest(args.fixture / name) for name in ("init.ixe", "init-mincut-8.ixes")},
        "runner_sha256": digest(Path(__file__)),
        "environment": settings,
        "cpu_affinity": sorted(os.sched_getaffinity(0)),
        "kernel": os.uname().release,
        "gpus": subprocess.check_output([
            "nvidia-smi", "--query-gpu=index,uuid,name,memory.total,driver_version", "--format=csv",
        ], text=True),
        "orders": orders,
        "timeout_seconds": args.timeout,
        "tree_budget_bytes": args.tree_budget_mib * 1024**2,
        "diagnostic_pilot": args.diagnostics,
        "expected_root": args.expected_root,
        "expected_batches": args.expected_batches,
        "cgroup": Path("/proc/self/cgroup").read_text(),
    }
    write_json(args.output / "metadata.json", metadata)
    results = []
    for block, order in enumerate(orders, 1):
        for case in order:
            binary = args.old if case == "old-regenerate" else args.fixed
            results.append(run_trial(args, case, block, binary, env))
            if len({row["root"] for row in results}) != 1:
                raise RuntimeError("verified roots differ between trials")
            if len({(row["generated_sources"], row["generated_rows"]) for row in results}) != 1:
                raise RuntimeError("generated workload differs between trials")
            write_json(args.output / "results.json", results)
    summary = {}
    for case in CASES:
        rows = [row for row in results if row["case"] == case]
        if not rows:
            continue
        values = [row["wall_seconds"] for row in rows]
        summary[case] = {"trials": len(rows), "wall_seconds": values,
                         "median_seconds": statistics.median(values),
                         "min_seconds": min(values), "max_seconds": max(values)}
    write_json(args.output / "summary.json", summary)
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
