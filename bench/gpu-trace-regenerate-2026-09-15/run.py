#!/usr/bin/env python3
"""Compare CPU and GPU trace generation with one frozen CUDA prover binary."""

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time


ROOT = "6221602089142e7998ca8581617c70ae817e7bd68a8c0c510a67a1723a794024"
MODES = {"cpu": "cpu", "gpu": "blake3"}


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def stop(process):
    if process is None or process.poll() is not None:
        return
    os.killpg(process.pid, signal.SIGTERM)
    try:
        process.wait(timeout=15)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.wait()


def run_trial(args, mode, environment):
    directory = args.output / mode
    directory.mkdir()
    (directory / "cache").mkdir()
    settings = {
        "AIUR_GPU_TRACE": MODES[mode],
        "AIUR_LANES_CACHE_DIR": str(directory / "cache"),
    }
    command = [
        str(args.binary), "prove", "--ixe", str(args.fixture / "init.ixe"),
        "--ixes", str(args.fixture / "init-mincut-8.ixes"),
        "--trace-shards", "--lanes", "4", "--exec-jobs", "2", "--max-ram", "200",
    ]
    write_json(directory / "command.json", {"command": command, "environment": settings})
    result = {"mode": mode, "valid": False}
    print(f"Starting {mode} trace generation: {directory}", flush=True)
    process = monitor = None
    with (directory / "stdout.log").open("w") as stdout, \
            (directory / "stderr.log").open("w") as stderr, \
            (directory / "gpu.csv").open("w") as gpu, \
            (directory / "gpu-monitor.err").open("w") as monitor_errors:
        try:
            monitor = subprocess.Popen([
                "nvidia-smi",
                "--query-gpu=timestamp,index,memory.used,utilization.gpu,power.draw",
                "--format=csv,noheader,nounits", "--loop-ms=1000",
            ], stdout=gpu, stderr=monitor_errors, start_new_session=True)
            started = time.monotonic()
            process = subprocess.Popen([
                "/usr/bin/time", "-v", "-o", str(directory / "time.txt"), *command,
            ], env=dict(environment, **settings), cwd=directory, stdout=stdout,
                stderr=stderr, start_new_session=True)
            result["returncode"] = process.wait(timeout=args.timeout)
            result["wall_seconds"] = time.monotonic() - started
        except subprocess.TimeoutExpired:
            result["error"] = f"trial exceeded {args.timeout} seconds"
        finally:
            stop(process)
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
        if result["returncode"] != 0 or not root or not cold or root[1] != ROOT:
            raise ValueError("expected eight fresh claims, seven fresh joins and the verified Init root")
        result.update(root=root[1], proving_seconds=int(root[2]))
        generated = re.findall(
            r"prepared GPU BLAKE3 trace.*?row_count=(\d+).*?seed_bytes=(\d+)", log,
        )
        result["generated_sources"] = len(generated)
        result["generated_rows"] = sum(int(row[0]) for row in generated)
        result["seed_preparation_bytes"] = sum(int(row[1]) for row in generated)
        paths = re.findall(r'main commitment path.*?path="(host_pcs|prepared)"', log)
        result["main_commit_paths"] = {name: paths.count(name) for name in ("host_pcs", "prepared")}
        if len(paths) != 182:
            raise ValueError(f"expected 182 main commitments across both rounds; observed {len(paths)}")
        if mode == "cpu" and (generated or result["main_commit_paths"]["prepared"]):
            raise ValueError("CPU trial unexpectedly used generated traces")
        if mode == "gpu" and (len(generated) != 120 or result["generated_rows"] != 110892480
                              or result["main_commit_paths"]["prepared"] == 0):
            raise ValueError("GPU trace generation differs from the reference workload")
        spills = re.findall(r"spilled active LDE.*?bytes=(\d+)", log)
        result["lde_spills"] = len(spills)
        result["lde_spilled_bytes"] = sum(map(int, spills))
        for line in (directory / "time.txt").read_text().splitlines():
            for label, key in (
                ("User time (seconds):", "user_seconds"),
                ("System time (seconds):", "system_seconds"),
                ("Maximum resident set size (kbytes):", "max_rss_kib"),
            ):
                if line.strip().startswith(label):
                    result[key] = float(line.split(label, 1)[1])
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
        result["valid"] = True
    except (ValueError, KeyError) as error:
        result["error"] = str(error)
    write_json(directory / "result.json", result)
    write_json(directory / "rows.json", {"Init-resident-four-gpu": {
        "status": "ok" if result["valid"] else "failed",
        "wall-seconds": result.get("wall_seconds"),
        "cpu-seconds": result.get("cpu_seconds"),
        "peak-rss": result.get("max_rss_kib", 0) * 1024,
    }})
    print(json.dumps(result), flush=True)
    if not result["valid"]:
        raise RuntimeError(f"invalid trial: {directory}: {result.get('error')}")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--fixture", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--mode", choices=MODES)
    parser.add_argument("--timeout", type=int, default=900)
    args = parser.parse_args()
    args.binary = args.binary.resolve(strict=True)
    args.fixture = args.fixture.resolve(strict=True)
    args.output = args.output.resolve()
    args.output.mkdir(parents=True)
    shutil.copy2(__file__, args.output / "run.py")
    settings = {
        "LC_ALL": "C",
        "AIUR_TRACE_ONLY_LOOKUPS": "1",
        "AIUR_MAX_PIECE_LOG_HEIGHT": "24",
        "AIUR_TRACE_SHARD_MAX_CELLS": "1500000000",
        "RUST_LOG": "aiur::gpu_trace=debug,multi_stark::cuda::witness=debug",
    }
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("AIUR_", "MULTI_STARK_", "RAYON_", "CUDA_"))}
    env.update(settings)
    modes = [args.mode] if args.mode else list(MODES)
    cgroup = Path("/proc/self/cgroup").read_text()
    scope = Path("/sys/fs/cgroup") / cgroup.strip().split(":", 2)[2].lstrip("/")
    metadata = {
        "schema": 1,
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "binary": {"path": str(args.binary), "sha256": digest(args.binary)},
        "fixtures": {name: digest(args.fixture / name) for name in ("init.ixe", "init-mincut-8.ixes")},
        "runner_sha256": digest(Path(__file__)),
        "environment": settings,
        "cpu_affinity": sorted(os.sched_getaffinity(0)),
        "gpus": subprocess.check_output([
            "nvidia-smi", "--query-gpu=index,uuid,name,memory.total,driver_version", "--format=csv",
        ], text=True),
        "kernel": os.uname().release,
        "modes": modes,
        "timeout_seconds": args.timeout,
        "cgroup": cgroup,
        "resource_limits": {name: (scope / name).read_text().strip()
                            for name in ("memory.max", "memory.swap.max") if (scope / name).exists()},
    }
    write_json(args.output / "metadata.json", metadata)
    results = []
    for mode in modes:
        results.append(run_trial(args, mode, env))
        write_json(args.output / "results.json", results)
    if len(results) == 2:
        cpu, gpu = results
        write_json(args.output / "comparison.json", {
            "wall_time_reduction_percent": (1 - gpu["wall_seconds"] / cpu["wall_seconds"]) * 100,
            "speedup_ratio": cpu["wall_seconds"] / gpu["wall_seconds"],
            "cpu_time_reduction_percent": (1 - gpu["cpu_seconds"] / cpu["cpu_seconds"]) * 100,
            "trials_per_mode": 1,
        })


if __name__ == "__main__":
    signal.signal(signal.SIGTERM, lambda signum, frame: sys.exit(128 + signum))
    main()
