#!/usr/bin/env python3
"""Compare trace providers on the fixed eight-claim Init fixture."""

import argparse
import csv
import hashlib
import json
import mmap
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time


CASES = {
    "cpu": ("cpu", False),
    "gpu": ("blake3", False),
    "gpu-trees": ("blake3", True),
}


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def stop(process):
    if process.poll() is None:
        os.killpg(process.pid, signal.SIGTERM)
        try:
            process.wait(timeout=15)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()


def run_case(name, binary, fixture, output, budget):
    provider, retain = CASES[name]
    directory = output / name
    directory.mkdir()
    cache = directory / "cache"
    cache.mkdir()
    env = os.environ.copy()
    for key in (
        "RAYON_NUM_THREADS", "CUDA_VISIBLE_DEVICES",
        "MULTI_STARK_CUDA_STAGE1_THREADS", "MULTI_STARK_CUDA_LOOKUP_THREADS",
        "MULTI_STARK_CUDA_DEFERRED_THREADS", "MULTI_STARK_CUDA_TRACE_FORCE_SPILL",
        "MULTI_STARK_CUDA_LOOKUP_TRACE_TILE_ROWS",
    ):
        env.pop(key, None)
    settings = {
        "LC_ALL": "C",
        "AIUR_TRACE_ONLY_LOOKUPS": "1",
        "AIUR_MAX_PIECE_LOG_HEIGHT": "24",
        "AIUR_TRACE_SHARD_MAX_CELLS": "1500000000",
        "AIUR_GPU_TRACE": provider,
        "AIUR_TREE_CACHE_BYTES": str(budget if retain else 0),
        "AIUR_LANES_CACHE_DIR": str(cache),
        "RUST_LOG": "aiur::gpu_trace=debug,multi_stark::cuda::witness=debug,multi_stark::batch=debug",
    }
    env.update(settings)
    command = [
        str(binary), "prove", "--ixe", str(fixture / "init.ixe"),
        "--ixes", str(fixture / "init-mincut-8.ixes"),
        "--trace-shards", "--lanes", "4", "--exec-jobs", "2", "--max-ram", "200",
    ]
    (directory / "command.json").write_text(json.dumps({
        "command": command, "environment": settings,
    }, indent=2) + "\n")
    print(f"Starting {name}: {directory}", flush=True)
    with (directory / "gpu.csv").open("w") as gpu, \
            (directory / "gpu-monitor.err").open("w") as gpu_errors, \
            (directory / "stdout.log").open("w") as stdout, \
            (directory / "stderr.log").open("w") as stderr:
        monitor = subprocess.Popen([
            "nvidia-smi",
            "--query-gpu=timestamp,index,memory.used,utilization.gpu,power.draw",
            "--format=csv,noheader,nounits", "--loop-ms=1000",
        ], stdout=gpu, stderr=gpu_errors, start_new_session=True)
        process = None
        started = time.monotonic()
        try:
            process = subprocess.Popen([
                "/usr/bin/time", "-v", "-o", str(directory / "time.txt"),
                *command,
            ], env=env, cwd=directory, stdout=stdout, stderr=stderr,
                start_new_session=True)
            returncode = process.wait()
        finally:
            if process is not None:
                stop(process)
            stop(monitor)
        elapsed = time.monotonic() - started

    log = (directory / "stderr.log").read_text()
    timing = (directory / "time.txt").read_text()
    verified = re.search(r"root ([0-9a-f]{64}) verified; composed verdict OK; end to end (\d+)s", log)
    cold = re.search(
        r"8 claims \(0 reused from the index, 0 retired under cached joins"
        r"(?: without an indexed proof)?\), 7 joins \(0 cached\)", log,
    ) is not None
    rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", timing)
    wall = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)", timing)
    seconds = 0.0
    if wall:
        for part in wall[1].split(":"):
            seconds = seconds * 60 + float(part)
    generated = re.findall(r"prepared GPU BLAKE3 trace.*?row_count=(\d+).*?seed_bytes=(\d+).*?main_bytes=(\d+)", log)
    peaks = {}
    with (directory / "gpu.csv").open() as stream:
        for row in csv.reader(stream):
            if len(row) == 5 and row[1].strip().isdigit():
                device = row[1].strip()
                peaks[device] = max(peaks.get(device, 0), float(row[2]))
    result = {
        "case": name, "returncode": returncode,
        "wall_seconds": seconds if wall else elapsed, "harness_seconds": elapsed,
        "root": verified[1] if verified else None,
        "proving_seconds": int(verified[2]) if verified else None,
        "cold_proof_cache": cold,
        "max_rss_gib": int(rss[1]) / 2**20 if rss else None,
        "peak_gpu_mib": peaks,
        "generated_shard_sources": len(generated),
        "generated_rows": sum(int(item[0]) for item in generated),
        "compact_seed_bytes": sum(int(item[1]) for item in generated),
        "replaced_host_trace_bytes": sum(int(item[2]) for item in generated),
        "tree_checkpoints": log.count("retained stage-one Merkle tree"),
        "tree_reuses": log.count("reused stage-one Merkle tree"),
        "tree_evictions": log.count("evicted stage-one tree checkpoint"),
    }
    (directory / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result), flush=True)
    if returncode != 0 or not verified or not cold:
        raise RuntimeError(f"{name} did not complete a fresh verified Init proof")
    if provider == "blake3" and not generated:
        raise RuntimeError(f"{name} did not report GPU BLAKE3 dispatch")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ix", type=Path, required=True)
    parser.add_argument("--fixture-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--case", choices=CASES, action="append")
    parser.add_argument("--tree-budget", type=int, default=536870912)
    args = parser.parse_args()
    source = args.ix.resolve(strict=True)
    fixture = args.fixture_dir.resolve(strict=True)
    with source.open("rb") as stream, mmap.mmap(stream.fileno(), 0, access=mmap.ACCESS_READ) as data:
        for marker in (b"AIUR_GPU_TRACE", b"AIUR_TREE_CACHE_BYTES", b"AIUR_LANES_CACHE_DIR"):
            if data.find(marker) < 0:
                raise RuntimeError(f"binary lacks {marker.decode()}; a current CUDA build is required")
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    binary = output / "ix"
    if binary.exists():
        if digest(binary) != digest(source):
            raise RuntimeError("the output directory contains a different binary")
    else:
        shutil.copy2(source, binary)
    metadata = {
        "binary_sha256": digest(binary),
        "fixtures": {name: digest(fixture / name) for name in ("init.ixe", "init-mincut-8.ixes")},
        "available_cpus": len(os.sched_getaffinity(0)),
        "utc_started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    if not (output / "metadata.json").exists():
        (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    for name in (args.case or list(CASES)):
        run_case(name, binary, fixture, output, args.tree_budget)
    results = [json.loads(path.read_text()) for name in CASES
               if (path := output / name / "result.json").exists()]
    if len({result["root"] for result in results}) != 1:
        raise RuntimeError("providers produced different verified root addresses")
    (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
