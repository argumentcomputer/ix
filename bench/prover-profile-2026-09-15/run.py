"""Profile one cached join, or one claim, with bounded CPU affinity."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / "target/prover-profile-build"
DATA = Path("/home/sam/benchdata/mathlib-gpu")


def gpu_processes(device):
    result = subprocess.check_output(["nvidia-smi", f"--id={device}",
        "--query-compute-apps=pid", "--format=csv,noheader,nounits"], text=True)
    return {int(line) for line in result.splitlines() if line.strip()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("kind", choices=["join", "claim"])
    parser.add_argument("index", type=int)
    parser.add_argument("--label", required=True)
    parser.add_argument("--cpus", type=int, default=24)
    parser.add_argument("--device", type=int, default=0)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--no-cupti", action="store_true")
    parser.add_argument("--binary", type=Path, default=BUILD / "ix-profile")
    parser.add_argument("--output-root", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    busy = gpu_processes(args.device)
    if busy:
        raise SystemExit(f"GPU {args.device} is in use by {sorted(busy)}; refusing a contended profile")
    out = args.output_root.resolve() / args.label
    out.mkdir(exist_ok=False)
    binary = args.binary.resolve()
    settings = {
        "CUDA_VISIBLE_DEVICES": str(args.device), "AIUR_GPU_TRACE": "blake3",
        "AIUR_TRACE_ONLY_LOOKUPS": "1", "AIUR_MAX_PIECE_LOG_HEIGHT": "24",
        "AIUR_TRACE_SHARD_MAX_CELLS": "1500000000", "AIUR_TREE_CACHE_BYTES": "0",
        "RAYON_NUM_THREADS": str(args.cpus), "LEAN_NUM_THREADS": str(args.cpus),
        "AIUR_PROFILE": str(out / "spans.jsonl"),
        "AIUR_AGGREGATE_CACHE_DIR": str(DATA / "mathlib78-gpu-shared/cache/aggregate"),
    }
    if not args.no_cupti:
        settings.update(AIUR_CUDA_PROFILE=str(out / "cuda.jsonl"),
                        CUDA_INJECTION64_PATH=str(BUILD / "libcupti_trace.so"))
    command = [str(binary), "aggregate" if args.kind == "join" else "prove",
               "--ixe", str(DATA / "mathlib.ixe"), "--ixes", str(DATA / "mathlib-78.ixes"),
               "--trace-shards", "--max-ram", "230"]
    if args.kind == "join":
        command += ["--direct-joins", "--jobs", "1", "--no-write", "--reprove-slot", str(args.index)]
    else:
        command += ["--shard", str(args.index), "--no-index", "--texray"]
    affinity = sorted(os.sched_getaffinity(0))[-args.cpus:]
    def configure_child():
        os.sched_setaffinity(0, affinity)
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    with binary.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    with (BUILD / "libcupti_trace.so").open("rb") as stream:
        collector_digest = hashlib.file_digest(stream, "sha256").hexdigest()
    metadata = {"command": command, "environment": settings, "cpu_affinity": affinity,
                "collector_sha256": collector_digest,
                "binary_sha256": digest, "started_ns": time.time_ns()}
    (out / "meta.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print("Running", args.kind, args.index, "on GPU", args.device, "and", len(affinity), "CPU cores", flush=True)
    with (out / "stdout").open("w") as stdout, (out / "stderr").open("w") as stderr, \
            (out / "gpu.csv").open("w") as gpu:
        monitor = subprocess.Popen(["nvidia-smi", f"--id={args.device}",
            "--query-gpu=timestamp,index,memory.used,utilization.gpu,power.draw",
            "--format=csv,noheader,nounits", "--loop-ms=200"], stdout=gpu, stderr=subprocess.DEVNULL)
        process = None
        stop_watcher = threading.Event()
        watcher = None
        try:
            process = subprocess.Popen(["/usr/bin/time", "-v", *command], env=dict(os.environ, **settings),
                stdout=stdout, stderr=stderr, start_new_session=True,
                preexec_fn=configure_child)
            metadata["pid"] = process.pid
            def check_contention():
                while not stop_watcher.wait(1):
                    try:
                        foreign = []
                        for pid in gpu_processes(args.device):
                            try:
                                if os.getpgid(pid) != process.pid:
                                    foreign.append(pid)
                            except ProcessLookupError:
                                pass
                        if foreign and process.poll() is None:
                            metadata["aborted_for_contention"] = foreign
                            print("Stopping profile: another process is using the GPU:", foreign, flush=True)
                            os.killpg(process.pid, signal.SIGTERM)
                            return
                    except (OSError, subprocess.CalledProcessError) as error:
                        metadata["watcher_error"] = str(error)
                        if process.poll() is None:
                            os.killpg(process.pid, signal.SIGTERM)
                        return
            watcher = threading.Thread(target=check_contention, daemon=True)
            watcher.start()
            (out / "meta.json").write_text(json.dumps(metadata, indent=2) + "\n")
            metadata["exit_code"] = process.wait(timeout=args.timeout)
        finally:
            stop_watcher.set()
            if watcher is not None:
                watcher.join(timeout=5)
            if process is not None and process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                metadata["killed"] = True
            monitor.terminate()
            try:
                monitor.wait(timeout=5)
            except subprocess.TimeoutExpired:
                monitor.kill()
                monitor.wait()
            metadata["finished_ns"] = time.time_ns()
            (out / "meta.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print("Finished:", out, "exit", metadata.get("exit_code"), flush=True)
    raise SystemExit(metadata.get("exit_code", 1))


if __name__ == "__main__":
    main()
