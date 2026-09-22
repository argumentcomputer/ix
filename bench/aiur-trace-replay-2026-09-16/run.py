"""Replay one cached aggregate slot with a selected trace provider."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--mode', choices=['blake3', 'generated'], required=True)
    parser.add_argument('--ixe', type=Path, required=True)
    parser.add_argument('--ixes', type=Path, required=True)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--slot', type=int, default=33)
    parser.add_argument('--structural-above', type=int, default=4096)
    parser.add_argument('--device', type=int, default=3)
    args = parser.parse_args()
    os.sched_setaffinity(0, set(range(8)))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    busy = subprocess.check_output([
        'nvidia-smi', f'--id={args.device}', '--query-compute-apps=pid',
        '--format=csv,noheader,nounits'], text=True).strip()
    if busy:
        raise SystemExit(f'GPU {args.device} is occupied by: {busy}')
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    settings = {
        'CUDA_VISIBLE_DEVICES': str(args.device), 'AIUR_GPU_TRACE': args.mode,
        'RAYON_NUM_THREADS': '8', 'OMP_NUM_THREADS': '8', 'LEAN_NUM_THREADS': '8',
        'AIUR_TRACE_ONLY_LOOKUPS': '1', 'AIUR_MAX_PIECE_LOG_HEIGHT': '24',
        'AIUR_TRACE_SHARD_MAX_CELLS': '1500000000', 'AIUR_TREE_CACHE_BYTES': '0',
        'AIUR_AGGREGATE_CACHE_DIR': str(args.cache.resolve()),
        'AIUR_PROFILE': str(out / 'spans.jsonl'),
        'RUST_LOG': 'aiur::gpu_trace=debug,aiur::trace_codegen=debug',
    }
    env = dict(os.environ)
    for key in ['AIUR_CUDA_PROFILE', 'CUDA_INJECTION64_PATH', 'LD_PRELOAD']:
        env.pop(key, None)
    env.update(settings)
    command = [str(args.binary.resolve()), '--ixe', str(args.ixe.resolve()),
               '--ixes', str(args.ixes.resolve()), '--trace-shards', '--max-ram', '230',
               '--direct-joins', '--structural-above', str(args.structural_above),
               '--jobs', '1', '--no-write', '--reprove-slot', str(args.slot)]
    meta = {
        'command': command, 'environment': settings, 'cpu_affinity': [*range(8)],
        'binary_sha256': digest(args.binary),
        'ixe_sha256': digest(args.ixe), 'ixes_sha256': digest(args.ixes),
        'started_ns': time.time_ns(),
    }
    (out / 'meta.json').write_text(json.dumps(meta, indent=2) + '\n')
    print(f'Running {args.mode}, slot {args.slot}, GPU {args.device}, eight CPU cores', flush=True)
    with (out / 'stdout').open('w') as stdout, (out / 'stderr').open('w') as stderr, \
            (out / 'gpu.csv').open('w') as gpu:
        monitor = subprocess.Popen([
            'nvidia-smi', f'--id={args.device}',
            '--query-gpu=timestamp,index,memory.used,utilization.gpu,power.draw',
            '--format=csv,noheader,nounits', '--loop-ms=200'],
            stdout=gpu, stderr=subprocess.DEVNULL)
        process = None
        try:
            process = subprocess.Popen(['/usr/bin/time', '-v', *command],
                env=env, stdout=stdout, stderr=stderr, start_new_session=True)
            meta['pid'] = process.pid
            meta['exit_code'] = process.wait(timeout=600)
        finally:
            if process is not None and process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                meta['killed'] = True
            monitor.terminate()
            try:
                monitor.wait(timeout=5)
            except subprocess.TimeoutExpired:
                monitor.kill()
                monitor.wait()
            meta['finished_ns'] = time.time_ns()
            (out / 'meta.json').write_text(json.dumps(meta, indent=2) + '\n')
    print(f'Finished {args.mode}: exit {meta.get("exit_code")}', flush=True)
    raise SystemExit(meta.get('exit_code', 1))


if __name__ == '__main__':
    main()
