#!/usr/bin/env python3
"""Measure one GPU proof stage and stop its process group on memory exhaustion."""

import argparse
import datetime
import json
import os
from pathlib import Path
import signal
import subprocess
import time


def available_kib():
    return next(int(line.split()[1]) for line in Path('/proc/meminfo').read_text().splitlines()
        if line.startswith('MemAvailable:'))


def tree_rss(pid, seen=None):
    seen = set() if seen is None else seen
    if pid in seen:
        return 0
    seen.add(pid)
    try:
        status = Path(f'/proc/{pid}/status').read_text()
        own = next((int(line.split()[1]) for line in status.splitlines() if line.startswith('VmRSS:')), 0)
        children = Path(f'/proc/{pid}/task/{pid}/children').read_text().split()
        return own + sum(tree_rss(int(child), seen) for child in children)
    except (OSError, ProcessLookupError):
        return 0


def gpu_memory():
    result = subprocess.run(['nvidia-smi', '--query-gpu=index,memory.used,utilization.gpu',
        '--format=csv,noheader,nounits'], capture_output=True, text=True, timeout=5)
    if result.returncode:
        raise RuntimeError(result.stderr.strip())
    return {row[0].strip(): {'used_mib': int(row[1]), 'utilization_percent': int(row[2])}
        for line in result.stdout.splitlines() if (row := line.split(','))}


def stop_group(process):
    for sig in [signal.SIGTERM, signal.SIGKILL]:
        try:
            os.killpg(process.pid, sig)
        except ProcessLookupError:
            break
        try:
            process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            continue
    process.wait(timeout=10)
    for _ in range(20):
        try:
            os.killpg(process.pid, 0)
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            return
        time.sleep(0.5)
    raise RuntimeError(f'process group {process.pid} still exists after termination')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        parser.error('missing command')
    args.directory.mkdir(parents=True, exist_ok=False)
    (args.directory / 'supervisor.pid').write_text(str(os.getpid()) + '\n')
    if available_kib() < 32 * 1024 * 1024:
        raise RuntimeError('less than 32 GiB host memory available before launch')
    environment_keys = [
        'IX_COMPRESSION_WORKER', 'IX_KZG_FIXED_CACHE', 'IX_KZG_SRS_CACHE', 'IX_KZG_PREFETCH_GIB',
        'IX_TEXRAY', 'IX_KZG_CUDA_DEVICES', 'IX_KZG_CUDA_RESIDENT_GIB', 'IX_KZG_CUDA_SRS_CACHE',
        'IX_KZG_MSM_CHUNK_POINTS',
        'IX_KZG_CUDA_PASSES', 'IX_KZG_CUDA_PROFILE', 'CUDA_VISIBLE_DEVICES', 'LD_LIBRARY_PATH',
        'RAYON_NUM_THREADS', 'OMP_NUM_THREADS', 'CARGO_BUILD_JOBS', 'RUST_LOG',
    ]
    record = {
        'command': command, 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'environment': {k: os.environ[k] for k in environment_keys if k in os.environ},
        'cpu_count': os.cpu_count(), 'initial_gpu_memory': gpu_memory(),
        'memory_stop_available_gib': 16, 'telemetry_interval_seconds': 2,
    }
    (args.directory / 'command.json').write_text(json.dumps(record, indent=2) + '\n')
    interrupted = []
    signal.signal(signal.SIGINT, lambda sig, frame: interrupted.append(sig))
    signal.signal(signal.SIGTERM, lambda sig, frame: interrupted.append(sig))
    peak = 0
    minimum = available_kib()
    gpu_peaks = {}
    reason = None
    started = time.monotonic()
    next_report = started
    time_path = args.directory / 'time.txt'
    with (args.directory / 'worker.log').open('w') as log, (args.directory / 'samples.jsonl').open('w') as samples:
        process = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(time_path), '--', *command],
            stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        (args.directory / 'child.pid').write_text(str(process.pid) + '\n')
        try:
            while process.poll() is None:
                available = available_kib()
                minimum = min(minimum, available)
                rss = tree_rss(process.pid)
                peak = max(peak, rss)
                gpus = gpu_memory()
                for index, gpu in gpus.items():
                    gpu_peaks[index] = max(gpu_peaks.get(index, 0), gpu['used_mib'])
                sample = {'elapsed_seconds': time.monotonic() - started,
                    'tree_rss_gib': rss / 2**20, 'available_gib': available / 2**20, 'gpus': gpus}
                samples.write(json.dumps(sample) + '\n')
                samples.flush()
                if time.monotonic() >= next_report:
                    print(json.dumps({'stage': str(args.directory), **sample}), flush=True)
                    next_report = time.monotonic() + 30
                if interrupted or available < 16 * 1024 * 1024:
                    reason = 'interrupted' if interrupted else 'host memory pressure'
                    stop_group(process)
                    break
                try:
                    process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    pass
        except BaseException:
            stop_group(process)
            raise
        code = process.wait()
    record.update({'exit_status': code, 'wall_seconds': time.monotonic() - started,
        'sampled_tree_peak_rss_gib': peak / 2**20, 'minimum_host_available_gib': minimum / 2**20,
        'sampled_device_peak_used_mib': gpu_peaks, 'stop_reason': reason})
    for line in time_path.read_text().splitlines():
        if 'Maximum resident set size (kbytes):' in line:
            record['peak_rss_gib'] = int(line.rsplit(':', 1)[1]) / 2**20
    (args.directory / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record), flush=True)
    return 0 if code == 0 and reason is None else 1


if __name__ == '__main__':
    raise SystemExit(main())
