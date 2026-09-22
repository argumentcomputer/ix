#!/usr/bin/env python3
"""Run one fresh Init proof, retaining automatic-sharding and scheduler data."""
import argparse
import csv
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import time


def sha256(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def stop(process):
    if process is None or process.poll() is not None:
        return
    os.killpg(process.pid, signal.SIGTERM)
    try:
        process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.wait()


def summarize(directory):
    text = (directory / 'lanes.err').read_text()
    metadata = json.loads((directory / 'meta.json').read_text())
    tasks = {}
    def task(kind, ident):
        return tasks.setdefault((kind, ident or 'root'), dict(kind=kind, id=ident or 'root'))
    for line in text.splitlines():
        match = re.match(r'\[lanes\] (claim|join|root)(?: (\d+))? dispatched at \+(\d+)s', line)
        if match:
            task(match[1], match[2])['dispatched_s'] = int(match[3])
        match = re.match(r'\[lanes\] executor (\d+): (claim|join|root)(?: (\d+))? execution started at \+(\d+)s', line)
        if match:
            task(match[2], match[3]).update(executor=int(match[1]), execution_started_s=int(match[4]))
        match = re.match(r'\[lanes\] executor (\d+): (claim|join|root)(?: (\d+))? executed in ([\d.]+)s, record (\d+) B .* at \+(\d+)s', line)
        if match:
            task(match[2], match[3]).update(executor=int(match[1]), execution_s=float(match[4]), record_bytes=int(match[5]), prepared_s=int(match[6]))
        match = re.match(r'\[lanes\] worker (\d+): (claim|join|root)(?: (\d+))? proving started at \+(\d+)s', line)
        if match:
            task(match[2], match[3]).update(gpu=int(match[1]), proving_started_s=int(match[4]))
        match = re.match(r'\[lanes\] worker (\d+): (claim|join|root)(?: (\d+))? (?:proven|published) at \+(\d+)s', line)
        if match:
            task(match[2], match[3]).update(gpu=int(match[1]), proven_s=int(match[4]))
    fields = ['kind', 'id', 'executor', 'gpu', 'dispatched_s', 'execution_started_s', 'execution_s', 'record_bytes', 'prepared_s', 'proving_started_s', 'proven_s']
    with (directory / 'tasks.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(tasks.values())
    root = re.search(r'\[lanes\] root ([0-9a-f]{64}) verified; composed verdict OK; end to end (\d+)s', text)
    cold = re.search(r'\[lanes\] (\d+) claims \(0 reused from the index, 0 retired under cached joins without an indexed proof\), (\d+) joins \(0 cached\)', text)
    summary = dict(verified=bool(root), fresh=bool(cold), tasks=len(tasks))
    if root:
        summary.update(root=root[1], proving_seconds=int(root[2]))
    if cold:
        summary.update(claims=int(cold[1]), joins=int(cold[2]))
        assert summary['joins'] == summary['claims'] - 1
    if root and cold:
        assert len(tasks) == summary['claims'] + summary['joins']
        assert all('proven_s' in t and 'record_bytes' in t for t in tasks.values())
        last_claim = max(t['proven_s'] for t in tasks.values() if t['kind'] == 'claim')
        summary['tail_seconds'] = summary['proving_seconds'] - last_claim
    summary['host_budget'] = next((line for line in text.splitlines() if line.startswith('[lanes] host budget')), None)
    summary['pool'] = next((line for line in text.splitlines() if line.startswith('[lanes] record pool:')), None)
    summary['contention_retries'] = text.count('released for memory contention; requeued')
    spill_logging = 'multi_stark::cuda::witness=debug' in metadata['environment'].get('RUST_LOG', '')
    summary['lde_spills'] = text.count('spilled active LDE') if spill_logging else None
    summary['generated_main_commitments'] = text.count('path="prepared"') if spill_logging else None
    summary['trace_plans'] = [
        dict(zip(['shards', 'cells', 'record_bytes', 'host_workspace_bytes', 'reserved_workspace_bytes'], map(int, match.groups())))
        for match in re.finditer(r'\[trace-shards\] (\d+) shards, (\d+) committed cells: record (\d+) B in shared pool, host workspace (\d+) B of (\d+) B reserved per prover', text)
    ]
    summary['root_wraps'] = [
        dict(seconds=float(match[1]), input_shards=int(match[2]), output_shards=int(match[3]))
        for match in re.finditer(r'\[aggregate\] root wrap proven in ([\d.]+)s .*: (\d+) shard\(s\) verified into (\d+)', text)
    ]
    samples = {}
    with (directory / 'gpu.csv').open(newline='') as stream:
        for row in csv.reader(stream):
            if len(row) == 4:
                samples.setdefault(int(row[1]), []).append((int(row[2]), int(row[3])))
    summary['gpu_samples'] = {
        gpu: dict(peak_vram_mib=max(memory for memory, _ in values),
                  mean_utilization_percent=sum(util for _, util in values) / len(values),
                  samples=len(values))
        for gpu, values in samples.items()
    }
    for line in (directory / 'time.txt').read_text().splitlines():
        for label, key in [('User time (seconds):', 'user_seconds'), ('System time (seconds):', 'system_seconds'), ('Maximum resident set size (kbytes):', 'peak_rss_kib')]:
            if line.strip().startswith(label):
                summary[key] = float(line.split(label, 1)[1])
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--max-ram', type=int, default=230)
    parser.add_argument('--exec-jobs', type=int, default=3)
    parser.add_argument('--lanes', type=int, default=4)
    parser.add_argument('--shards', type=int)
    parser.add_argument('--timeout', type=int, default=1200)
    args = parser.parse_args()
    binary, source, directory = args.binary.resolve(), args.input.resolve(), args.output.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    cache = directory / 'cache'
    cache.mkdir()
    manifest = directory / 'init.ixes'
    environment = dict(os.environ, AIUR_GPU_TRACE='blake3', AIUR_TRACE_ONLY_LOOKUPS='1',
                       AIUR_MAX_PIECE_LOG_HEIGHT='24', AIUR_TRACE_SHARD_MAX_CELLS='1500000000',
                       AIUR_LANES_CACHE_DIR=str(cache), RAYON_NUM_THREADS=str(len(os.sched_getaffinity(0))),
                       RUST_LOG='multi_stark::cuda::pcs=debug,multi_stark::cuda::witness=debug', LC_ALL='C')
    shard = [str(binary), 'shard', str(source), '--max-ram', str(args.max_ram), '--exec-jobs', str(args.exec_jobs), '--parallelism', str(args.lanes), '--out', str(manifest)]
    if args.shards is not None:
        shard += ['--shards', str(args.shards)]
    prove = [str(binary), 'prove', '--ixe', str(source), '--ixes', str(manifest), '--trace-shards', '--lanes', str(args.lanes), '--exec-jobs', str(args.exec_jobs), '--max-ram', str(args.max_ram)]
    meta = dict(started=datetime.datetime.now(datetime.timezone.utc).isoformat(), binary=str(binary), binary_sha256=sha256(binary), input=str(source), input_sha256=sha256(source), shard_command=shard, prove_command=prove,
                environment={k: v for k, v in environment.items() if k.startswith(('AIUR_', 'RAYON_', 'RUST_LOG', 'MULTI_STARK_', 'CUDA_'))}, affinity=sorted(os.sched_getaffinity(0)))
    meta['platform'] = platform.platform()
    meta['gpus'] = subprocess.check_output(['nvidia-smi', '--query-gpu=index,name,driver_version,memory.total', '--format=csv,noheader'], text=True).splitlines()
    for name in ('enabled', 'defrag'):
        path = Path('/sys/kernel/mm/transparent_hugepage') / name
        if path.exists():
            meta['thp_' + name] = path.read_text().strip()
    (directory / 'meta.json').write_text(json.dumps(meta, indent=2) + '\n')
    with (directory / 'shard.log').open('w') as output:
        subprocess.run(shard, env=environment, stdout=output, stderr=subprocess.STDOUT, check=True, timeout=args.timeout)
    meta['manifest_sha256'] = sha256(manifest)
    monitor = process = None
    result = {}
    with (directory / 'gpu.csv').open('w') as gpu, (directory / 'monitor.err').open('w') as monitor_err, (directory / 'lanes.out').open('w') as out, (directory / 'lanes.err').open('w') as err:
        try:
            monitor = subprocess.Popen(['nvidia-smi', '--query-gpu=timestamp,index,memory.used,utilization.gpu', '--format=csv,noheader,nounits', '-l', '1'], stdout=gpu, stderr=monitor_err, start_new_session=True)
            began = time.monotonic()
            process = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(directory / 'time.txt'), *prove], env=environment, stdout=out, stderr=err, start_new_session=True)
            result['returncode'] = process.wait(timeout=args.timeout)
            result['wall_seconds'] = time.monotonic() - began
        finally:
            stop(process)
            stop(monitor)
            (directory / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    result.update(summarize(directory))
    meta['ended'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    (directory / 'meta.json').write_text(json.dumps(meta, indent=2) + '\n')
    (directory / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)
    if result['returncode'] or not result['verified'] or not result['fresh']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
