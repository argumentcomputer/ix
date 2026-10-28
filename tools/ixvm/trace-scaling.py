#!/usr/bin/env python3
"""Compare CPU trace scaling using fixed grouped artifacts and query records.

Build bench-compare-aiur and the stark-verifier compare example with parallel
support first. Each process executes once, then generates complete traces and
host lookup buffers twice for warmup and --samples times for measurement.
Processes run sequentially, pinned to one hardware thread per core before SMT.
"""
import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess


def cpu_order():
    cores = {}
    for cpu in sorted(os.sched_getaffinity(0)):
        topology = Path(f'/sys/devices/system/cpu/cpu{cpu}/topology')
        key = tuple((topology / name).read_text().strip()
                    for name in ('physical_package_id', 'core_id'))
        cores.setdefault(key, []).append(cpu)
    return ([cpus[0] for cpus in cores.values()]
            + [cpu for cpus in cores.values() for cpu in cpus[1:]])


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('output', type=Path)
    cli.add_argument('--inputs', type=Path, default=Path('.lake/formal-comparison/final'))
    cli.add_argument('--ixvm-artifact', type=Path, required=True)
    cli.add_argument('--recursion-artifact', type=Path, required=True)
    cli.add_argument('--threads', type=int, nargs='+', default=[8, 64, 1, 32])
    cli.add_argument('--samples', type=int, default=3)
    args = cli.parse_args()
    cpus = cpu_order()
    if args.samples < 1 or any(n < 1 or n > len(cpus) for n in args.threads):
        cli.error('samples must be positive and thread counts must fit available CPUs')
    args.output.mkdir(parents=True, exist_ok=True)
    inputs = [
        ('environment', 'ixvm', args.ixvm_artifact, args.inputs / 'environment-input.json'),
        ('recursion-real', 'recursion', args.recursion_artifact,
         args.inputs / 'new-environment-grouped.json.inner/input.json'),
    ]
    binaries = {'legacy': '.lake/build/bin/bench-compare-aiur',
                'new': 'target/release/examples/compare'}
    files = [p for _, _, artifact, input_path in inputs for p in (artifact, input_path)]
    manifest = dict(
        base_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        cpus=cpus, threads=args.threads, samples=args.samples, warmups=2,
        lscpu=json.loads(subprocess.check_output(['lscpu', '-J'], text=True)),
        reused_execution=True, host_lookups=True, thp_disabled=True,
        artifact_input_sha256={str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        binary_sha256={name: hashlib.sha256(Path(p).read_bytes()).hexdigest()
                       for name, p in binaries.items()},
        commands=[],
    )
    rows = []
    shapes = {}
    for ti, threads in enumerate(args.threads):
        env = dict(os.environ, RAYON_NUM_THREADS=str(threads),
                   IX_BENCH_NO_THP='1', IX_BENCH_REUSE_EXECUTION='1',
                   AIUR_TRACE_ONLY_LOOKUPS='0')
        for wi, (workload, app, artifact, input_path) in enumerate(inputs):
            order = ['legacy', 'new'] if (ti + wi) % 2 == 0 else ['new', 'legacy']
            for backend in order:
                output = args.output / f'{workload}-{backend}-{threads}.json'
                program = app if backend == 'legacy' else str(artifact)
                command = ['taskset', '-c', ','.join(map(str, cpus[:threads])),
                           binaries[backend], program, str(input_path), str(output), str(args.samples)]
                manifest['commands'].append(command)
                (args.output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
                print(f'{workload} {backend}: {threads} threads', flush=True)
                with output.with_suffix('.log').open('w') as log:
                    subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
                data = json.loads(output.read_text())
                if not data.get('reused_execution') or not all(s['execute_seconds'] is None for s in data['samples']):
                    raise RuntimeError('benchmark binary did not reuse execution; rebuild it')
                shape = [(c['height'], c['stage1_width'], c['stage2_width'], c['cells'])
                         for c in data['circuits']]
                key = workload, backend
                if shapes.setdefault(key, shape) != shape:
                    raise RuntimeError(f'{key}: circuit shapes changed with thread count')
                samples = [s['trace_with_lookups_seconds'] for s in data['samples']]
                row = dict(workload=workload, backend=backend, threads=threads,
                           median_seconds=statistics.median(samples), min_seconds=min(samples),
                           max_seconds=max(samples), cells=sum(c['cells'] for c in data['circuits']))
                rows.append(row)
                with (args.output / 'summary.csv').open('w') as f:
                    writer = csv.DictWriter(f, fieldnames=list(row), lineterminator='\n')
                    writer.writeheader()
                    writer.writerows(rows)
                print(f"  trace + lookups: {row['median_seconds']:.6f}s", flush=True)


if __name__ == '__main__':
    main()
