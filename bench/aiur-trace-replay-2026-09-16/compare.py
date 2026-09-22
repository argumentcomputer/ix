"""Check a paired production replay and summarize its timings and memory."""

import argparse
import csv
import hashlib
import importlib.util
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    'analyze', HERE.parent / 'prover-profile-2026-09-15/analyze.py')
analyze = importlib.util.module_from_spec(spec)
spec.loader.exec_module(analyze)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('handwritten', type=Path)
    parser.add_argument('generated', type=Path)
    parser.add_argument('--output', type=Path, default=HERE / 'comparison.json')
    args = parser.parse_args()
    runs = {}
    reference = None
    for mode, directory in [('blake3', args.handwritten), ('generated', args.generated)]:
        metadata = json.loads((directory / 'meta.json').read_text())
        assert metadata['exit_code'] == 0 and not metadata.get('killed'), directory
        assert metadata['environment']['AIUR_GPU_TRACE'] == mode
        stderr = (directory / 'stderr').read_text()
        proof = re.findall(r'replay slot (\d+): proof ([0-9a-f]{64}) \(not persisted\)', stderr)
        assert len(proof) == 1, 'Expected one verified replay proof'
        plan = [line for line in stderr.splitlines() if line.startswith('[trace-shards] shard ')]
        assert plan, 'Missing trace-piece plan'
        record = re.search(r'\[trace-shards\].*?record (\d+) B', stderr)
        assert record, 'Missing record size'
        spans = analyze.read_spans(directory / 'spans.jsonl')
        prefix = 'blake3' if mode == 'blake3' else 'codegen'
        seed_name = f'aiur/{prefix}_seeds'
        device_name = f'aiur/{prefix}_device_rows'
        seeds = [s for s in spans if s['name'] == seed_name]
        devices = [s for s in spans if s['name'] == device_name]
        assert seeds and devices, 'Selected trace provider did not run'
        shapes = sorted((int(s['fields']['circuit']), int(s['fields']['rows'])) for s in seeds)
        other = 'codegen' if mode == 'blake3' else 'blake3'
        assert not any(s['name'] == f'aiur/{other}_seeds' for s in spans)
        identity = {
            'proof': proof[0][1], 'slot': int(proof[0][0]),
            'command': metadata['command'],
            'environment': {k: v for k, v in metadata['environment'].items()
                            if k not in ('AIUR_GPU_TRACE', 'AIUR_PROFILE')},
            'cpu_affinity': metadata['cpu_affinity'],
            'binary_sha256': metadata['binary_sha256'],
            'ixe_sha256': metadata['ixe_sha256'],
            'ixes_sha256': metadata['ixes_sha256'],
            'trace_plan': plan, 'seed_shapes': shapes,
            'committed_widths': [line for line in stderr.splitlines()
                                 if line.startswith('[trace-shards] committed widths:')],
            'record_bytes': int(record[1]),
        }
        if reference is None:
            reference = identity
        assert identity == reference, f'Replay inputs or proof/plan differ: {mode}'
        names = {
            'proving': 'aiur/prove_planned', 'replay': 'aiur/replay',
            'execution_and_planning': 'aiur/prepare_slot',
            'seed_preparation': seed_name, 'device_callback': device_name,
            'cpu_witness': 'aiur/cpu_witness',
            'stage1_commit': 'stark/stage1_commit',
            'lookup_construction': 'stark/lookup_construction',
            'quotient': 'stark/quotient', 'fri_open': 'stark/fri_open',
        }
        phases = {label: analyze.seconds((s['start'], s['end']) for s in spans
                                        if s['name'] == name)
                  for label, name in names.items()}
        assert phases['proving'] > 0
        rss = int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', stderr)[1]) / 2**20
        with (directory / 'gpu.csv').open() as stream:
            gpu_peak = max(float(row[2]) for row in csv.reader(stream)) / 1024
        dispatch = [line for line in stderr.splitlines()
                    if 'prepared GPU BLAKE3 trace' in line or 'prepared generated CUDA trace' in line]
        seed_bytes = sum(int(re.search(r'seed_bytes=(\d+)', line)[1]) for line in dispatch)
        assert len(dispatch) == len(seeds)
        assert seed_bytes == sum(rows for _, rows in shapes) * 176
        runs[mode] = {
            'directory': directory.name, 'phases_s': phases, 'peak_rss_gib': rss,
            'sampled_gpu_peak_gib': gpu_peak, 'seed_bytes_prepared': seed_bytes,
            'seed_preparations': len(seeds), 'device_callbacks': len(devices),
        }
    output = {
        'samples_per_mode': 1, 'proof': reference['proof'], 'slot': reference['slot'],
        'binary_sha256': reference['binary_sha256'], 'record_bytes': reference['record_bytes'],
        'pieces': len(reference['trace_plan']),
        'trace_plan_sha256': hashlib.sha256('\n'.join(reference['trace_plan']).encode()).hexdigest(),
        'runs': runs,
        'generated_proving_change_percent': 100 * (
            runs['generated']['phases_s']['proving'] / runs['blake3']['phases_s']['proving'] - 1),
    }
    args.output.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
