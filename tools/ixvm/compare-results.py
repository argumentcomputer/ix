#!/usr/bin/env python3
"""Save timing summaries and every circuit's separate stage widths/costs."""
import csv
import hashlib
import json
import os
import pathlib
import platform
import statistics
import subprocess
import sys

directory = pathlib.Path(sys.argv[1])
summary, circuits = [], []
for path in sorted(directory.glob('*.json')):
    data = json.loads(path.read_text())
    if not isinstance(data, dict) or 'samples' not in data or 'circuits' not in data:
        continue
    rows = data['circuits']
    executions = [s['execute_seconds'] for s in data['samples']
                  if s['execute_seconds'] is not None]
    summary.append(dict(run=path.stem, backend=data['backend'], samples=len(data['samples']),
                        thp_disabled=data.get('thp_disabled'),
                        reused_execution=data.get('reused_execution', False),
                        initial_execute_seconds=data.get('initial_execute_seconds'),
                        execute_seconds=statistics.median(executions) if executions else None,
                        trace_with_lookups_seconds=statistics.median(s['trace_with_lookups_seconds'] for s in data['samples']),
                        circuits=len(rows), active_circuits=sum(r['height'] > 0 for r in rows),
                        stage1_columns=sum(r['stage1_width'] for r in rows),
                        stage2_columns=sum(r['stage2_width'] for r in rows),
                        cells=sum(r['cells'] for r in rows), fft_cost=sum(r['fft_cost'] for r in rows),
                        **(data['proof'] or {})))
    names = data.get('circuit_names', [])
    for row in rows:
        index = row['index']
        name = row.get('name') or (names[index] if index < len(names) else f'auxiliary_{index-len(names)}')
        circuits.append(dict(run=path.stem, name=name, **{k: row[k] for k in [
            'index', 'height', 'stage1_width', 'stage2_width', 'preprocessed_width',
            'preprocessed_height', 'quotient_degree', 'cells', 'fft_cost']}))

for name, rows in [('summary', summary), ('circuits', circuits)]:
    keys = list(dict.fromkeys(key for row in rows for key in row))
    with (directory / f'{name}.csv').open('w') as out:
        writer = csv.DictWriter(out, fieldnames=keys)
        writer.writeheader()
        writer.writerows(rows)
manifest = dict(base_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                working_tree_modified=bool(subprocess.check_output(['git', 'diff', 'HEAD', '--name-only'], text=True)),
                platform=platform.platform(), threads=os.getenv('RAYON_NUM_THREADS', 'unspecified'),
                thp=os.getenv('IX_BENCH_NO_THP', '0'), rustflags=pathlib.Path('.cargo/config.toml').read_text(),
                artifacts={p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest() for p in sys.argv[2:]})
inner = directory / 'new-environment-grouped.json.inner'
manifest['recursive_input'] = {
    name: dict(bytes=path.stat().st_size, sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    for name in ['proof.bin', 'key.bin', 'claims.bin', 'input.json']
    if (path := inner / name).is_file()}
(directory / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(f'Wrote {directory / "summary.csv"} and {directory / "circuits.csv"}')
