#!/usr/bin/env python3
"""Suggest a grouping policy from Lean layout metrics and recorded row counts.

This is an untrusted search heuristic, not an artifact compiler. Feed its policy
to grouping_tune (or the application exporter) to obtain certified layouts.
Every workload's estimated cells and FFT work must stay within the starting
policy's budget; column count is a smaller secondary objective.
"""
import argparse
import functools
import json
import math
from pathlib import Path


def padded(n):
    return 0 if n == 0 else 1 << (n - 1).bit_length()


def fft_cost(main, auxiliary, quotient, height):
    def transform(n):
        return n * max(1, n.bit_length() - 1) if n else 0
    return (3 * (main + auxiliary) * transform(height)
            + 2 * transform(quotient * height)
            + 2 * quotient * transform(2 * height))


def lookup_degree(lookups, size):
    result = 1
    for at in range(0, len(lookups), size):
        chunk = lookups[at:at + size]
        degree = sum(p[0] for p in chunk)
        result = max(result, degree + 1,
                     max(p[1] + degree - p[0] for p in chunk))
    return result


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('metrics', type=Path)
    cli.add_argument('output', type=Path)
    cli.add_argument('--profile', nargs=2, action='append', required=True,
                     metavar=('COUNTS', 'UNGROUPED_BENCH'))
    cli.add_argument('--prefix', required=True)
    cli.add_argument('--max-members', type=int, default=16)
    cli.add_argument('--sweeps', type=int, default=4)
    cli.add_argument('--report-only', action='store_true')
    args = cli.parse_args()
    data = json.loads(args.metrics.read_text())
    chips = data['chips']
    indices = {c['name']: i for i, c in enumerate(chips)}
    reps = dict(data['representatives'])
    entries = {indices[reps.get(n, n)] for n in data['entries']}
    counts, statistics = [], []
    for count_path, bench_path in args.profile:
        rows = [0] * len(chips)
        for f in json.loads(Path(count_path).read_text())['function_rows']:
            rows[indices[f['chip']]] += f['rows']
        counts.append(rows)
        statistics.append({c['name']: c for c in json.loads(Path(bench_path).read_text())['circuits']})
    # Singleton shape is measured by the actual Rust lowering, including lookup
    # pairing. These shapes are independent of which workload produced rows.
    singleton = statistics[0]
    groups, used = {}, set()
    for _, names in data['groups']:
        members = tuple(sorted({indices[reps.get(n, n)] for n in names
                               if reps.get(n, n) in indices} - entries - used))
        if len(members) >= 2:
            groups[len(groups)] = members
            used.update(members)
    for i in range(len(chips)):
        if i not in used:
            groups[len(groups)] = (i,)

    @functools.lru_cache(maxsize=200_000)
    def shape(members):
        if len(members) == 1:
            c = singleton[chips[members[0]]['name']]
            return c['stage1_width'], c['stage2_width'], c['quotient_degree']
        selected = [chips[i] for i in members]
        width = 1 + sum(c['private'] + c['lifted'] for c in selected) + max(c['shared'] for c in selected)
        lookups = [(max((c['lookups'][j][0] if j < len(c['lookups']) else 0) for c in selected),
                    max((c['lookups'][j][1] if j < len(c['lookups']) else 0) for c in selected))
                   for j in range(max(len(c['lookups']) for c in selected))]
        constraints = max(2, *(c['constraint_degree'] for c in selected))
        quotient = padded(max(2, constraints, lookup_degree(lookups, 1)) - 1)
        size = 1
        for candidate in range(min(8, len(lookups)), 1, -1):
            if padded(max(2, constraints, lookup_degree(lookups, candidate)) - 1) <= quotient:
                size = candidate
                break
        return width, 2 * math.ceil(len(lookups) / size), quotient

    @functools.lru_cache(maxsize=200_000)
    def cost(members):
        if not members:
            return (0,) * (2 + 2 * len(counts))
        main, auxiliary, quotient = shape(members)
        values = [main, 1]
        for rows in counts:
            height = padded(sum(rows[i] for i in members))
            values.extend((height * main, fft_cost(main, auxiliary, quotient, height)))
        return tuple(values)

    def total():
        return tuple(map(sum, zip(*(cost(g) for g in groups.values()))))

    initial = total()
    weights = [0.05 / initial[0], 0.01 / initial[1]]
    for i in range(len(counts)):
        weights.extend((0.2 / len(counts) / max(1, initial[2 + 2*i]),
                        1.0 / len(counts) / max(1, initial[3 + 2*i])))

    def score(delta):
        return sum(a * b for a, b in zip(delta, weights))

    def delta_for(old, new):
        return tuple(sum(cost(g)[i] for g in new) - sum(cost(g)[i] for g in old)
                     for i in range(len(weights)))

    def fits(delta, current):
        return all(current[i] + delta[i] <= initial[i] for i in range(2, len(weights)))

    current = initial
    if not args.report_only:
        for sweep in range(args.sweeps):
            moves = 0
            for member in range(len(chips)):
                if member in entries:
                    continue
                source = next(k for k, g in groups.items() if member in g)
                old = groups[source]
                remainder = tuple(i for i in old if i != member)
                best = None
                destinations = list(groups) + ([None] if len(old) > 1 else [])
                for target in destinations:
                    if target == source:
                        continue
                    other = groups[target] if target is not None else ()
                    if any(i in entries for i in other) or len(other) >= args.max_members:
                        continue
                    combined = tuple(sorted((*other, member)))
                    delta = delta_for((old, other), (remainder, combined))
                    gain = score(delta)
                    if gain < -1e-10 and fits(delta, current) and (best is None or gain < best[0]):
                        best = gain, target, combined, delta
                if best is not None:
                    _, target, combined, delta = best
                    if target is None:
                        target = max(groups) + 1
                    groups[target] = combined
                    if remainder:
                        groups[source] = remainder
                    else:
                        del groups[source]
                    current = tuple(a + b for a, b in zip(current, delta))
                    moves += 1
            # Moving a whole group can cross a padding boundary that no single
            # member move can improve on its own.
            for source in list(groups):
                if source not in groups or any(i in entries for i in groups[source]):
                    continue
                old = groups[source]
                best = None
                for target, other in groups.items():
                    if target == source or any(i in entries for i in other) or len(old) + len(other) > args.max_members:
                        continue
                    combined = tuple(sorted(old + other))
                    delta = delta_for((old, other), (combined,))
                    gain = score(delta)
                    if gain < -1e-10 and fits(delta, current) and (best is None or gain < best[0]):
                        best = gain, target, combined, delta
                if best is not None:
                    _, target, combined, delta = best
                    groups[target] = combined
                    del groups[source]
                    current = tuple(a + b for a, b in zip(current, delta))
                    moves += 1
            print(f'sweep {sweep}: {moves} moves, {len(groups)} function circuits, {current[0]} columns, objective {score(current):.6f}', flush=True)
            if not moves:
                break
    ordered = sorted(groups.values(), key=lambda g: min(g))
    policy = [[f'{args.prefix}_{i:02}', [chips[j]['name'] for j in g]]
              for i, g in enumerate(g for g in ordered if len(g) >= 2)]
    args.output.write_text(json.dumps(policy, indent=2) + '\n')
    report = {'initial': initial, 'optimized': current,
              'dimensions': ['stage1_columns', 'function_circuits'] +
                  [s for i in range(len(counts)) for s in (f'cells_{i}', f'fft_{i}')],
              'profiles': args.profile,
              'circuits': [{'members': [chips[i]['name'] for i in g], 'shape': shape(g), 'cost': cost(g)} for g in ordered]}
    args.output.with_suffix('.report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('dimensions', 'initial', 'optimized')}), flush=True)


if __name__ == '__main__':
    main()
