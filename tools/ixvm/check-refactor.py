#!/usr/bin/env python3
"""Compare a modularized artifact with its pre-refactor export.

Only declared global renames and no-op guards/assignments may differ. Removing
the legacy load/store syntax wrappers eliminates their empty binding guards;
jump targets and trace hint instruction offsets are relocated accordingly.
Every other instruction, constraint, table row, layout and grouping must match.
This is an artifact regression check, not a legacy-to-Aiur translation proof.
"""
import argparse
import json
from pathlib import Path
import re


def transform(value, f):
    if isinstance(value, str):
        return f(value)
    if isinstance(value, list):
        return [transform(x, f) for x in value]
    if isinstance(value, dict):
        return {k: transform(x, f) for k, x in value.items()}
    return value


def normalize_guards(package):
    maps = {}
    removed = 0
    for function in package['program']['functions']:
        code, positions = [], {}
        for pc, op in enumerate(function['code']):
            positions[pc] = len(code)
            if op['op'] == 'guard' and op['tests'] == []:
                removed += 1
            else:
                code.append(op)
        positions[len(function['code'])] = len(code)
        for op in code:
            if op['op'] == 'jump':
                op['target'] = positions[op['target']]
            elif op['op'] == 'branch':
                op['otherwise'] = positions[op['otherwise']]
        function['code'] = code
        maps[function['name']] = positions

    def hints(value, positions):
        if isinstance(value, dict):
            if value.get('op') == 'hint':
                value['instruction'] = positions[value['instruction']]
            for x in value.values():
                hints(x, positions)
        elif isinstance(value, list):
            for x in value:
                hints(x, positions)

    for function in package['trace']['functions']:
        hints(function['steps'], maps[function['name']])
        function['steps'] = [step for step in function['steps'] if not (
            step['action']['op'] == 'assign' and
            step['action']['values'] == [{'var': dest} for dest in step['action']['dest']])]
    return removed


def first_difference(a, b, path=''):
    if type(a) is not type(b):
        return path + ': different types'
    if isinstance(a, dict):
        if a.keys() != b.keys():
            return path + ': different keys'
        for k in a:
            if a[k] != b[k]:
                return first_difference(a[k], b[k], f'{path}.{k}')
    elif isinstance(a, list):
        if len(a) != len(b):
            return f'{path}: different lengths {len(a)} != {len(b)}'
        for i, (x, y) in enumerate(zip(a, b)):
            if x != y:
                return first_difference(x, y, f'{path}[{i}]')
    elif a != b:
        return f'{path}: {a!r} != {b!r}'
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('before', type=Path)
    parser.add_argument('after', type=Path)
    parser.add_argument('names', type=Path)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    names = json.loads(args.names.read_text())
    before = json.loads(args.before.read_text())
    after = json.loads(args.after.read_text())
    before = transform(before, lambda s: re.sub(r'\b(?:IxVM|MultiStark)::\w+',
        lambda m: names.get(m[0], m[0]), s))
    removed_before = normalize_guards(before)
    removed_after = normalize_guards(after)
    difference = first_difference(before, after)
    if difference:
        raise SystemExit('Refactor mismatch at ' + difference)
    summary = {
        'equivalent_artifacts_modulo_names_and_noops': True,
        'functions': len(after['program']['functions']),
        'maps': len(after['program']['maps']),
        'chips': len(after['trace']['chips']),
        'groups': len(after['trace']['groups']),
        'removed_empty_guards': removed_before - removed_after,
        'before': str(args.before), 'after': str(args.after),
    }
    print(json.dumps(summary, indent=2))
    if args.out:
        args.out.write_text(json.dumps(summary, indent=2) + '\n')


if __name__ == '__main__':
    main()
