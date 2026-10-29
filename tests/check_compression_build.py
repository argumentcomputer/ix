#!/usr/bin/env python3
"""Check the actual Lake-generated CLI and worker arguments without building ix."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def features(arguments):
    if '--features' not in arguments:
        return set()
    index = arguments.index('--features')
    return set(arguments[index + 1].split(','))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--toolchain', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    toolchain = args.toolchain.resolve()
    lean = toolchain / 'bin' / 'lean'
    plugin = toolchain / 'lib' / 'lean' / 'libLake_shared.so'
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    prefix = [str(lean), f'--load-dynlib={plugin}']
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    expected_version = Path('lean-toolchain').read_text().strip().split(':')[-1].removeprefix('v')
    if f'version {expected_version},' not in version:
        raise RuntimeError(f'wrong toolchain: {version}')
    result = subprocess.run(prefix + ['-o', str(out / 'lakefile.olean'), 'lakefile.lean'],
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (out / 'typecheck.log').write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f'Lake configuration typecheck failed: {out / "typecheck.log"}')
    cases = [('default', {}, False, True, set())]
    for cuda in [False, True]:
        for selected in [set(), {'plonk'}, {'groth16'}, {'plonk', 'groth16'}]:
            name = ('cuda' if cuda else 'cpu') + '-' + ('-'.join(sorted(selected)) or 'kzg')
            selection = {'IX_CUDA': str(int(cuda)), 'IX_PLONK': str(int('plonk' in selected)), 'IX_GROTH16': str(int('groth16' in selected))}
            cases.append((name, selection, cuda, True, selected))
    cases += [
        ('trace-codegen', {'IX_CUDA_TRACE_CODEGEN': '1'}, True, True, set()),
        ('no-parallel', {'IX_NO_PAR': '1'}, False, False, set()),
    ]
    report = {'lean': version, 'typecheck_passed': True, 'cases': []}
    for name, selection, cuda, parallel, final in cases:
        environment = dict(os.environ, LEAN_PATH=str(out))
        for variable in ['IX_PLONK', 'IX_GROTH16', 'IX_CUDA', 'IX_CUDA_TRACE_CODEGEN', 'IX_NO_PAR']:
            environment.pop(variable, None)
        environment.update(selection)
        result = subprocess.run(prefix + ['--run', 'tests/compression_build_config.lean'],
            env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (out / f'{name}.log').write_text(result.stdout)
        if result.returncode:
            raise RuntimeError(f'configuration evaluation failed: {name}')
        actual = json.loads(result.stdout.splitlines()[-1])
        ffi = ({'parallel'} if parallel else set()) | ({'cuda-trace-codegen'} if name == 'trace-codegen' else ({'cuda'} if cuda else set()))
        for target, expected in [
            ('ffi', ffi),
            ('net', ffi | final | ({'net'} if sys.platform != 'darwin' else set())),
            ('test', ffi | {'test-ffi'}),
        ]:
            arguments = actual[target]
            if arguments[arguments.index('-p') + 1] != 'ix-ffi':
                raise RuntimeError(f'{name}: wrong package for {target}')
            if '--no-default-features' not in arguments or features(arguments) != expected:
                raise RuntimeError(f'{name}: unexpected {target} features: {arguments}')
        if actual['final_plonk'] != ('plonk' in final) or actual['final_groth16'] != ('groth16' in final):
            raise RuntimeError(f'{name}: wrong final backend selection')
        if actual['plonk_cuda'] != (cuda and 'plonk' in final):
            raise RuntimeError(f'{name}: PLONK CUDA requires both plonk and cuda')
        report['cases'].append({'name': name, 'environment': selection, 'arguments': actual, 'passed': True})
    environment.update(IX_PLONK='invalid')
    result = subprocess.run(prefix + ['--run', 'tests/compression_build_config.lean'],
        env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (out / 'invalid.log').write_text(result.stdout)
    if result.returncode != 1 or 'IX_PLONK must be' not in result.stdout:
        raise RuntimeError('invalid final feature flag was not rejected')
    report['invalid_feature_flag_rejected'] = True
    report['source_sha256'] = {p: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in [
        'lakefile.lean', 'tests/compression_build_config.lean', 'tests/check_compression_build.py',
        'crates/ffi/Cargo.toml', 'crates/proof-compression/Cargo.toml', 'lean-toolchain',
    ]}
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'report': str(out / 'report.json'), 'typecheck': 'passed',
        'configurations_passed': len(cases), 'invalid_feature_flag_rejected': True}))


if __name__ == '__main__':
    main()
