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
    cases = [('default', {}, 'bn254', False, True)]
    for curve in ['bn254']:
        for cuda in [False, True]:
            cases.append((f'{curve}-{"cuda" if cuda else "cpu"}',
                {'IX_KZG_CURVE': curve, 'IX_CUDA': str(int(cuda))}, curve, cuda, True))
    cases += [
        ('trace-codegen', {'IX_KZG_CURVE': 'bn254', 'IX_CUDA_TRACE_CODEGEN': '1'}, 'bn254', True, True),
        ('no-parallel', {'IX_KZG_CURVE': 'bn254', 'IX_NO_PAR': '1'}, 'bn254', False, False),
        ('plonk-cuda-only', {'IX_KZG_CURVE': 'bn254', 'IX_PLONK_CUDA': '1'}, 'bn254', False, True),
        ('both-cuda', {'IX_KZG_CURVE': 'bn254', 'IX_PLONK_CUDA': '1', 'IX_CUDA': '1'}, 'bn254', True, True),
    ]
    report = {'lean': version, 'typecheck_passed': True, 'cases': []}
    for name, selection, curve, cuda, parallel in cases:
        environment = dict(os.environ, LEAN_PATH=str(out))
        for variable in ['IX_KZG_CURVE', 'IX_CUDA', 'IX_CUDA_TRACE_CODEGEN', 'IX_NO_PAR', 'IX_PLONK_CUDA']:
            environment.pop(variable, None)
        environment.update(selection)
        result = subprocess.run(prefix + ['--run', 'tests/compression_build_config.lean'],
            env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (out / f'{name}.log').write_text(result.stdout)
        if result.returncode:
            raise RuntimeError(f'configuration evaluation failed: {name}')
        actual = json.loads(result.stdout.splitlines()[-1])
        required = {'plonk'}
        required |= {'parallel'} if parallel else set()
        worker = required | ({'cuda'} if cuda else set())
        ffi = required | ({'cuda-trace-codegen'} if name == 'trace-codegen' else ({'cuda'} if cuda else set()))
        for target, expected in [
            ('worker', worker), ('ffi', ffi),
            ('net', ffi | ({'net'} if sys.platform != 'darwin' else set())),
            ('test', ffi | {'test-ffi'}),
        ]:
            arguments = actual[target]
            package = 'ix-proof-compression' if target == 'worker' else 'ix-ffi'
            if arguments[arguments.index('-p') + 1] != package:
                raise RuntimeError(f'{name}: wrong package for {target}')
            if '--no-default-features' not in arguments or features(arguments) != expected:
                raise RuntimeError(f'{name}: unexpected {target} features: {arguments}')
        if actual['worker'][actual['worker'].index('--bin') + 1] != 'ix-compression-worker':
            raise RuntimeError(f'{name}: wrong worker executable')
        if actual['terminal_plonk'] is not True:
            raise RuntimeError(f'{name}: wrong terminal backend selection')
        if actual['plonk_cuda'] != (selection.get('IX_PLONK_CUDA') == '1'):
            raise RuntimeError(f'{name}: PLONK CUDA selection depends on inner CUDA selection')
        helper = 'ix-bn254-plonk-wrapper'
        if actual['plonk_helper'] != helper or '-tags' in actual['plonk_build']:
            raise RuntimeError(f'{name}: wrong PLONK helper or Go build tags')
        report['cases'].append({'name': name, 'environment': selection, 'arguments': actual, 'passed': True})
    environment.update(IX_KZG_CURVE='invalid')
    result = subprocess.run(prefix + ['--run', 'tests/compression_build_config.lean'],
        env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (out / 'invalid.log').write_text(result.stdout)
    if result.returncode != 1 or 'IX_KZG_CURVE must be bn254' not in result.stdout:
        raise RuntimeError('invalid curve was not rejected as expected')
    report['invalid_curve_rejected'] = True
    environment.update(IX_KZG_CURVE='bls12-381', IX_PLONK_CUDA='1')
    result = subprocess.run(prefix + ['--run', 'tests/compression_build_config.lean'],
        env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (out / 'invalid-plonk-cuda.log').write_text(result.stdout)
    if result.returncode != 1 or 'IX_KZG_CURVE must be bn254' not in result.stdout:
        raise RuntimeError('retired curve configuration was not rejected')
    report['retired_curve_rejected'] = True
    report['source_sha256'] = {p: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in [
        'lakefile.lean', 'tests/compression_build_config.lean', 'tests/check_compression_build.py',
        'crates/ffi/Cargo.toml', 'crates/proof-compression/Cargo.toml', 'lean-toolchain',
    ]}
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'report': str(out / 'report.json'), 'typecheck': 'passed',
        'configurations_passed': len(cases), 'invalid_curve_rejected': True}))


if __name__ == '__main__':
    main()
