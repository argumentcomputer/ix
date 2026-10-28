#!/usr/bin/env python3
"""Compare CPU and CUDA development proofs using independently built binaries."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time


def sha256(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def run(command, log, environment, *, success=True, expected_error=None):
    print(json.dumps({'command': command, 'log': str(log)}), flush=True)
    started = time.monotonic()
    timing = log.with_suffix('.time')
    measured = ['/usr/bin/time', '-v', '-o', str(timing), '--', *command]
    with log.open('w') as output:
        result = subprocess.run(
            measured if Path('/usr/bin/time').is_file() else command,
            env=environment, stdout=output, stderr=subprocess.STDOUT,
        )
    if result.returncode != (0 if success else 1):
        raise RuntimeError(f'unexpected exit {result.returncode}: {log}')
    if expected_error is not None and expected_error not in log.read_text():
        raise RuntimeError(f'missing expected rejection {expected_error!r}: {log}')
    return {
        'command': command, 'log': str(log), 'exit_code': result.returncode,
        'elapsed_seconds': time.monotonic() - started,
        'timing': str(timing) if timing.exists() else None,
    }


def build(curve, cuda, directory, environment):
    mode = 'cuda' if cuda else 'cpu'
    features = 'parallel' + (',cuda' if cuda else '')
    command = [
        'cargo', 'build', '--offline', '--locked', '-p', 'ix-proof-compression',
        '--no-default-features', '--features', features,
        '--example', 'kzg_backend_parity', '--message-format=json-render-diagnostics',
    ]
    log = directory / f'build-{mode}.jsonl'
    record = run(command, log, environment)
    executable = None
    native = None
    for line in log.read_text().splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if event.get('reason') == 'compiler-artifact' and event.get('target', {}).get('name') == 'kzg_backend_parity':
            executable = event.get('executable')
        if 'dylib=multi_stark_cuda' in event.get('linked_libs', []):
            native = Path(event['out_dir']) / 'libmulti_stark_cuda.so'
    if not executable or (cuda and native is None):
        raise RuntimeError(f'Cargo did not report the requested artifacts: {log}')
    # Cargo reuses the example's output name across feature selections.
    # Snapshot each binary and its shared library before building another one.
    binary = directory / 'bin' / mode
    binary.parent.mkdir(exist_ok=True)
    shutil.copy2(executable, binary)
    if cuda:
        library = directory / 'lib' / native.name
        library.parent.mkdir(exist_ok=True)
        shutil.copy2(native, library)
        record['native_sha256'] = sha256(library)
    record.update({'features': features, 'binary': str(binary), 'binary_sha256': sha256(binary)})
    return binary, record


def check_dispatch(log, mode):
    text = log.read_text()
    if mode == 'passes':
        required = ['KZG lookup constructed in GPU passes', 'KZG quotient evaluated in GPU passes']
    else:
        required = ['KZG lookup constructed on device', 'KZG quotient evaluated on device']
    required += ['KZG interpolation queue']
    if mode == 'cached':
        required += ['KZG SRS cache access']
    missing = [entry for entry in required if entry not in text]
    if missing:
        raise RuntimeError(f'missing GPU dispatch evidence {missing}: {log}')
    return required


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    root = args.out.resolve()
    if root.exists() and any(root.iterdir()):
        parser.error('output directory must be empty')
    root.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ, RUST_LOG='ix_proof_compression=debug')
    curves = ['bn254']
    report = {
        'baseline_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'scope': 'Two ordinary KZG circuits at 4096/8192 rows with development parameters; no FRI or recursive KZG proving.',
        'curves': {},
    }
    sources = subprocess.check_output([
        'git', 'ls-files', '--cached', '--others', '--exclude-standard', '--',
        'crates/proof-compression', 'crates/aiur', 'Cargo.toml', 'Cargo.lock',
        '.cargo/config.toml', 'rust-toolchain.toml', 'tests/kzg_backend_parity.py',
    ], text=True).splitlines()
    report['source_sha256'] = {p: sha256(Path(p)) for p in sorted(set(sources))
        if Path(p).suffix in {'.rs', '.cu', '.cuh', '.cpp', '.h', '.hpp', '.toml', '.lock', '.py'}}
    for curve in curves:
        directory = root / curve
        directory.mkdir()
        cpu, cpu_build = build(curve, False, directory, environment)
        cpu_env = dict(environment, CUDA_VISIBLE_DEVICES='')
        cpu_run = run([str(cpu), 'prove', str(directory / 'cpu'), 'cpu'], directory / 'prove-cpu.log', cpu_env)
        reference = json.loads((directory / 'cpu' / 'report.json').read_text())
        gpu, gpu_build = build(curve, True, directory, environment)
        gpu_env = dict(environment, CUDA_VISIBLE_DEVICES='0')
        gpu_env['LD_LIBRARY_PATH'] = str(directory / 'lib') + (
            ':' + environment['LD_LIBRARY_PATH'] if environment.get('LD_LIBRARY_PATH') else '')
        runs = {'cpu': cpu_run}
        for mode in ['dense', 'passes', 'cached']:
            log = directory / f'prove-{mode}.log'
            runs[mode] = run([str(gpu), 'prove', str(directory / mode), mode], log, gpu_env)
            runs[mode]['dispatch'] = check_dispatch(log, mode)
            candidate = json.loads((directory / mode / 'report.json').read_text())
            for key in ['curve', 'input_blake3', 'proof_blake3', 'verifier_blake3']:
                if candidate[key] != reference[key]:
                    raise RuntimeError(f'{curve} {mode}: {key} differs from CPU')
            for artifact in ['proof.bin', 'vk.bin']:
                if (directory / mode / artifact).read_bytes() != (directory / 'cpu' / artifact).read_bytes():
                    raise RuntimeError(f'{curve} {mode}: {artifact} differs from CPU')
        verifier = directory / 'cpu' / 'vk.bin'
        pin = reference['verifier_blake3']
        verified = []
        for mode in runs:
            verified.append(run([str(cpu), 'verify', str(directory / mode / 'proof.bin'), str(verifier), pin],
                directory / f'verify-{mode}-on-cpu.log', cpu_env))
        verified.append(run([str(gpu), 'verify', str(directory / 'cpu' / 'proof.bin'), str(verifier), pin],
            directory / 'verify-cpu-on-cuda-binary.log', dict(gpu_env, CUDA_VISIBLE_DEVICES='')))
        rejected = run([str(cpu), 'verify', str(directory / 'cpu' / 'proof.bin'), str(verifier), '0' * 64],
            directory / 'reject-verifier-pin.log', cpu_env, success=False,
            expected_error='verifier differs from the independently supplied pin')
        report['curves'][curve] = {
            'builds': [cpu_build, gpu_build], 'proving_runs': runs, 'verification_runs': verified,
            'wrong_pin_rejection': rejected, 'proof_bytes': reference['proof_bytes'],
            'proof_blake3': reference['proof_blake3'], 'verifier_blake3': pin,
            'input_blake3': reference['input_blake3'], 'exact_byte_parity': True,
        }
        (root / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    (root / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'report': str(root / 'report.json'), 'curves': curves, 'exact_byte_parity': True}), flush=True)


if __name__ == '__main__':
    main()
