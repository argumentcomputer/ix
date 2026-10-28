#!/usr/bin/env python3
"""Check grouped, sharded CPU/CUDA proofs using check-formal.sh fixtures.

The default requires a real CUDA device. --cpu-only exercises the CPU controls
without claiming hardware validation. Every run preserves its logs and report.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def files(product, ixvm):
    if ixvm:
        return product, Path(f'{product}.vk'), Path(f'{product}.report.json')
    return product / 'proof.bin', product / 'key.bin', product / 'report.json'


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('fixtures', type=Path)
    cli.add_argument('--ixvm-artifact', type=Path, required=True)
    cli.add_argument('--recursion-artifact', type=Path, required=True)
    cli.add_argument('--aggregate-artifact', type=Path, required=True)
    cli.add_argument('--cpu-dir', type=Path, default=Path('target/release'))
    cli.add_argument('--cuda-dir', type=Path, default=Path('target/formal-cuda/release'))
    cli.add_argument('--device', type=int, default=os.getenv('MULTI_STARK_CUDA_DEVICE', '0'))
    cli.add_argument('--cpu-only', action='store_true')
    args = cli.parse_args()
    if not 0 <= args.device < 2**31:
        cli.error('device must be a nonnegative CUDA device index fitting i32')
    args.fixtures = args.fixtures.resolve()
    out = Path(tempfile.mkdtemp(prefix='cuda-check-', dir=args.fixtures))
    report = dict(success=False, hardware_validated=False, cpu_only=args.cpu_only,
                  device=args.device, cuda_visible_devices=os.getenv('CUDA_VISIBLE_DEVICES'),
                  revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                  binary_sha256={}, artifact_sha256={}, input_sha256={}, commands=[], cases=[])
    print(f'CUDA validation logs and report: {out}', flush=True)

    def save():
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')

    def run(name, command, env, succeeds=True):
        command = [str(x) for x in command]
        log = out / f'{len(report["commands"]):02}-{name}.log'
        print(name, flush=True)
        start = time.monotonic()
        with log.open('w') as stream:
            result = subprocess.run(command, env=env, stdout=stream, stderr=subprocess.STDOUT)
        report['commands'].append(dict(name=name, command=command, log=log.name,
                                       seconds=time.monotonic() - start, exit_code=result.returncode,
                                       expected_success=succeeds,
                                       trace_only_lookups=env['AIUR_TRACE_ONLY_LOOKUPS']))
        save()
        if (result.returncode == 0) != succeeds:
            raise RuntimeError(f'{name}: unexpected exit {result.returncode}; see {log}')

    try:
        cpu_env = dict(os.environ, IX_CUDA='0', AIUR_TRACE_ONLY_LOOKUPS='0')
        verify_env = dict(cpu_env, AIUR_TRACE_ONLY_LOOKUPS='1')
        gpu_env = dict(cpu_env, IX_CUDA='1', MULTI_STARK_CUDA_DEVICE=str(args.device))
        for directory in [args.cpu_dir] + ([] if args.cpu_only else [args.cuda_dir]):
            for name in ['ixvm-proof', 'stark-verifier']:
                binary = directory / name
                report['binary_sha256'][str(binary)] = digest(binary)
        if not args.cpu_only and shutil.which('nvidia-smi'):
            run('nvidia-smi', ['nvidia-smi'], gpu_env)

        claims = json.loads((args.fixtures / 'claims.json').read_text())
        claim = next(c['invocation'] for c in claims
                     if c['accept'] and c['label'] == 'CheckEnv frontier-asm (Nat.add_comm)')
        claim_path = out / 'claim.json'
        claim_path.write_text(json.dumps(claim) + '\n')
        cases = [
            ('ixvm', args.ixvm_artifact, claim_path, True),
            ('recursion', args.recursion_artifact, args.fixtures / 'inner/input.json', False),
            ('aggregate', args.aggregate_artifact, args.fixtures / 'aggregation.json.wrap.json', False),
        ]
        for name, artifact, invocation, ixvm in cases:
            report['artifact_sha256'][str(artifact)] = digest(artifact)
            report['input_sha256'][str(invocation)] = digest(invocation)
            binary_name = 'ixvm-proof' if ixvm else 'stark-verifier'
            cpu = args.cpu_dir / binary_name
            cuda = args.cuda_dir / binary_name
            directory = out / name
            directory.mkdir()

            # Derive a two-shard fixture from the actual record, instead of
            # picking a row cap that might silently leave a one-shard test.
            plan = directory / 'plan'
            run(f'{name}-plan', [cpu, 'plan', artifact, invocation, plan, '0', 'regenerate'], cpu_env)
            planning = json.loads(files(plan, ixvm)[2].read_text())['plan']
            if not planning['fits'] or planning['max_rows'] < 2:
                raise RuntimeError(f'{name}: fixture cannot exercise trace sharding')
            rows = planning['max_rows'] // 2
            case = dict(name=name, max_rows=rows, proofs=[])
            report['cases'].append(case)

            variants = [('cpu-retain', cpu, cpu_env, 'retain', None),
                        ('cpu-regenerate', cpu, cpu_env, 'regenerate', None)]
            if not args.cpu_only:
                variants += [('cuda-host-retain', cuda, gpu_env, 'retain', args.device),
                             ('cuda-host-regenerate', cuda, gpu_env, 'regenerate', args.device),
                             ('cuda-graph-regenerate', cuda,
                              dict(gpu_env, AIUR_TRACE_ONLY_LOOKUPS='1'), 'regenerate', args.device)]
            reference = None
            for variant, binary, env, retention, device in variants:
                target = directory / variant
                target.mkdir()
                product = target / 'proof'
                options = target / 'options.json'
                options.write_text(json.dumps(dict(max_rows=rows, retention=retention, device=device)))
                run(f'{name}-{variant}', [binary, 'prove', artifact, invocation, product,
                                         rows, retention, options], env)
                proof, key, proof_report = files(product, ixvm)
                result = json.loads(proof_report.read_text())
                if not result['verified'] or result['shards'] < 2:
                    raise RuntimeError(f'{name}-{variant}: proof did not verify across multiple shards')
                # Deliberately inherit the GPU lookup flag in the CPU verifier.
                run(f'{name}-{variant}-verify', [cpu, 'verify', artifact, invocation, proof], verify_env)
                identity = (proof.read_bytes(), key.read_bytes())
                if reference is None:
                    reference = identity
                    exported = directory / 'cpu-key'
                    run(f'{name}-cpu-key', [cpu, 'key', artifact, exported], verify_env)
                    if (exported / 'key.bin').read_bytes() != identity[1]:
                        raise RuntimeError(f'{name}: exported key differs from proving key')
                    wrong = json.loads(invocation.read_text())
                    wrong['args'][0] = int(wrong['args'][0] == 0)
                    wrong_path = directory / 'wrong-public.json'
                    wrong_path.write_text(json.dumps(wrong))
                    run(f'{name}-reject-wrong-public', [cpu, 'verify', artifact, wrong_path, proof],
                        verify_env, succeeds=False)
                    # A CPU host must not silently honor an explicit GPU request.
                    invalid = directory / 'cpu-device.json'
                    invalid.write_text(json.dumps(dict(device=args.device)))
                    run(f'{name}-reject-cpu-device', [cpu, 'plan', artifact, invocation,
                                                    directory / 'invalid', rows, 'auto', invalid],
                        cpu_env, succeeds=False)
                elif identity != reference:
                    raise RuntimeError(f'{name}-{variant}: CPU/CUDA or retention proof/key bytes differ')
                case['proofs'].append(dict(variant=variant, proof_sha256=digest(proof),
                                          key_sha256=digest(key), shards=result['shards'],
                                          proof_bytes=result['proof_bytes']))
                save()
        report['success'] = True
        report['hardware_validated'] = not args.cpu_only
        print('CPU controls passed.' if args.cpu_only else 'CPU/CUDA proof and key parity passed.', flush=True)
    except Exception as error:
        report['error'] = str(error)
        raise
    finally:
        save()


if __name__ == '__main__':
    main()
