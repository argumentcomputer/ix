#!/usr/bin/env python3
"""Exercise the aggregate controller on production artifacts.

Uses fixtures from check-formal.sh: a two-claim environment proven on CPU
lanes, its claims alone, the ceiling failure, and resumption. --pipeline
additionally runs the complete recursive aggregation, on CUDA lanes with
--devices. All logs and reports are preserved in the fixture directory.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('fixtures', type=Path)
    cli.add_argument('--ixvm-artifact', type=Path, required=True)
    cli.add_argument('--recursion-artifact', type=Path, required=True)
    cli.add_argument('--aggregate-artifact', type=Path, required=True)
    cli.add_argument('--devices', help='comma-separated CUDA device indices; default: two CPU lanes. '
                     'A repeated index (0,0) runs several lanes on one GPU, a single-device '
                     'smoke test of concurrent multi-lane proving')
    cli.add_argument('--pipeline', action='store_true')
    cli.add_argument('--pipeline-ram-gib', type=int, default=192)
    args = cli.parse_args()
    fixtures = args.fixtures.resolve()
    out = Path(tempfile.mkdtemp(prefix='controller-check-', dir=fixtures))
    devices = [int(d) for d in args.devices.split(',')] if args.devices else [None, None]
    if not devices or any(d is not None and not 0 <= d < 2**31 for d in devices):
        cli.error('invalid CUDA device indices')
    artifacts = [p.resolve() for p in [args.ixvm_artifact, args.recursion_artifact, args.aggregate_artifact]]
    env = dict(os.environ, IX_CUDA='0', AIUR_TRACE_ONLY_LOOKUPS='0',
               IX_AIUR_ARTIFACT=str(artifacts[0]), IX_AGGR_ARTIFACT=str(artifacts[2]))
    if len(set(devices)) < len(devices) and None not in devices:
        env['IX_PROVER_SHARED_DEVICES'] = '1'
    ix = Path('.lake/build/bin/ix').resolve()
    report = dict(success=False, devices=devices, commands=[],
                  revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                  binary_sha256=hashlib.sha256(ix.read_bytes()).hexdigest(),
                  artifact_sha256=[hashlib.sha256(p.read_bytes()).hexdigest() for p in artifacts])
    print(f'Controller validation logs: {out}', flush=True)

    def save():
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')

    def run(name, command, extra=None, succeeds=True):
        log = out / f'{len(report["commands"]):02}-{name}.log'
        start = time.monotonic()
        with log.open('w') as stream:
            result = subprocess.run([str(x) for x in command], env=dict(env, **(extra or {})),
                                    stdout=stream, stderr=subprocess.STDOUT, timeout=1800)
        report['commands'].append(dict(name=name, command=[str(x) for x in command], log=log.name, exit_code=result.returncode,
                                       seconds=time.monotonic() - start))
        save()
        if (result.returncode == 0) != succeeds:
            raise RuntimeError(f'{name}: unexpected status {result.returncode}; see {log}')
        return log.read_text()

    try:
        # A real dependency-bearing IxVM environment, split into two leaves.
        tiny = fixtures / 'claims.json.controller.ixe'
        if not tiny.exists():
            raise RuntimeError('regenerate formal-aiur-tests fixtures: missing controller environment')
        manifest = out / 'two.ixes'
        run('partition', [ix, 'shard', tiny, '--shards', 2, '--out', manifest])
        failed_manifest = out / 'failed.ixes'
        failed_report = out / 'failed-pipeline.json'
        text = run('pipeline-budget-failure',
                   [ix, 'prove', '--aggregate', '--direct-joins', '--no-cache', '--no-index',
                    '--ixe', tiny, '--ixes', manifest, '--trace-shards', '--jobs', 2,
                    '--exec-jobs', 2, '--max-ram', 16, '--report', failed_report,
                    '--out-ixes', failed_manifest],
                   dict(AIUR_RECORD_MAX_BYTES='1024', AIUR_HOST_WORKSPACE_BYTES=str(4 << 30),
                        AIUR_LANES_CACHE_DIR=str(out / 'failed-checkpoints')),
                   succeeds=False)
        assert 'cannot be split further' in text, 'an unsplittable claim over the ceiling did not stop the run'
        assert not failed_manifest.exists(), 'failed run published a completed manifest'

        # Legacy's fold (every join structural): proves, passes the trusted
        # acceptance check, verifies independently, and resumes.
        rust = [ix, 'prove', '--aggregate', '--structural-above', 0,
                '--ixe', tiny, '--ixes', manifest, '--trace-shards', '--jobs', 2,
                '--exec-jobs', 2, '--max-ram', 64, '--out-ixes', out / 'rust.ixes']
        rust_env = dict(AIUR_HOST_WORKSPACE_BYTES=str(16 << 30),
                        AIUR_LANES_CACHE_DIR=str(out / 'rust-cache'))
        text = run('rust-controller', rust, rust_env)
        rust_root = text.strip().splitlines()[-1]
        assert 'composed verdict OK' in text, 'the controller skipped the composed verdict'
        run('rust-controller-verify', [ix, 'verify', '--aggregate', '--structural-above', 0,
                                       '--ixe', tiny, '--ixes', out / 'rust.ixes', rust_root])
        text = run('rust-controller-resume', rust, rust_env)
        assert text.strip().splitlines()[-1] == rust_root
        assert not any('claim' in line and 'execution started' in line for line in text.splitlines()), \
            'resumed run executed a claim again'
        assert 'cache hit' in text, 'resumed run ignored the aggregate cache'
        report['structural_root'] = rust_root

        # The claims alone: one line per claim, each a verified proof.
        text = run('claims-only', [ix, 'prove', '--ixe', tiny, '--ixes', manifest, '--jobs', 2,
                                   '--exec-jobs', 2, '--max-ram', 64, '--no-index',
                                   '--out-ixes', out / 'claims.ixes'], rust_env)
        claims = [line.split() for line in text.splitlines() if len(line.split()) == 2
                  and len(line.split()[1]) == 64]
        assert len(claims) == 2, text
        run('claims-verify', [ix, 'verify', '--ixe', tiny, '--ixes', out / 'claims.ixes']
            + [address for _, address in claims])
        if args.pipeline:
            command = [ix, 'prove', '--aggregate', '--direct-joins', '--ixe', tiny,
                       '--ixes', manifest, '--trace-shards', '--shard-rows', 4194304,
                       '--max-ram', args.pipeline_ram_gib, '--exec-jobs', 2,
                       '--report', out / 'pipeline.json', '--out-ixes', out / 'final.ixes']
            if args.devices:
                # CLI --lanes chooses consecutive devices, so reject a hole.
                assert devices == list(range(devices[0], devices[0] + len(devices)))
                command += ['--lanes', len(devices), '--gpu-device', devices[0]]
            else:
                command += ['--jobs', 2]
            text = run('pipeline', command, dict(AIUR_LANES_CACHE_DIR=str(out / 'checkpoints')))
            address = text.strip().splitlines()[-1]
            run('pipeline-verify', [ix, 'verify', '--aggregate', '--ixe', tiny,
                                   '--ixes', out / 'final.ixes', address])
            text = run('pipeline-resume', command, dict(AIUR_LANES_CACHE_DIR=str(out / 'checkpoints')))
            assert text.strip().splitlines()[-1] == address
            assert not any('claim' in line and 'execution started' in line
                           for line in text.splitlines()), 'resumed pipeline executed a claim'
            report['pipeline_proof'] = address
        report['success'] = True
        print(f'Controller validation passed: {out / "report.json"}', flush=True)
    finally:
        save()


if __name__ == '__main__':
    main()
