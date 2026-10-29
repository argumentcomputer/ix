#!/usr/bin/env python3
"""Exercise resident proving and cross-record IxVM proofs on production artifacts.

Uses fixtures from check-formal.sh. CPU is the default; --devices 0,1 runs the
same resident jobs on real CUDA lanes and independently verifies on the CPU.
--pipeline additionally runs the expensive complete recursive aggregation.
All logs and reports are preserved in the fixture directory.
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
    cli.add_argument('--devices', help='comma-separated CUDA device indices; default: two CPU lanes')
    cli.add_argument('--pipeline', action='store_true')
    cli.add_argument('--pipeline-ram-gib', type=int, default=192)
    args = cli.parse_args()
    fixtures = args.fixtures.resolve()
    out = Path(tempfile.mkdtemp(prefix='controller-check-', dir=fixtures))
    cpu = Path('target/release').resolve()
    binary = Path('target/formal-cuda/release/ix-prover').resolve() if args.devices else cpu / 'ix-prover'
    devices = [int(d) for d in args.devices.split(',')] if args.devices else [None, None]
    if not devices or any(d is not None and not 0 <= d < 2**31 for d in devices):
        cli.error('invalid CUDA device indices')
    artifacts = [p.resolve() for p in [args.ixvm_artifact, args.recursion_artifact, args.aggregate_artifact]]
    env = dict(os.environ, IX_CUDA='0', AIUR_TRACE_ONLY_LOOKUPS='0', RAYON_NUM_THREADS='8',
               IX_AIUR_ARTIFACT=str(artifacts[0]), IX_AGGR_ARTIFACT=str(artifacts[2]))
    report = dict(success=False, devices=devices, commands=[], resident_jobs=[],
                  revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                  binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
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

    def wait_file(path, child):
        deadline = time.monotonic() + 600
        while not path.exists():
            if child.poll() is not None:
                raise RuntimeError(f'resident exited {child.returncode} waiting for {path}')
            if time.monotonic() > deadline:
                raise TimeoutError(f'waiting for {path}')
            time.sleep(0.02)
        return json.loads(path.read_text())

    def resident(name, config, jobs, statuses):
        directory = out / name
        directory.mkdir()
        config_path = directory / 'config.json'
        config_path.write_text(json.dumps(config))
        with (directory / 'host.log').open('w') as stream:
            child = subprocess.Popen([str(binary), 'serve', str(config_path), str(directory)],
                                     env=env, stdout=stream, stderr=subprocess.STDOUT)
            try:
                wait_file(directory / 'ready.json', child)
                for job in jobs:
                    path = directory / 'pending' / (job['id'] + '.tmp')
                    path.write_text(json.dumps(job))
                    path.rename(path.with_suffix('.json'))
                for job, expected in zip(jobs, statuses):
                    result = wait_file(directory / 'done' / (job['id'] + '.json'), child)
                    assert result['status'] == expected, result
                    report['resident_jobs'].append(dict(id=job['id'], **result))
            finally:
                (directory / 'stop').touch()
                try:
                    child.wait(timeout=120)
                except subprocess.TimeoutExpired:
                    child.kill()
                    child.wait()
                    raise
        assert child.returncode == 0, directory
        summary = json.loads((directory / 'summary.json').read_text())
        assert summary['record_reserved_bytes'] == 0, summary
        report[name] = summary
        save()
        return directory

    def product_files(path, ixvm):
        return (path, Path(str(path) + '.vk')) if ixvm else (path / 'proof.bin', path / 'key.bin')

    try:
        cases = json.loads((fixtures / 'claims.json').read_text())
        claim = next(c['invocation'] for c in cases if c['accept'] and
                     c['label'] == 'CheckEnv frontier-asm (Nat.add_comm)')
        invocation = out / 'claim.json'
        invocation.write_text(json.dumps(claim))
        inputs = [invocation, fixtures / 'inner/input.json', fixtures / 'aggregation.json.wrap.json']
        jobs, references = [], []
        for i, (artifact, source) in enumerate(zip(artifacts, inputs)):
            ixvm = i == 0
            host = cpu / ('ixvm-proof' if ixvm else 'stark-verifier')
            plan = out / f'plan-{i}'
            run(f'plan-{i}', [host, 'plan', artifact, source, plan, 0, 'regenerate'])
            plan_path = Path(str(plan) + '.report.json') if ixvm else plan / 'report.json'
            rows = json.loads(plan_path.read_text())['plan']['max_rows'] // 2
            assert rows > 0
            reference = out / f'reference-{i}'
            run(f'reference-{i}', [host, 'prove', artifact, source, reference, rows, 'regenerate'])
            references.append(product_files(reference, ixvm))
            for copy in range(2):
                jobs.append(dict(id=f'case-{i}-{copy}', artifact=str(artifact), input=str(source),
                                 output=str(out / f'proof-{i}-{copy}'), priority=i != 0,
                                 options=dict(max_rows=rows, retention='regenerate')))
        config = dict(artifacts=[dict(path=str(p), kind='ixvm' if i == 0 else 'recursion')
                                 for i, p in enumerate(artifacts)],
                      devices=devices, exec_jobs=2, threads_per_prover=4,
                      max_ram_bytes=8 << 30, texray=True)
        directory = resident('resident', config, jobs, [0] * len(jobs))
        assert '[texray]' in (directory / 'host.log').read_text(), 'texray emitted no phases'
        for job in jobs:
            i = int(job['id'].split('-')[1])
            proof, key = product_files(Path(job['output']), i == 0)
            assert proof.read_bytes() == references[i][0].read_bytes(), job['id']
            assert key.read_bytes() == references[i][1].read_bytes(), job['id']
            host = cpu / ('ixvm-proof' if i == 0 else 'stark-verifier')
            run(job['id'] + '-verify', [host, 'verify', artifacts[i], inputs[i], proof],
                dict(AIUR_TRACE_ONLY_LOOKUPS='1'))
        limited = dict(jobs[0], id='limited', output=str(out / 'limited-proof'))
        resident('record-limit', dict(config, record_limit_bytes=1024), [limited], [75])
        assert not Path(limited['output']).exists()

        # A real dependency-bearing IxVM environment, with all worker records
        # contributing to one public claim rather than independent leaf claims.
        tiny = fixtures / 'claims.json.controller.ixe'
        if not tiny.exists():
            raise RuntimeError('regenerate formal-aiur-tests fixtures: missing controller environment')
        ix = Path('.lake/build/bin/ix').resolve()
        manifest = out / 'two.ixes'
        run('partition', [ix, 'shard', tiny, '--shards', 2, '--out', manifest])
        proof_addresses = []
        for retention in ['retain', 'regenerate']:
            result_path = out / f'distributed-{retention}.json'
            command = [ix, 'prove', '--distributed', '--ixe', tiny, '--ixes', manifest,
                        '--exec-jobs', 2, '--max-ram', 8, '--retention', retention,
                        '--no-index', '--report', result_path]
            if args.devices:
                command += ['--gpu-device', devices[0]]
            text = run('distributed-' + retention, command)
            address = text.strip().splitlines()[-1]
            proof_addresses.append(address)
            result = json.loads(result_path.read_text())
            assert result['verified'] and result['cross_record_calls'] > 0
            assert len(result['workers']) == 2 and result['shards'] >= 2
            run('distributed-verify-' + retention,
                [ix, 'verify', '--distributed', '--ixe', tiny, '--ixes', manifest, address],
                dict(AIUR_TRACE_ONLY_LOOKUPS='1'))
        assert proof_addresses[0] == proof_addresses[1], 'retention changed distributed proof'
        report['distributed_proof'] = proof_addresses[0]
        run('reject-leaf-binding', [ix, 'verify', '--ixe', tiny, '--ixes', manifest,
                                   proof_addresses[0]], succeeds=False)
        failed_manifest = out / 'failed.ixes'
        failed_report = out / 'failed-pipeline.json'
        text = run('pipeline-budget-failure',
                   [ix, 'prove', '--aggregate', '--direct-joins', '--no-cache', '--no-index',
                    '--ixe', tiny, '--ixes', manifest, '--trace-shards', '--jobs', 2,
                    '--exec-jobs', 2, '--max-ram', 8, '--report', failed_report,
                    '--out-ixes', failed_manifest],
                   dict(AIUR_RECORD_MAX_BYTES='1024', AIUR_LANES_CACHE_DIR=str(out / 'failed-checkpoints')),
                   succeeds=False)
        assert 'no such process' not in text and 'prover stopped' not in text
        assert not failed_manifest.exists(), 'failed run published a completed manifest'
        failed_summary = json.loads(Path(str(failed_report) + '.summary.json').read_text())
        assert failed_summary['record_reserved_bytes'] == 0
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
            events = (out / 'pipeline.json.events.jsonl').read_text()
            assert not events.strip(), 'cached root triggered execution'
            report['pipeline_proof'] = address
        report['success'] = True
        print(f'Controller validation passed: {out / "report.json"}', flush=True)
    finally:
        save()


if __name__ == '__main__':
    main()
