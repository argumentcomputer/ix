#!/usr/bin/env python3
"""Force a record-ceiling split on Init, verify the root and probe restart."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def stop(process):
    if process is None or process.poll() is not None:
        return
    os.killpg(process.pid, signal.SIGTERM)
    try:
        process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.wait()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--record-gib', type=int, default=22)
    parser.add_argument('--verify-existing', action='store_true',
        help='Check saved results and rerun verification/restart without another proof run.')
    args = parser.parse_args()
    binary, source, manifest, output = (path.resolve() for path in
        (args.binary, args.input, args.manifest, args.output))
    if not args.verify_existing:
        active = subprocess.check_output(['nvidia-smi',
            '--query-compute-apps=pid,process_name', '--format=csv,noheader'], text=True)
        if active.strip():
            raise SystemExit('GPU processes are active; wait before validating:\n' + active)
        output.mkdir(parents=True, exist_ok=False)
    original = manifest.read_bytes()
    frozen_manifest = output / 'input.ixes'
    if not args.verify_existing:
        frozen_manifest.write_bytes(original)
    refined = output / 'refined.ixes'
    environment = dict(os.environ, AIUR_GPU_TRACE='blake3',
        AIUR_TRACE_ONLY_LOOKUPS='1', AIUR_MAX_PIECE_LOG_HEIGHT='24',
        AIUR_TRACE_SHARD_MAX_CELLS='1500000000',
        AIUR_RECORD_MAX_BYTES=str(args.record_gib << 30),
        AIUR_LANES_CACHE_DIR=str(output / 'cache'),
        RAYON_NUM_THREADS=str(len(os.sched_getaffinity(0))),
        RUST_LOG='multi_stark::cuda::witness=debug', LC_ALL='C')
    environment.pop('AIUR_PROFILE', None)
    prove = [str(binary), 'prove', '--ixe', str(source), '--ixes', str(frozen_manifest),
        '--out-ixes', str(refined), '--trace-shards', '--lanes', '4',
        '--exec-jobs', '3', '--max-ram', '230']
    metadata = dict(binary_sha256=digest(binary), input_sha256=digest(source),
        manifest_sha256=digest(manifest), command=prove,
        environment={k: v for k, v in environment.items()
            if k.startswith(('AIUR_', 'RAYON_', 'RUST_LOG', 'MULTI_STARK_', 'CUDA_'))})
    if args.verify_existing:
        assert json.loads((output / 'meta.json').read_text()) == metadata, 'run metadata differs'
    else:
        (output / 'meta.json').write_text(json.dumps(metadata, indent=2) + '\n')
        process = monitor = None
        with (output / 'lanes.out').open('w') as out, (output / 'lanes.err').open('w') as err, \
                (output / 'gpu.csv').open('w') as gpu, (output / 'monitor.err').open('w') as monitor_err:
            try:
                monitor = subprocess.Popen(['nvidia-smi',
                    '--query-gpu=timestamp,index,memory.used,utilization.gpu',
                    '--format=csv,noheader,nounits', '-l', '1'],
                    stdout=gpu, stderr=monitor_err, start_new_session=True)
                process = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(output / 'time.txt'), *prove],
                    env=environment, stdout=out, stderr=err, start_new_session=True)
                code = process.wait(timeout=1200)
            finally:
                stop(process)
                stop(monitor)
        assert code == 0, f'prove exited {code}'
    timing = (output / 'time.txt').read_text()
    assert re.search(r'Exit status: 0$', timing, re.M), 'saved proof run failed'
    clock = re.search(r'Elapsed \(wall clock\) time.*: ([\d:.]+)$', timing, re.M)[1]
    elapsed = sum(float(part) * 60 ** i for i, part in enumerate(reversed(clock.split(':'))))
    log = (output / 'lanes.err').read_text()
    root = re.search(r'root ([0-9a-f]{64}) verified; composed verdict OK;', log)
    assert root, 'missing verified root'
    splits = re.findall(r'\[lanes\] split claim (\d+) into claims \[(\d+), (\d+)\]', log)
    assert splits, 'the ceiling did not force a split'
    reused = [int(n) for n in re.findall(r'\[lanes\] \d+ claims \((\d+) reused', log)]
    assert max(reused) > 0, 'unaffected proofs were not reused'
    checkpoints = list((output / 'cache/refined-manifests').glob('*.ixes'))
    assert len(checkpoints) == 1 and checkpoints[0].read_bytes() == refined.read_bytes()
    assert frozen_manifest.read_bytes() == original == manifest.read_bytes()
    verify = [str(binary), 'verify', '--aggregate', '--ixe', str(source),
        '--ixes', str(refined), '--structural-above', '0', root[1]]
    with (output / 'verify.log').open('w') as stream:
        subprocess.run(verify, env=environment, stdout=stream, stderr=subprocess.STDOUT,
                       check=True, timeout=120)
    # The cached root join needs no record. A one-byte ceiling rejects its
    # first wrap, exercising the proving thread's reservation binding.
    probe_env = dict(environment, AIUR_RECORD_MAX_BYTES='1')
    with (output / 'resume.log').open('w') as stream:
        probe = subprocess.run(prove, env=probe_env, stdout=stream, stderr=subprocess.STDOUT,
                               timeout=120)
    resume = (output / 'resume.log').read_text()
    assert probe.returncode != 0
    assert 'resuming refined partition' in resume
    counts = re.search(r'\[lanes\] (\d+) claims \((\d+) reused', resume)
    assert counts and counts[1] == counts[2], 'restart did not reuse every claim'
    assert re.search(r'root: record reached \d+ B, over the 1 B record cap', resume)
    assert not re.search(r'claim \d+ execution started', resume)
    result = dict(verified=True, wall_seconds=elapsed, root=root[1], splits=splits,
        reused_claims_by_pass=reused, checkpoint_resume=True,
        resume_claims_reused=int(counts[2]), root_wrap_ceiling_enforced=True,
        resume_probe_exit_code=probe.returncode,
        peak_rss_gib=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', timing)[1]) / (1 << 20),
        refined_manifest_sha256=digest(refined),
        input_unchanged=True, lde_spills=log.count('spilled active LDE'))
    (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
