#!/usr/bin/env python3
"""Runs Closure.lean over every test module in parallel and collects one JSONL file per shard.

usage: run.py TOP10 OUTDIR [--heartbeats N] [--timeout-ms N] [--shard N] [--jobs N]
              [--limit-theorems N] [--rankers a,b,...]

TOP10 has lines THEOREM<TAB>MODULE<TAB>RANKER<TAB>P1,P2,...; a `none` condition with no premises
is added for every theorem. A module with more theorems than --shard is split into shards that
each elaborate the whole module but attempt only their own theorems. Existing shard outputs that
finished are kept, so an interrupted run resumes.
"""
import argparse, collections, concurrent.futures as cf, json, os, random, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
MATHLIB = '/home/sam/repos/ix.ixai-aiur/.lake/packages/mathlib'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('top10'); ap.add_argument('outdir')
    ap.add_argument('--heartbeats', type=int, default=50000)
    ap.add_argument('--timeout-ms', type=int, default=10000)
    ap.add_argument('--shard', type=int, default=12)
    ap.add_argument('--jobs', type=int, default=os.cpu_count())
    ap.add_argument('--limit-theorems', type=int, default=0,
                    help='random sample of this many theorems (seed 0); 0 = all')
    ap.add_argument('--rankers', default='')
    ap.add_argument('--process-timeout', type=int, default=3600)
    a = ap.parse_args()

    keep = set(a.rankers.split(',')) if a.rankers else None
    conds = collections.OrderedDict()   # (module, thm) -> [(cond, premises)]
    for line in open(a.top10):
        f = line.rstrip('\n').split('\t')
        if len(f) < 3: continue
        thm, mod, rk = f[0], f[1], f[2]
        if keep and rk not in keep: continue
        key = (mod, thm)
        if key not in conds: conds[key] = [('none', '')]
        conds[key].append((rk, f[3] if len(f) > 3 else ''))
    keys = list(conds)
    if a.limit_theorems:
        random.Random(0).shuffle(keys)
        keys = sorted(keys[:a.limit_theorems], key=list(conds).index)
    bymod = collections.defaultdict(list)
    for k in keys: bymod[k[0]].append(k[1])

    os.makedirs(os.path.join(a.outdir, 'shards'), exist_ok=True)
    jobs = []
    for mod, thms in bymod.items():
        src = os.path.join(MATHLIB, mod.replace('.', '/') + '.lean')
        for i in range(0, len(thms), a.shard):
            name = f'{mod}.{i // a.shard}'
            tasks = os.path.join(a.outdir, 'shards', name + '.tasks.tsv')
            with open(tasks, 'w') as h:
                for t in thms[i:i + a.shard]:
                    for c, ps in conds[(mod, t)]:
                        h.write(f'{t}\t{c}\t{ps}\n')
            jobs.append((os.path.getsize(src), name, mod, src, tasks))
    jobs.sort(reverse=True)
    with open(os.path.join(a.outdir, 'config.json'), 'w') as h:
        json.dump({'heartbeats': a.heartbeats, 'timeout_ms': a.timeout_ms, 'shard': a.shard,
                   'theorems': len(keys), 'modules': len(bymod), 'shards': len(jobs),
                   'top10': os.path.abspath(a.top10), 'limit_theorems': a.limit_theorems}, h)

    def run(job):
        _, name, mod, src, tasks = job
        out = os.path.join(a.outdir, 'shards', name + '.jsonl')
        done = os.path.join(a.outdir, 'shards', name + '.done')
        if os.path.exists(done): return name, 'cached', 0
        t0 = time.time()
        with open(os.path.join(a.outdir, 'shards', name + '.log'), 'w') as log:
            try:
                p = subprocess.run([os.path.join(HERE, 'lean.sh'), '--run', os.path.join(HERE, 'Closure.lean'),
                                    src, mod, tasks, out, str(a.heartbeats), str(a.timeout_ms)],
                                   stdout=log, stderr=log, timeout=a.process_timeout)
                rc = p.returncode
            except subprocess.TimeoutExpired:
                rc = 'process-timeout'
        dt = time.time() - t0
        if rc == 0:
            open(done, 'w').write(f'{dt:.1f}\n')
        return name, rc, dt

    t0 = time.time()
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        futs = [ex.submit(run, j) for j in jobs]
        for n, fut in enumerate(cf.as_completed(futs), 1):
            name, rc, dt = fut.result()
            print(f'[{time.time() - t0:7.0f}s] {n}/{len(jobs)} {name} rc={rc} {dt:.0f}s', flush=True)
    print(f'wall {time.time() - t0:.0f}s', flush=True)


if __name__ == '__main__':
    main()
