#!/usr/bin/env python3
"""Aggregates the shard outputs of run.py into closure rates and paired comparisons.

usage: report.py OUTDIR      writes OUTDIR/results.jsonl, OUTDIR/table.md, OUTDIR/summary.json
"""
import collections, glob, json, math, os, sys


def sign_test(b, c):
    """Exact two-sided binomial sign test on discordant pairs b and c."""
    n = b + c
    if n == 0: return 1.0
    k = min(b, c)
    p = sum(math.comb(n, i) for i in range(k + 1)) / 2 ** n
    return min(1.0, 2 * p)


def wilson(k, n, z=1.96):
    if n == 0: return (0.0, 0.0)
    p = k / n; d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d; h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (c - h, c + h)


def paired_ci(b, c, n, z=1.96):
    """Normal-approximation interval for the difference of paired proportions (b - c) / n."""
    if n == 0: return (0.0, 0.0)
    d = (b - c) / n
    var = ((b + c) / n - d * d) / n
    h = z * math.sqrt(max(var, 0.0))
    return (d - h, d + h)


def main():
    out = sys.argv[1]
    rows = []
    for f in sorted(glob.glob(os.path.join(out, 'shards', '*.jsonl'))):
        for line in open(f):
            line = line.strip()
            if line: rows.append(json.loads(line))
    cfg = json.load(open(os.path.join(out, 'config.json')))
    # Theorems that a shard was given but did not report (crash, process timeout).
    expected = collections.defaultdict(set)
    for f in glob.glob(os.path.join(out, 'shards', '*.tasks.tsv')):
        for line in open(f):
            t, c = line.split('\t')[:2]
            expected[t].add(c)
    seen = collections.defaultdict(dict)
    for r in rows: seen[r['thm']][r['cond']] = r
    lost = sorted(t for t in expected if t not in seen)
    with open(os.path.join(out, 'results.jsonl'), 'w') as h:
        for r in rows: h.write(json.dumps(r) + '\n')

    conds = ['none', 'gold', 'knn', 'encoder', 'head', 'idf']
    conds = [c for c in conds if any(c in v for v in expected.values())]
    skipped = collections.Counter()
    attempted = {}
    for t, cs in seen.items():
        r0 = next(iter(cs.values()))
        if r0['status'] == 'skipped':
            skipped[r0['reason']] += 1
            continue
        if not all(c in cs for c in conds):
            skipped['incomplete conditions'] += 1
            continue
        attempted[t] = cs
    n = len(attempted)
    lines = [f"# Proof closure ({n} theorems attempted; heartbeats {cfg['heartbeats']}, "
             f"timeout {cfg['timeout_ms']} ms per tactic)", '',
             '| condition | attempted | closed | rate | 95% CI | simp_all | aesop | grind | mean given | mean accessible | mean used per closed | incl. via aux/internal/eq |',
             '|---|---|---|---|---|---|---|---|---|---|---|---|']
    summary = {'theorems_given': len(expected), 'attempted': n, 'skipped': dict(skipped),
               'lost': len(lost), 'conditions': {}}
    closed = {c: {t for t, cs in attempted.items() if cs[c]['status'] == 'closed'} for c in conds}
    for c in conds:
        k = len(closed[c]); lo, hi = wilson(k, n)
        by = collections.Counter(attempted[t][c]['tactic'] for t in closed[c])
        g = sum(attempted[t][c]['given'] for t in attempted) / max(n, 1)
        acc = sum(attempted[t][c]['accessible'] for t in attempted) / max(n, 1)
        # Outputs written before premise use was recorded have no `used` field.
        rec = [attempted[t][c] for t in closed[c] if 'used' in attempted[t][c]]
        u = sum(len(r['used']) for r in rec) / len(rec) if rec else float('nan')
        ua = sum(len(r['used']) + len(r['usedViaAux']) + len(r.get('usedViaInternal', [])) + len(r['usedViaEq']) for r in rec) / len(rec) if rec else float('nan')
        lines.append(f"| {c} | {n} | {k} | {k / max(n, 1):.3f} | [{lo:.3f}, {hi:.3f}] | "
                     f"{by['simp_all']} | {by['aesop']} | {by['grind']} | {g:.2f} | {acc:.2f} | {u:.2f} | {ua:.2f} |")
        summary['conditions'][c] = {'closed': k, 'rate': k / max(n, 1), 'ci': [lo, hi],
                                    'by_tactic': dict(by), 'mean_given': g, 'mean_accessible': acc,
                                    'mean_used_closed': u, 'mean_used_incl_aux_closed': ua}
    lines += ['', '## Paired comparisons', '',
              '| A | B | A only | B only | both | neither | A-B rate | 95% CI | sign test p |',
              '|---|---|---|---|---|---|---|---|---|']
    pairs = [('head', 'knn'), ('head', 'encoder'), ('encoder', 'knn'), ('head', 'idf'),
             ('knn', 'idf'), ('gold', 'head'), ('gold', 'none')] + \
            [(c, 'none') for c in conds if c not in ('none', 'gold')]
    summary['pairs'] = []
    for A, B in pairs:
        if A not in closed or B not in closed: continue
        b = len(closed[A] - closed[B]); c = len(closed[B] - closed[A])
        both = len(closed[A] & closed[B]); nei = n - b - c - both
        lo, hi = paired_ci(b, c, n); p = sign_test(b, c)
        lines.append(f"| {A} | {B} | {b} | {c} | {both} | {nei} | {(b - c) / max(n, 1):+.3f} | "
                     f"[{lo:+.3f}, {hi:+.3f}] | {p:.3g} |")
        summary['pairs'].append({'A': A, 'B': B, 'A_only': b, 'B_only': c, 'both': both,
                                 'neither': nei, 'diff': (b - c) / max(n, 1), 'ci': [lo, hi], 'p': p})
    lines += ['', '## Not attempted', '']
    for r, k in skipped.most_common(): lines.append(f'- {r}: {k}')
    lines.append(f'- no output (shard crashed or timed out): {len(lost)}')
    ms = [a['ms'] for cs in attempted.values() for r in cs.values() for a in r['attempts']]
    tos = sum(1 for cs in attempted.values() for r in cs.values() for a in r['attempts']
              if a['err'].startswith('timeout') or 'maximum number of heartbeats' in a['err'])
    lines += ['', f'Tactic runs: {len(ms)}, total {sum(ms) / 1000:.0f} s, '
              f'hit heartbeat or wall-clock limit: {tos}']
    summary['tactic_runs'] = len(ms); summary['limit_hits'] = tos
    open(os.path.join(out, 'table.md'), 'w').write('\n'.join(lines) + '\n')
    json.dump(summary, open(os.path.join(out, 'summary.json'), 'w'), indent=1)
    print('\n'.join(lines))


if __name__ == '__main__':
    main()
