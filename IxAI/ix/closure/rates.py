#!/usr/bin/env python3
"""Closure rate of every condition in one or more run directories, over the theorems all of them attempted.

usage: rates.py [PREFIX=]OUTDIR [[PREFIX=]OUTDIR ...] [--vs CONDITION]

Reads each OUTDIR/shards/*.jsonl; with a prefix, that directory's conditions other than `none` and
`gold` are named PREFIX/CONDITION, so runs that reuse condition names can be compared. With --vs, every condition is also compared with that one on the
same theorems: closed by this one only, by the other only, and the exact two-sided sign test.
"""
import collections, glob, json, math, sys

def sign_test(b, c):
    n = b + c
    if n == 0: return 1.0
    return min(1.0, 2 * sum(math.comb(n, i) for i in range(min(b, c) + 1)) / 2 ** n)

def main():
    argv = sys.argv[1:]; vs = None
    if '--vs' in argv: i = argv.index('--vs'); vs = argv[i + 1]; del argv[i:i + 2]
    res = collections.defaultdict(dict); used = collections.defaultdict(list)
    for d in argv:
        pre, d = d.split('=', 1) if '=' in d else ('', d)
        for path in glob.glob(d + '/shards/*.jsonl'):
            for line in open(path):
                r = json.loads(line)
                if r.get('status') in ('closed', 'failed'):
                    if pre and r['cond'] not in ('none', 'gold'): r['cond'] = pre + '/' + r['cond']
                    res[r['cond']][r['thm']] = r['status'] == 'closed'
                    if r['status'] == 'closed':
                        used[r['cond']].append(sum(len(r.get(k, [])) for k in ('used', 'usedViaAux', 'usedViaInternal', 'usedViaEq')))
    common = set.intersection(*(set(v) for v in res.values()))
    print('%d theorems attempted under every condition' % len(common))
    print('%-16s %7s %6s' % ('condition', 'closed', 'rate') + ('   only-this only-%s   p' % vs if vs else ''))
    for c in sorted(res, key=lambda c: -sum(res[c][t] for t in common)):
        k = sum(res[c][t] for t in common); line = '%-16s %7d %6.3f' % (c, k, k / len(common))
        if vs and c != vs:
            a = sum(res[c][t] and not res[vs][t] for t in common); b = sum(res[vs][t] and not res[c][t] for t in common)
            line += '   %9d %9d   %.3g' % (a, b, sign_test(a, b))
        print(line)

if __name__ == '__main__':
    main()
