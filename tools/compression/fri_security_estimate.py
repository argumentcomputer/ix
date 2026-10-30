#!/usr/bin/env python3
"""Soundness estimate for a saved FRI compression key under candidate parameters.

Reads JSON from `fri_sizing --statistics`, derives the instance facts
the bounds need (largest trace, batched columns, folded constraints, maximum
constraint degree, lookup rows and width) and prints every error term for the
unique-decoding, Johnson and conjectured regimes. Hypothetical shapes use the
same overrides as the `fri_sizing` example: `--drop` omits circuits and
`--set index:log_height:main_width` reassigns a circuit's height or width.

Formulas: UDR, conjectured and DEEP/ALI terms follow p3-security at Plonky3
3152b14a; the Johnson commit and batching terms are printed both in that
revision's BCHKS25 form and in the DKT26 line-count form of Plonky3 main at
4615dcd. Lookups use multi-stark's documented `(W + 2) N / |F|` bound. The
union bound is reported as the minimum term, as p3-security does.
"""
import argparse
import math
import json
import sys
from pathlib import Path

log2 = math.log2
FIELD_BITS = 128  # degree-2 Goldilocks extension
COLLISION_BITS = 128  # BLAKE3


def apply_overrides(circuits, drop, sets):
    out = []
    for i, c in enumerate(circuits):
        if i in drop:
            continue
        c = dict(c)
        if i in sets:
            log_h, main = sets[i]
            c['height'] = 1 << log_h
            c['main'] = main
        out.append(c)
    return out


def instance(circuits, log_blowup):
    quotient = lambda c: 1 << max(0, (max(c['max_degree'], 2) - 2).bit_length())
    return dict(
        log_trace=max(c['height'] for c in circuits).bit_length() - 1,
        columns=sum(c['main'] + c['pre'] + c['stage2'] + 2 * quotient(c) for c in circuits),
        constraints=sum(c['zeros'] + 2 * max(1, -(-c['lookups'] // c['group'])) for c in circuits),
        max_degree=max(c['max_degree'] for c in circuits),
        lookup_rows=sum(c['height'] * c['lookups'] for c in circuits),
        lookup_width=max(c['max_lookup_width'] for c in circuits),
        combo=2,
    )


def terms(inst, log_blowup, queries, query_pow, log_arity, commit_pow):
    lt, F = inst['log_trace'], FIELD_BITS
    n, k, fold = 2.0 ** (lt + log_blowup), 2.0 ** lt, (1 << log_arity) - 1
    rho = 2.0 ** -log_blowup
    ali = F - log2(inst['constraints'])
    deep = F - log2(inst['max_degree'] * (k + inst['combo'] - 1) + (k - 1))
    lookup = F - log2((inst['lookup_width'] + 2) * inst['lookup_rows'])
    nf = inst['columns']
    out = {}
    alpha = (1 + (k + inst['combo']) / n) / 2
    out['unique decoding'] = dict(
        ALI=ali, DEEP=deep, lookup=lookup,
        batching=F - ((lt + log_blowup) + log2(nf - 1)),
        commit=F - log2(fold * (n + 1)) + commit_pow,
        query=query_pow - queries * log2(alpha), collision=COLLISION_BITS)
    for label, line_count in (('Johnson, BCHKS25 (3152b14a)', None), ('Johnson, DKT26 (4615dcd)', True)):
        best = None
        for m in range(3, 300):
            ms = m + 0.5
            if line_count:
                lc = 3 + (lt + log_blowup) + 3 * log2(ms) - log2(3) - (log2(1 - 2.0 ** -lt) - log_blowup)
                commit_linear = F - lc - log2(fold) + commit_pow
                batching = F - (lc + log2(nf - 1))
            else:
                pp = 1 - math.sqrt(rho) * (1 + 0.5 / m)
                eps = ((2 * ms ** 5 + 3 * ms * pp * rho) * n / (3 * rho * math.sqrt(rho)) + ms / math.sqrt(rho)) * fold
                commit_linear = F - log2(max(eps, 1.0)) + commit_pow
                batching = F - ((lt + log_blowup) + log2(2 * ms ** 5 / 3) + 1.5 * log_blowup + log2(nf - 1))
            commit = min(commit_linear,
                         F - log_arity - log2(n + 1) - log2(2 * m + 1) + 0.5 * log2(rho) + commit_pow)
            L = ms / math.sqrt(rho)
            d = dict(ALI=F - log2(L) - log2(inst['constraints']),
                     DEEP=F - log2(L) - log2(inst['max_degree'] * (k + inst['combo'] - 1) + (k - 1)),
                     lookup=lookup, batching=batching, commit=commit,
                     query=query_pow - queries * log2((1 + 0.5 / m) * math.sqrt(rho)),
                     collision=COLLISION_BITS)
            if best is None or min(d.values()) > min(best[1].values()):
                best = (m, d)
        out['%s, m=%d' % (label, best[0])] = best[1]
    eta = ((math.log2(math.e) + log_blowup) * rho) / F
    out['conjectured (2025/2010)'] = dict(
        ALI=ali, DEEP=deep, lookup=lookup,
        commit=F - log2(fold * (n + 1)) + commit_pow,
        query=queries * (-log2(rho + eta)) + query_pow, collision=COLLISION_BITS)
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('statistics', help='Rust-exported key statistics JSON, or - for stdin')
    parser.add_argument('--queries', type=int)
    parser.add_argument('--query-pow', type=int)
    parser.add_argument('--commit-pow', type=int)
    parser.add_argument('--log-arity', type=int)
    parser.add_argument('--log-blowup', type=int)
    parser.add_argument('--drop', default='', help='comma-separated circuit indices to omit')
    parser.add_argument('--set', default='', help='comma-separated index:log_height:main_width overrides')
    args = parser.parse_args()
    key = json.load(sys.stdin) if args.statistics == '-' else json.loads(Path(args.statistics).read_text())
    drop = {int(i) for i in args.drop.split(',') if i}
    sets = {}
    for item in args.set.split(','):
        if item:
            i, log_h, main = (int(x) for x in item.split(':'))
            sets[i] = (log_h, main)
    circuits = apply_overrides(key['circuits'], drop, sets)
    log_blowup = args.log_blowup if args.log_blowup is not None else key['log_blowup']
    inst = instance(circuits, log_blowup)
    queries = args.queries if args.queries is not None else key['num_queries']
    query_pow = args.query_pow if args.query_pow is not None else key['query_pow']
    commit_pow = args.commit_pow if args.commit_pow is not None else key['commit_pow']
    log_arity = args.log_arity if args.log_arity is not None else key['max_log_arity']
    print('key: %d circuits (%d after overrides), blowup 2^%d, %d queries, query pow %d, commit pow %d, arity 2^%d'
          % (len(key['circuits']), len(circuits), log_blowup, queries, query_pow, commit_pow, log_arity))
    print('instance: trace 2^%d, %d batched columns, %d constraints, max degree %d, lookup rows %d, lookup width %d'
          % (inst['log_trace'], inst['columns'], inst['constraints'], inst['max_degree'],
             inst['lookup_rows'], inst['lookup_width']))
    for regime, d in terms(inst, log_blowup, queries, query_pow, log_arity, commit_pow).items():
        limiting = min(d, key=d.get)
        print('  %-32s %6.2f bits (limited by %s)   %s' % (
            regime, d[limiting], limiting, '  '.join('%s %.2f' % kv for kv in d.items())))


if __name__ == '__main__':
    main()
