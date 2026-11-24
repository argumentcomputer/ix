#!/usr/bin/env python3
"""Lists, for every theorem a run closed only with premises, the premises its proofs used.

usage: used.py OUTDIR [OUTDIR ...] > USED.tsv

Reads OUTDIR/shards/*.jsonl and prints `THEOREM<TAB>p1,p2,...`: the union, over the conditions that
closed the theorem, of the handed premises the closing proof reaches (directly, through
declarations the tactic added, through earlier internal declarations, or through an equation
lemma). Theorems that the `none` condition closes are left out, since no premise was needed.
"""
import collections, glob, json, sys

def main():
    used = collections.defaultdict(set); free = set(); closed = set()
    for d in sys.argv[1:]:
        for path in glob.glob(d + '/shards/*.jsonl'):
            for line in open(path):
                r = json.loads(line)
                if r.get('status') != 'closed': continue
                if r['cond'] == 'none': free.add(r['thm']); continue
                closed.add(r['thm'])
                for k in ('used', 'usedViaAux', 'usedViaInternal', 'usedViaEq'): used[r['thm']].update(r.get(k, []))
    n = 0
    for t in sorted(closed - free):
        if used[t]: print(t + '\t' + ','.join(sorted(used[t]))); n += 1
    print('%d theorems closed only with premises, %d with a used premise recorded; %d closed without premises' % (len(closed - free), n, len(free)), file=sys.stderr)

if __name__ == '__main__':
    main()
