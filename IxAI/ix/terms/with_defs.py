"""Add the rarely mentioned definitions of each goal to its premise lists.

    with_defs.py IN.tsv OUT.tsv RANKER[,RANKER...] [--max 8] [--rare 50]

For every theorem of `IN.tsv` (closure-harness format) this writes its `gold`
line, each named ranker's line unchanged, and a line `RANKER+defs` with up to
`--max` definitions appended: constants of kind `def` that the theorem's
statement mentions and at most `--rare` library statements mention, rarest
first. A line `defs` holds those definitions alone. Solvers unfold a
definition handed to them as a premise, which no list of theorems can do.
"""
import sys, collections
import numpy as np
import encoder_gpu as E

def main():
    argv = sys.argv[1:]; mx = 8; rare = 50
    if '--max' in argv: i = argv.index('--max'); mx = int(argv[i + 1]); del argv[i:i + 2]
    if '--rare' in argv: i = argv.index('--rare'); rare = int(argv[i + 1]); del argv[i:i + 2]
    src, out, rankers = argv[0], argv[1], argv[2].split(',')
    E.DEV = 'cpu'
    M = E.load_meta(); G = E.Graph('graph_nary')
    kind = {}; addr_of = {}
    for line in open(E.ROOT + '/consts.tsv'):
        f = line.split('\t', 3); kind[int(f[0])] = f[2]; addr_of[int(f[0])] = f[1]
    name_of = {}; cid_of = {}
    id_of_addr = {a: c for c, a in addr_of.items()}
    for line in open(E.DATA + '/mathlib-full/names.tsv'):
        n, a = line.rstrip('\n').split('\t')
        if a in id_of_addr:
            c = id_of_addr[a]; cid_of[n] = c
            if c not in name_of or len(n) < len(name_of[c]): name_of[c] = n
    cnt = np.zeros(len(G.roots) + 1, dtype=np.int64)
    for c in np.unique(M['lib_cid']):
        ns = G.nodes[G.ptr[c]:G.ptr[c + 1]]; m = G.tag_np[ns] == E.REF
        cnt[np.unique(G.x_np[ns][m])] += 1
    def defs(thm):
        c = cid_of.get(thm)
        if c is None: return []
        ns = G.nodes[G.ptr[c]:G.ptr[c + 1]]; cs = np.unique(G.x_np[ns][G.tag_np[ns] == E.REF])
        cs = [int(x) for x in cs if kind.get(int(x)) == 'def' and cnt[x] <= rare and int(x) in name_of]
        cs = [x for x in cs if not name_of[x].split('.')[-1].startswith('inst')]
        return [name_of[x] for x in sorted(cs, key=lambda x: cnt[x])[:mx]]
    n = 0; total = 0
    with open(out, 'w') as h:
        for line in open(src):
            f = line.rstrip('\n').split('\t')
            if f[2] == 'gold':
                d = defs(f[0]); n += 1; total += len(d)
                h.write(line); h.write('%s\t%s\tdefs\t%s\n' % (f[0], f[1], ','.join(d)))
                h.write('%s\t%s\tgold+defs\t%s\n' % (f[0], f[1], ','.join([x for x in f[3].split(',') if x] + d) if len(f) > 3 else ','.join(d)))
            elif f[2] in rankers:
                h.write(line); h.write('%s\t%s\t%s+defs\t%s\n' % (f[0], f[1], f[2], ','.join(f[3].split(',') + d)))
    print('theorems %d, definitions added per theorem %.2f' % (n, total / max(n, 1)))

if __name__ == '__main__':
    main()
