"""Write the top premises of trained encoders by name, for the closure harness.

    toplists.py OUT.tsv val|test [--k 10] [--sample N] NAME=RUN.pt ...

For every theorem of the split this writes one line per run,
`THEOREM<TAB>MODULE<TAB>NAME<TAB>p1,p2,...`, with the run's `k` best
accessible library theorems by query-premise similarity, and a `gold` line
with the premises of the theorem's proof. `--sample` keeps a fixed random
subset of the theorems.
"""
import sys
import numpy as np, torch
from encoder_gpu import load_meta, DEV, DATA, log

def main():
    argv = sys.argv[1:]; k = 10; sample = 0
    if '--k' in argv: i = argv.index('--k'); k = int(argv[i + 1]); del argv[i:i + 2]
    if '--sample' in argv: i = argv.index('--sample'); sample = int(argv[i + 1]); del argv[i:i + 2]
    out_path, split = argv[0], argv[1]; runs = [a.split('=', 1) for a in argv[2:]]
    M = load_meta()
    lib_mod, lib_decl, lib_cid, reach = M['lib_mod'], M['lib_decl'], M['lib_cid'], M['reach']
    item_row, gptr, gold = M['item_row'], M['gold_ptr'], M['gold']
    first = {}
    for r, c in enumerate(lib_cid): first.setdefault(int(c), r)
    mod_name = []; row_name = []
    for line in open(DATA + '/mathlib-full/decls.tsv'):
        f = line.rstrip('\n').split('\t')
        if f[0] == 'mod': mod_name.append(f[2])
        elif f[0] == 'lib': row_name.append(f[1])
    lm = torch.from_numpy(lib_mod).to(DEV); ld = torch.from_numpy(lib_decl).to(DEV); lc = torch.from_numpy(lib_cid).to(DEV)
    reach_t = torch.from_numpy(reach).to(DEV)
    lines = {}; items = None
    for name, path in runs:
        run = torch.load(path, weights_only=False)
        its = run[split]; Q = run['Q' + split].to(DEV)
        if items is None:
            items = its; pick = np.arange(len(items))
            if sample: pick = np.sort(np.random.default_rng(0).permutation(len(items))[:sample])
        assert np.array_equal(its, items)
        Prow = run['P'].to(DEV)[torch.from_numpy(np.searchsorted(run['lib_u'], lib_cid)).to(DEV)]
        for s in range(0, len(pick), 256):
            sel = pick[s:s + 256]; it = items[sel]; r = torch.from_numpy(item_row[it]).to(DEV); tm = lm[r]; td = ld[r]
            cand = reach_t[tm][:, lm] | ((lm[None, :] == tm[:, None]) & (ld[None, :] < td[:, None]))
            cand &= lc[None, :] != lc[r][:, None]
            top = (Q[torch.from_numpy(sel).to(DEV)] @ Prow.T).masked_fill(~cand, -1e30).topk(k, dim=1).indices.cpu().numpy()
            for j, i in enumerate(it):
                lines.setdefault(int(i), []).append((name, ','.join(row_name[x] for x in top[j])))
        log('ranked', name)
    with open(out_path, 'w') as out:
        for i in items[pick]:
            thm = row_name[item_row[i]]; mod = mod_name[lib_mod[item_row[i]]]
            out.write('%s\t%s\tgold\t%s\n' % (thm, mod, ','.join(row_name[first[int(c)]] for c in gold[gptr[i]:gptr[i + 1]])))
            for name, names in lines[int(i)]: out.write('%s\t%s\t%s\t%s\n' % (thm, mod, name, names))
    log('wrote', out_path, len(pick), 'theorems')

if __name__ == '__main__':
    main()
