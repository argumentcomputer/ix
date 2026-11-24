"""Adapt a trained encoder's embeddings to the premises a solver used.

    adapt_solver.py RUN.pt USED.tsv OUT.pt [--steps 400] [--decay 1e-2]

`RUN.pt` holds the embeddings `encoder_gpu.py --save` wrote and `USED.tsv` lines
`THEOREM<TAB>p1,p2,...`: for validation theorems a solver closed, the listed
premises its proofs used (`ix/closure/used.py`). Two square maps, starting at
the identity, are fitted so that a theorem's adapted query embedding ranks the
premises the solver used above the 300 accessible premises nearest to it
before adaptation: `q (I + A)` and `p (I + B)`, renormalised.

The fit is first done on every other validation module and scored on the rest
(share of solver-used premises in the top 10 of the pool, before and after),
then repeated on all of them, and `OUT.pt` is `RUN.pt` with every
embedding passed through the second fit.
"""
import sys
import numpy as np, torch
import torch.nn.functional as Fn
from encoder_gpu import load_meta, DEV, DATA, log

def main():
    argv = sys.argv[1:]; steps = 400; decay = 1e-2
    if '--steps' in argv: i = argv.index('--steps'); steps = int(argv[i + 1]); del argv[i:i + 2]
    if '--decay' in argv: i = argv.index('--decay'); decay = float(argv[i + 1]); del argv[i:i + 2]
    run = torch.load(argv[0], weights_only=False)
    M = load_meta()
    lib_mod, lib_decl, lib_cid, reach, item_row = M['lib_mod'], M['lib_decl'], M['lib_cid'], M['reach'], M['item_row']
    row_of_name = {}; nrow = 0
    for line in open(DATA + '/mathlib-full/decls.tsv'):
        if line.startswith('lib\t'): row_of_name.setdefault(line.split('\t', 2)[1], nrow); nrow += 1
    val = run['val']; pos_of_item = {int(i): k for k, i in enumerate(val)}; item_of_row = {int(item_row[i]): int(i) for i in val}
    lm = torch.from_numpy(lib_mod).to(DEV); ld = torch.from_numpy(lib_decl).to(DEV); lc = torch.from_numpy(lib_cid).to(DEV)
    reach_t = torch.from_numpy(reach).to(DEV)
    col = torch.from_numpy(np.searchsorted(run['lib_u'], lib_cid)).to(DEV)
    P = run['P'].to(DEV); Qv = run['Qval'].to(DEV); d = P.shape[1]

    # per labelled theorem: its query, the pool (premise columns) and which of the pool the solver used
    data = []
    for line in open(argv[1]):
        f = line.rstrip('\n').split('\t')
        if f[0] not in row_of_name or row_of_name[f[0]] not in item_of_row or len(f) < 2: continue
        i = item_of_row[row_of_name[f[0]]]; r = int(item_row[i])
        cand = reach_t[lm[r]][lm] | ((lm == lm[r]) & (ld < ld[r])); cand &= lc != lc[r]
        used = torch.tensor([row_of_name[p] for p in f[1].split(',') if p in row_of_name], device=DEV, dtype=torch.long)
        used = used[cand[used]]
        if not len(used): continue
        q = Qv[pos_of_item[i]]
        top = (P[col] @ q).masked_fill(~cand, -1e30).topk(300).indices
        pool = torch.unique(col[torch.cat([top, used])]); y = torch.isin(pool, col[used])
        data.append((pos_of_item[i], pool, y, int(lib_mod[r]) // 50 % 2))
    log('labelled theorems %d, solver-used premises %d' % (len(data), sum(int(y.sum()) for _, _, y, _ in data)))

    def embed(X, A): return Fn.normalize(X + X @ A, dim=1)
    def recall(A, B, part):
        hit = tot = 0
        with torch.no_grad():
            Pa = embed(P, B)
            for k, pool, y, par in data:
                if par != part: continue
                s = Pa[pool] @ embed(Qv[k:k + 1], A)[0]
                hit += int(y[s.topk(10).indices].sum()); tot += int(y.sum())
        return 100 * hit / max(tot, 1)
    def fit(part):
        torch.manual_seed(0)
        A = torch.zeros(d, d, device=DEV, requires_grad=True); B = torch.zeros(d, d, device=DEV, requires_grad=True)
        opt = torch.optim.Adam([A, B], lr=1e-3, weight_decay=decay)
        idx = [j for j, x in enumerate(data) if part is None or x[3] == part]
        for step in range(steps):
            opt.zero_grad(); loss = 0.0; Pa = embed(P, B)
            for j in [idx[x] for x in torch.randint(len(idx), (128,)).tolist()]:
                k, pool, y, _ = data[j]
                s = 40.0 * (Pa[pool] @ embed(Qv[k:k + 1], A)[0])
                neg = torch.logsumexp(s.masked_fill(y, -1e30), 0)
                loss = loss + (torch.logaddexp(s[y], neg) - s[y]).mean()
            (loss / 128).backward(); opt.step()
        return A.detach(), B.detach()

    Z = torch.zeros(d, d, device=DEV)
    A, B = fit(0)
    log('solver-used premises of held-back validation modules in the top 10 of the pool: before %.1f%%, after fitting on the others %.1f%%' % (
        recall(Z, Z, 1), recall(A, B, 1)))
    log('the same on the modules it was fitted on: before %.1f%%, after %.1f%%' % (recall(Z, Z, 0), recall(A, B, 0)))
    A, B = fit(None)
    out = dict(run)
    with torch.no_grad():
        out['P'] = embed(P, B).cpu()
        for k in ('Qtrain', 'Qval', 'Qtest'): out[k] = embed(run[k].to(DEV), A).cpu()
    torch.save(out, argv[2]); log('wrote', argv[2])

if __name__ == '__main__':
    main()
