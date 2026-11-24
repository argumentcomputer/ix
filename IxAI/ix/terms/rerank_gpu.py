"""Second-stage scorers over the features written by `rerank_feats.py`.

    rerank_gpu.py FEATS_DIR EXPERIMENT [--seeds N] [--test] [--out FILE]

A scorer maps a candidate's transformed features (`rerank_feats.NAMES`) to a
score; candidates are ranked by it over the whole accessible library. Scorers
are fitted on candidate pools with a softmax loss, then evaluated exactly over
every candidate. Validation numbers for a scorer fitted on the validation
modules are 5-fold cross-validated by module. `--test` also reports the test
modules and saves per-query results for bootstrapping.

Scorers:
  linear   score = w . x
  inter    score = w . x + same * (v . x): separate weights for candidates in
           the query's own module
  mlp      a one-hidden-layer ReLU network over x and the same-module indicator,
           plus the `inter` linear term

FITSET `fixed` is `fusion_gpu.py`'s six-weight head at its printed weights, `val` fits on the validation pools, `train` on the training sample,
`both` on both, and `dom` on both with an extra `inter` term that is applied
only to training queries. The extra term absorbs how training queries differ
(their encoder features are optimistic, the encoder having been fitted on
them) and is dropped when scoring held-out queries.
"""
import argparse, json, os, sys, time
import numpy as np, torch
from encoder_gpu import load_meta, DEV, log
from rerank_feats import NAMES, RAW, transform

BASE6 = ['z_dense', 'z_v_idf', 'z_v_enc', 'z_idf', 'z_same', 'z_used']
SAME = NAMES.index('z_same')
HEAD6 = [1.96, 0.02, 0.01, 0.11, 0.01, 0.37]   # fusion_gpu.py's six-weight head, as printed
RARE = 20                      # a gold premise used by at most this many training proofs counts as rare

class Data:
    def __init__(self, d):
        self.d = d; M = load_meta(); self.M = M
        lib_cid, lib_mod = M['lib_cid'], M['lib_mod']
        self.first = {}
        for r, c in enumerate(lib_cid): self.first.setdefault(int(c), r)
        self.rows_of = {}
        for r, c in enumerate(lib_cid): self.rows_of.setdefault(int(c), []).append(r)
        train_all = np.nonzero((M['item_split'] == 0) & ~(lib_mod[M['item_row']] % 50 == 7))[0]
        gptr, gold = M['gold_ptr'], M['gold']
        self.use = np.zeros(len(lib_cid)); self.mod_use = {}
        for i in train_all:
            d_m = self.mod_use.setdefault(int(lib_mod[M['item_row'][i]]), {})
            for c in gold[gptr[i]:gptr[i + 1]]:
                r = self.first[int(c)]; self.use[r] += 1; d_m[r] = d_m.get(r, 0) + 1

    def pool(self, split):
        """Padded pool tensors: X [q, L, F] half, mask, gold, rare (used by at most RARE training
        proofs outside the query's module); plus item indices and module of each query."""
        p = lambda k: np.load('%s/%s_pool_%s.npy' % (self.d, split, k), mmap_mode='r')
        ptr, X, g, prow = p('ptr'), p('X'), p('gold'), p('row'); items = np.load('%s/%s_items.npy' % (self.d, split))
        keep = [q for q in range(len(items)) if g[ptr[q]:ptr[q + 1]].any()]
        L = max(int(ptr[q + 1] - ptr[q]) for q in keep)
        Xp = torch.zeros(len(keep), L, X.shape[1], dtype=torch.float16); mk = torch.zeros(len(keep), L, dtype=torch.bool); gd = torch.zeros_like(mk); rare = torch.zeros_like(mk)
        mods = self.M['lib_mod'][self.M['item_row'][items[keep]]]
        for j, q in enumerate(keep):
            a, b = ptr[q], ptr[q + 1]; Xp[j, :b - a] = torch.from_numpy(np.asarray(X[a:b])); mk[j, :b - a] = True; gd[j, :b - a] = torch.from_numpy(np.asarray(g[a:b]))
            rows = np.asarray(prow[a:b]); mu = self.mod_use.get(int(mods[j]), {})
            u = self.use[rows] - np.array([mu.get(int(r), 0) for r in rows]) if mu else self.use[rows]
            rare[j, :b - a] = torch.from_numpy(u <= RARE)
        return dict(X=Xp, mask=mk, gold=gd, rare=rare, items=items[keep], mod=mods)

    def full(self, split):
        p = lambda k: np.load('%s/%s_full_%s.npy' % (self.d, split, k), mmap_mode='r')
        return dict(ptr=p('ptr'), row=p('row'), raw=p('raw'), items=np.load('%s/%s_items.npy' % (self.d, split)))

class Scorer(torch.nn.Module):
    def __init__(self, cols, kind, hidden=32, seed=0):
        super().__init__(); torch.manual_seed(seed)
        self.cols = torch.tensor([NAMES.index(c) for c in cols], device=DEV); self.kind = kind; n = len(cols)
        self.w = torch.nn.Parameter(torch.zeros(n, device=DEV)); self.v = torch.nn.Parameter(torch.zeros(n, device=DEV))
        if kind == 'mlp':
            self.l1 = torch.nn.Linear(n + 1, hidden).to(DEV); self.l2 = torch.nn.Linear(hidden, 1).to(DEV)
            torch.nn.init.zeros_(self.l2.weight)
        self.u = torch.nn.Parameter(torch.zeros(n, device=DEV)); self.u2 = torch.nn.Parameter(torch.zeros(n, device=DEV))

    def forward(self, Xall, dom=False):
        X = Xall[..., self.cols].float(); same = (Xall[..., SAME] > 0).float()
        s = X @ self.w
        if dom: s = s + X @ self.u + same * (X @ self.u2)
        if self.kind in ('inter', 'mlp'): s = s + same * (X @ self.v)
        if self.kind == 'mlp': s = s + self.l2(torch.relu(self.l1(torch.cat([X, same[..., None]], -1)))).squeeze(-1)
        return s

def loss_fn(s, mask, gold, kind, rare=None):
    """`multi`: one softmax per query over all gold; `each`: one softmax per gold premise
    against the non-gold candidates; `rareK`: `each` with rare gold weighted K times."""
    s = s.masked_fill(~mask, -1e4)
    if kind == 'multi':
        return (torch.logsumexp(s, 1) - torch.logsumexp(s.masked_fill(~gold, -1e4), 1)).mean()
    neg = torch.logsumexp(s.masked_fill(gold, -1e4), 1, keepdim=True)
    per = torch.logaddexp(s, neg) - s
    wt = gold.float()
    if kind.startswith('rare'): wt = wt * (1 + (float(kind[4:]) - 1) * rare.float())
    return ((per * wt).sum(1) / wt.sum(1)).mean()

def fit(pools, cols, kind, seed=0, steps=1500, batch=256, lr=0.02, loss='each', hidden=32, wd=0.0):
    model = Scorer(cols, kind, hidden, seed)
    opt = torch.optim.Adam(model.parameters(), lr=lr, weight_decay=wd)
    g = torch.Generator().manual_seed(seed)
    sizes = [len(p['X']) for p in pools]; tot = sum(sizes)
    for step in range(steps):
        if step == int(steps * 0.7):
            for pg in opt.param_groups: pg['lr'] = lr * 0.2
        idx = torch.randint(tot, (batch,), generator=g)
        parts = []; off = 0
        lossv = 0.0
        for p, n in zip(pools, sizes):
            sel = idx[(idx >= off) & (idx < off + n)] - off; off += n
            if len(sel) == 0: continue
            b = {k: p[k][sel].to(DEV, non_blocking=True) for k in ('X', 'mask', 'gold', 'rare')}
            lossv = lossv + loss_fn(model(b['X'], p.get('dom', False)), b['mask'], b['gold'], loss, b['rare']) * len(sel) / batch
        opt.zero_grad(); lossv.backward(); opt.step()
    return model

def subset(p, sel):
    sel_t = torch.from_numpy(sel)
    return dict(X=p['X'][sel_t], mask=p['mask'][sel_t], gold=p['gold'][sel_t], rare=p['rare'][sel_t], items=p['items'][sel], mod=p['mod'][sel])

@torch.no_grad()
def evaluate(D, F, model, qsel=None, chunk=24, tops=None):
    """Exact ranking over every candidate. Returns per-query arrays; appends each query's
    top ten library rows to `tops` when given."""
    M = D.M; lib_cid, lib_mod, item_row, gptr, gold = M['lib_cid'], M['lib_mod'], M['item_row'], M['gold_ptr'], M['gold']
    items = F['items']; ptr = F['ptr']; qs = np.arange(len(items)) if qsel is None else qsel
    out = {k: np.zeros(len(qs)) for k in ('h1', 'h5', 'h10', 'n', 'rr', 'own_h', 'own_n', 'seen_h', 'seen_n', 'new_h', 'new_n', 'rare_h', 'rare_n')}
    for s in range(0, len(qs), chunk):
        qq = qs[s:s + chunk]; lens = [int(ptr[q + 1] - ptr[q]) for q in qq]; L = max(lens)
        raw = torch.zeros(len(qq), L, len(RAW), device=DEV); cand = torch.zeros(len(qq), L, dtype=torch.bool, device=DEV)
        rows = torch.full((len(qq), L), -1, dtype=torch.long, device=DEV)
        for k, q in enumerate(qq):
            a, b = ptr[q], ptr[q + 1]
            raw[k, :b - a] = torch.from_numpy(np.asarray(F['raw'][a:b])).to(DEV); cand[k, :b - a] = True
            rows[k, :b - a] = torch.from_numpy(np.asarray(F['row'][a:b]).astype(np.int64)).to(DEV)
        S = model(transform(raw, cand)).masked_fill(~cand, -1e30)
        top = rows.gather(1, S.topk(10, dim=1).indices).cpu().numpy()
        if tops is not None: tops.extend(top)
        for k, q in enumerate(qq):
            j = s + k; i = items[q]; gs = gold[gptr[i]:gptr[i + 1]]; gset = set(int(c) for c in gs)
            topc = [int(lib_cid[x]) for x in top[k]]
            out['h1'][j] = len(gset & set(topc[:1])); out['h5'][j] = len(gset & set(topc[:5])); out['h10'][j] = len(gset & set(topc)); out['n'][j] = len(gs)
            t10 = set(topc)
            for c in gs:
                gr = D.first[int(c)]; cl = 'own' if lib_mod[gr] == lib_mod[item_row[i]] else ('seen' if D.use[gr] > 0 else 'new')
                out[cl + '_n'][j] += 1; out[cl + '_h'][j] += int(c) in t10
                if D.use[gr] <= RARE: out['rare_n'][j] += 1; out['rare_h'][j] += int(c) in t10
            grow = torch.tensor([x for c in gs for x in D.rows_of[int(c)]], device=DEV)
            hit = torch.isin(rows[k], grow) & cand[k]
            if hit.any():
                best = S[k][hit].max(); out['rr'][j] = 1.0 / (int((S[k] > best).sum()) + 1)
    return out

def summary(o):
    n = o['n'].sum()
    return dict(r1=100 * o['h1'].sum() / n, r5=100 * o['h5'].sum() / n, r10=100 * o['h10'].sum() / n, mrr=o['rr'].mean(),
                own=100 * o['own_h'].sum() / max(o['own_n'].sum(), 1), seen=100 * o['seen_h'].sum() / max(o['seen_n'].sum(), 1),
                new=100 * o['new_h'].sum() / max(o['new_n'].sum(), 1), rare=100 * o['rare_h'].sum() / max(o['rare_n'].sum(), 1))

def fmt(r): return '%5.1f %5.1f %5.1f %6.3f | own %5.1f used %5.1f unused %5.1f | rare %5.1f' % (r['r1'], r['r5'], r['r10'], r['mrr'], r['own'], r['seen'], r['new'], r['rare'])

FSETS = {
    'base6': BASE6,
    'base6+gap': BASE6 + ['z_gap'],
    'rank': ['r_dense', 'r_v_idf', 'r_v_enc', 'r_idf', 'r_cos', 'r_used', 'z_same', 'z_gap'],
    'zrank': BASE6 + ['r_dense', 'r_v_idf', 'r_v_enc', 'r_idf', 'r_used', 'z_gap'],
    'all10': [n for n in NAMES if not any(x in n for x in ('16', 'qx'))],
    'all': NAMES,
}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('feats'); ap.add_argument('variants', help='comma list of FSET:KIND:FITSET[:LOSS], FITSET in val|train|both|dom|fixed')
    ap.add_argument('--seeds', type=int, default=1); ap.add_argument('--test', action='store_true'); ap.add_argument('--out', default='')
    ap.add_argument('--steps', type=int, default=1500); ap.add_argument('--hidden', type=int, default=32)
    args = ap.parse_args()
    D = Data(args.feats)
    pv = D.pool('val'); fv = D.full('val'); log('val pool', tuple(pv['X'].shape))
    pt = ptd = None
    if any(':train' in v or ':both' in v or ':dom' in v for v in args.variants.split(',')):
        pt = D.pool('train'); log('train pool', tuple(pt['X'].shape))
        ptd = dict(pt, dom=True)
    ft = D.full('test') if args.test else None
    # validation queries by fold (5 folds of modules); folds index the val pool, evaluation indexes the full val arrays
    fmod = D.M['lib_mod'][D.M['item_row'][fv['items']]]
    fold_of = {m: k % 5 for k, m in enumerate(np.unique(fmod))}
    pfold = np.array([fold_of[m] for m in pv['mod']]); qfold = np.array([fold_of[m] for m in fmod])
    results = {}
    for var in args.variants.split(','):
        parts = var.split(':'); fs, kind, fitset = parts[:3]; lossk = parts[3] if len(parts) > 3 else 'each'
        cols = FSETS[fs]; vals = []; tests = []
        for seed in range(args.seeds):
            kw = dict(seed=seed, steps=args.steps, loss=lossk, hidden=args.hidden)
            if fitset == 'fixed':
                m = Scorer(BASE6, 'linear'); m.w.data = torch.tensor(HEAD6, device=DEV); vo = evaluate(D, fv, m)
            elif fitset == 'train':
                m = fit([pt], cols, kind, **kw); vo = evaluate(D, fv, m)
            else:
                parts_o = []
                for f in range(5):
                    tr = subset(pv, np.nonzero(pfold != f)[0]); pools = {'val': [tr], 'both': [tr, pt], 'dom': [tr, ptd]}[fitset]
                    parts_o.append(evaluate(D, fv, fit(pools, cols, kind, **kw), np.nonzero(qfold == f)[0]))
                vo = {k: np.concatenate([p[k] for p in parts_o]) for k in parts_o[0]}
                if args.test or args.out: m = fit({'val': [pv], 'both': [pv, pt], 'dom': [pv, ptd]}[fitset], cols, kind, **kw)
            rv = summary(vo); vals.append(rv); log('%-28s seed %d  val  %s' % (var, seed, fmt(rv)))
            if args.test:
                to = evaluate(D, ft, m); rt = summary(to); tests.append(rt); log('%-28s seed %d  test %s' % (var, seed, fmt(rt)))
                if args.out: np.savez('%s.%s.s%d.npz' % (args.out, var.replace(':', '_'), seed), **to)
            if args.out:
                sd = {k: v.detach().cpu().numpy().tolist() for k, v in m.state_dict().items()}
                json.dump(dict(cols=cols, kind=kind, state=sd), open('%s.%s.s%d.json' % (args.out, var.replace(':', '_'), seed), 'w'))
        agg = lambda rs: {k: (np.mean([r[k] for r in rs]), np.std([r[k] for r in rs])) for k in rs[0]}
        results[var] = dict(val=agg(vals), test=agg(tests) if tests else None)
        a = results[var]['val']; print('%-28s VAL  R@10 %.2f +- %.2f  MRR %.3f +- %.3f' % (var, a['r10'][0], a['r10'][1], a['mrr'][0], a['mrr'][1]), flush=True)

if __name__ == '__main__':
    main()
