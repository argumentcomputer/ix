"""Rerank the top candidates of a feature scorer using the embeddings themselves.

    rerank_embed.py FEATS_DIR RUN.pt [--kind diag|mlp] [--top 200] [--seeds N] [--test] [--out PREFIX]

Stage one is a `rerank_gpu` scorer (`all` features, `inter` kind) ranking every
candidate. Stage two rescores its top `--top` candidates with

  diag   s1 + w . (q * p) + v . x            (q, p query and premise embeddings,
                                              x the transformed features)
  mlp    s1 + MLP([q * p, x, same])          one hidden ReLU layer

and leaves the rest in stage-one order below them. Both stages are fitted on
validation modules only (the encoder was fitted on the training theorems, so
their q * p is not representative); validation numbers are 5-fold
cross-validated by module, each fold's stage one and stage two fitted without
that fold.
"""
import argparse
import numpy as np, torch
from encoder_gpu import load_meta, DEV, log
from rerank_feats import NAMES, RAW, transform
from rerank_gpu import Data, Scorer, fit, subset, summary, fmt, FSETS, SAME, RARE

@torch.no_grad()
def collect(D, F, model, Q, Prow, top, chunk=48):
    """Stage-one ranking over every candidate; per query the top rows with features, plus gold rows outside them."""
    M = D.M; lib_cid, gptr, gold = M['lib_cid'], M['gold_ptr'], M['gold']
    items = F['items']; ptr = F['ptr']; out = []
    for s in range(0, len(items), chunk):
        qq = np.arange(s, min(s + chunk, len(items))); lens = [int(ptr[q + 1] - ptr[q]) for q in qq]; L = max(lens)
        raw = torch.zeros(len(qq), L, len(RAW), device=DEV); cand = torch.zeros(len(qq), L, dtype=torch.bool, device=DEV)
        rows = torch.full((len(qq), L), -1, dtype=torch.long, device=DEV)
        for k, q in enumerate(qq):
            a, b = ptr[q], ptr[q + 1]
            raw[k, :b - a] = torch.from_numpy(np.asarray(F['raw'][a:b])).to(DEV); cand[k, :b - a] = True
            rows[k, :b - a] = torch.from_numpy(np.asarray(F['row'][a:b]).astype(np.int64)).to(DEV)
        X = transform(raw, cand); S = model(X).masked_fill(~cand, -1e30)
        ti = S.topk(top, dim=1).indices
        for k, q in enumerate(qq):
            i = items[q]; gs = gold[gptr[i]:gptr[i + 1]]
            grow = torch.tensor([x for c in gs for x in D.rows_of[int(c)]], device=DEV)
            isg = torch.isin(rows[k], grow) & cand[k]
            rank1 = int((S[k] > S[k][isg].max()).sum()) + 1 if isg.any() else 0
            extra = torch.nonzero(isg).flatten(); extra = extra[~torch.isin(extra, ti[k])]
            idx = torch.cat([ti[k], extra])
            r = rows[k, idx]
            out.append(dict(q=q, rows=r.cpu().numpy(), X=X[k, idx].half(), s1=S[k, idx], gold=isg[idx], qv=Q[q].to(DEV),
                            p=Prow[r].half(), rank1=rank1, ntop=top))
    return out

class Stage2(torch.nn.Module):
    def __init__(self, kind, d, nf, hidden=64, seed=0):
        super().__init__(); torch.manual_seed(seed); self.kind = kind
        self.a = torch.nn.Parameter(torch.ones(1, device=DEV))
        if kind == 'diag':
            self.w = torch.nn.Parameter(torch.zeros(d, device=DEV)); self.v = torch.nn.Parameter(torch.zeros(nf, device=DEV))
            self.vs = torch.nn.Parameter(torch.zeros(nf, device=DEV))
        else:
            self.l1 = torch.nn.Linear(d + nf + 1, hidden).to(DEV); self.l2 = torch.nn.Linear(hidden, 1).to(DEV); torch.nn.init.zeros_(self.l2.weight)
            self.drop = torch.nn.Dropout(0.1)

    def forward(self, s1, qp, X):
        X = X.float(); same = (X[..., SAME] > 0).float()
        if self.kind == 'diag': return self.a * s1 + qp @ self.w + X @ self.v + same * (X @ self.vs)
        return self.a * s1 + self.l2(torch.relu(self.l1(self.drop(torch.cat([qp, X, same[..., None]], -1))))).squeeze(-1)

def pad(recs, train):
    """Stack records; at training time gold outside the top rows is kept as extra positives."""
    L = max(len(r['rows']) for r in recs) if train else recs[0]['ntop']
    n = len(recs); d = recs[0]['p'].shape[1]; nf = recs[0]['X'].shape[1]
    qp = torch.zeros(n, L, d, device=DEV, dtype=torch.float16); X = torch.zeros(n, L, nf, device=DEV, dtype=torch.float16)
    s1 = torch.zeros(n, L, device=DEV); g = torch.zeros(n, L, dtype=torch.bool, device=DEV); mk = torch.zeros_like(g)
    for j, r in enumerate(recs):
        m = len(r['rows']) if train else r['ntop']
        qp[j, :m] = r['p'][:m] * r['qv'].half()[None]; X[j, :m] = r['X'][:m]; s1[j, :m] = r['s1'][:m]; g[j, :m] = r['gold'][:m]; mk[j, :m] = r['s1'][:m] > -1e29
    return qp, X, s1, g, mk

def train2(recs, kind, seed, steps=1500, lr=1e-3, wd=1e-4):
    recs = [r for r in recs if r['gold'].any()]
    qp, X, s1, g, mk = pad(recs, True)
    s1 = (s1 - s1[:, :1]).masked_fill(~mk, 0)
    m = Stage2(kind, qp.shape[2], X.shape[2], seed=seed); opt = torch.optim.Adam(m.parameters(), lr=lr, weight_decay=wd)
    gen = torch.Generator().manual_seed(seed)
    for step in range(steps):
        if step == int(steps * 0.7):
            for pg in opt.param_groups: pg['lr'] = lr * 0.2
        b = torch.randint(len(recs), (128,), generator=gen).to(DEV)
        s = m(s1[b], qp[b].float(), X[b]).masked_fill(~mk[b], -1e4); gb = g[b]
        neg = torch.logsumexp(s.masked_fill(gb, -1e4), 1, keepdim=True)
        loss = (((torch.logaddexp(s, neg) - s) * gb).sum(1) / gb.sum(1)).mean()
        opt.zero_grad(); loss.backward(); opt.step()
    m.eval(); return m

@torch.no_grad()
def score2(D, F, recs, m):
    """Per-query metric arrays after reranking the top rows of each record."""
    M = D.M; lib_cid, lib_mod, item_row, gptr, gold = M['lib_cid'], M['lib_mod'], M['item_row'], M['gold_ptr'], M['gold']
    out = {k: np.zeros(len(recs)) for k in ('h1', 'h5', 'h10', 'n', 'rr', 'own_h', 'own_n', 'seen_h', 'seen_n', 'new_h', 'new_n', 'rare_h', 'rare_n')}
    for s in range(0, len(recs), 256):
        rs = recs[s:s + 256]; qp, X, s1, g, mk = pad(rs, False)
        S = (s1 if m is None else m((s1 - s1[:, :1]).masked_fill(~mk, 0), qp.float(), X)).masked_fill(~mk, -1e30)
        order = S.argsort(1, descending=True).cpu().numpy(); Sg = S.masked_fill(~g, -1e30).max(1).values
        for k, r in enumerate(rs):
            j = s + k; i = F['items'][r['q']]; gs = gold[gptr[i]:gptr[i + 1]]; gset = set(int(c) for c in gs)
            topc = [int(lib_cid[r['rows'][x]]) for x in order[k][:10] if mk[k, x]]
            out['h1'][j] = len(gset & set(topc[:1])); out['h5'][j] = len(gset & set(topc[:5])); out['h10'][j] = len(gset & set(topc)); out['n'][j] = len(gs)
            for c in gs:
                gr = D.first[int(c)]; cl = 'own' if lib_mod[gr] == lib_mod[item_row[i]] else ('seen' if D.use[gr] > 0 else 'new')
                out[cl + '_n'][j] += 1; out[cl + '_h'][j] += int(c) in set(topc)
                if D.use[gr] <= RARE: out['rare_n'][j] += 1; out['rare_h'][j] += int(c) in set(topc)
            if g[k].any(): out['rr'][j] = 1.0 / (int((S[k][:r['ntop']] > Sg[k]).sum()) + 1)
            elif r['rank1']: out['rr'][j] = 1.0 / r['rank1']
    return out

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('feats'); ap.add_argument('run')
    ap.add_argument('--kind', default='diag'); ap.add_argument('--top', type=int, default=200); ap.add_argument('--seeds', type=int, default=1)
    ap.add_argument('--steps', type=int, default=1500); ap.add_argument('--wd', type=float, default=1e-4); ap.add_argument('--lr', type=float, default=1e-3)
    ap.add_argument('--test', action='store_true'); ap.add_argument('--out', default='')
    args = ap.parse_args()
    run = torch.load(args.run, weights_only=False); M = load_meta()
    Prow = run['P'].to(DEV)[torch.from_numpy(np.searchsorted(run['lib_u'], M['lib_cid'])).to(DEV)]
    D = Data(args.feats); pv = D.pool('val'); fv = D.full('val')
    vmod = M['lib_mod'][M['item_row'][fv['items']]]; fold_of = {m: k % 5 for k, m in enumerate(np.unique(vmod))}
    qfold = np.array([fold_of[m] for m in vmod]); pfold = np.array([fold_of[m] for m in pv['mod']])
    cols = FSETS['all']; kinds = args.kind.split(',')
    for seed in range(args.seeds):
        o1 = []; o2 = {k: [] for k in kinds}
        for f in range(5):
            st1 = fit([subset(pv, np.nonzero(pfold != f)[0])], cols, 'inter', seed=seed)
            recs = collect(D, fv, st1, run['Qval'], Prow, args.top)
            tr = [r for r in recs if qfold[r['q']] != f]; te = [r for r in recs if qfold[r['q']] == f]
            o1.append(score2(D, fv, te, None))
            for k in kinds: o2[k].append(score2(D, fv, te, train2(tr, k, seed, args.steps, args.lr, args.wd)))
            del recs
        cat = lambda os: {k: np.concatenate([o[k] for o in os]) for k in os[0]}
        log('seed %d  val  stage one        %s' % (seed, fmt(summary(cat(o1)))))
        for k in kinds: log('seed %d  val  stage two %-6s %s' % (seed, k, fmt(summary(cat(o2[k])))))
        if args.test:
            st1 = fit([pv], cols, 'inter', seed=seed)
            rv = collect(D, fv, st1, run['Qval'], Prow, args.top); ft = D.full('test'); rt = collect(D, ft, st1, run['Qtest'], Prow, args.top)
            to = score2(D, ft, rt, None); log('seed %d  test stage one        %s' % (seed, fmt(summary(to))))
            if args.out: np.savez('%s.stage1.s%d.npz' % (args.out, seed), **to)
            for k in kinds:
                m2 = train2(rv, k, seed, args.steps, args.lr, args.wd); to = score2(D, ft, rt, m2)
                log('seed %d  test stage two %-6s %s' % (seed, k, fmt(summary(to))))
                if args.out: np.savez('%s.%s.s%d.npz' % (args.out, k, seed), **to); torch.save(m2.state_dict(), '%s.%s.s%d.pt' % (args.out, k, seed))
            del rv, rt

if __name__ == '__main__':
    main()
