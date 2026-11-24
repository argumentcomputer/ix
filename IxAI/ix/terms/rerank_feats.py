"""Per-candidate features for second-stage premise ranking, written once for reuse.

    rerank_feats.py RUN.pt OUT_DIR [--train N] [--seed S]

For validation, test and a random sample of N training theorems this computes
raw features of every accessible library theorem (same candidate set as
`fusion_gpu.py`):

  dense    encoder query-premise similarity
  v_idf    votes of the 64 training theorems nearest by IDF-weighted shared constants
  v_enc    the same vote with neighbours chosen by the encoder's query embeddings
  idf      IDF-weighted overlap score of the recorded baseline
  cos      IDF-weighted overlap divided by the geometric mean of both masses
  same     1 when the candidate is in the query's module
  used     log(1 + number of training proofs using the candidate)
  gap      log(1 + declarations between candidate and query) for same-module candidates, else 0
  mv_idf   total v_idf of the candidate's module
  mv_enc   total v_enc of the candidate's module
  v_idf16, v_enc16
           v_idf and v_enc with only the 16 nearest neighbours voting
  qx_idf, qx_enc
           similarity of the candidate's premise embedding to the
           similarity-weighted sum of the 64 neighbours' query embeddings

Neighbours and usage counts never come from the query's own module, so a
training theorem's features are distributed like those of a held-out theorem
(apart from `dense` and `v_enc`, whose encoder was fitted on training theorems).

`transform` turns raw features into the model inputs, standardised and ranked
per query over its candidates. Written per split:

  SPLIT_items.npy                  item indices
  SPLIT_pool_{ptr,row,gold,forced,X}.npy
                                   per query a candidate pool (top 300 of each
                                   ranking feature, the 300 latest same-module
                                   declarations, 200 random candidates, and the
                                   gold premises; `forced` marks gold that is
                                   in the pool only because it is gold), with
                                   the transformed features `X`
  SPLIT_full_{ptr,row,raw}.npy     (validation and test) every candidate with its raw features
"""
import argparse, os
import numpy as np, torch
from encoder_gpu import load_meta, Graph, REF, REC, DEV, log

RAW = ['dense', 'v_idf', 'v_enc', 'idf', 'cos', 'same', 'used', 'gap', 'mv_idf', 'mv_enc', 'v_idf16', 'v_enc16', 'qx_idf', 'qx_enc']
RANKED = ['dense', 'v_idf', 'v_enc', 'idf', 'cos', 'used', 'mv_idf', 'mv_enc', 'v_idf16', 'v_enc16', 'qx_idf', 'qx_enc']
LOGGED = ['v_idf', 'v_enc', 'idf', 'mv_idf', 'mv_enc', 'v_idf16', 'v_enc16']
NAMES = (['z_' + f for f in RAW] + ['r_' + f for f in RANKED] + ['zl_' + f for f in LOGGED])
POOL_TOP = ['dense', 'v_idf', 'v_enc', 'idf', 'cos', 'used', 'mv_idf', 'qx_enc']

def transform(F, cand):
    """F: [q, n, len(RAW)] raw features, cand: [q, n] bool. Returns [q, n, len(NAMES)].

    z_f is f standardised over the query's candidates; r_f is -log2(1 + number
    of candidates with a strictly larger f); zl_f standardises log(1 + max(f, 0))."""
    cf = cand[:, :, None].float(); n = cf.sum(1, keepdim=True).clamp(min=1)
    def z(X):
        mean = (X * cf).sum(1, keepdim=True) / n; var = (((X - mean) ** 2) * cf).sum(1, keepdim=True) / n
        return (X - mean) / var.sqrt().clamp(min=1e-6)
    out = [z(F)]
    ranked = []
    for f in RANKED:
        x = F[:, :, RAW.index(f)].masked_fill(~cand, -float('inf'))
        s = x.sort(1).values
        greater = x.shape[1] - torch.searchsorted(s, x.contiguous(), right=True)
        ranked.append(-torch.log2(1 + greater.float()))
    out.append(torch.stack(ranked, 2))
    out.append(z(torch.log1p(F[:, :, [RAW.index(f) for f in LOGGED]].clamp(min=0))))
    return torch.cat(out, 2)

class Features:
    def __init__(self, run):
        M = load_meta(); G = Graph(); self.M = M
        lib_mod, lib_decl, lib_cid = M['lib_mod'], M['lib_decl'], M['lib_cid']
        NL = len(lib_cid); self.NL = NL; item_row, gptr, gold = M['item_row'], M['gold_ptr'], M['gold']
        first = {}
        for r, c in enumerate(lib_cid): first.setdefault(int(c), r)
        self.first = first
        train = run['train']; self.train = train
        col_of_row = torch.from_numpy(np.searchsorted(run['lib_u'], lib_cid)).to(DEV)
        self.Prow = run['P'].to(DEV)[col_of_row]
        self.Qtrain = run['Qtrain'].to(DEV); self.train_rows = torch.from_numpy(item_row[train]).to(DEV)
        ri = []; ci = []
        for r, c in enumerate(lib_cid):
            ns = G.nodes[G.ptr[c]:G.ptr[c + 1]]; m = (G.tag_np[ns] == REF) | (G.tag_np[ns] == REC)
            cs = np.unique(G.x_np[ns][m]); ri.append(np.full(len(cs), r)); ci.append(cs)
        ri = np.concatenate(ri); ci = np.concatenate(ci).astype(np.int64)
        uc, ci = np.unique(ci, return_inverse=True); self.nconst = len(uc); self.ci = ci
        df = np.bincount(ci, minlength=len(uc))
        idf = np.array([max((NL ** 4 // max(int(x), 1) ** 4).bit_length() - 1, 0) for x in df], dtype=np.float32)
        self.wgt = torch.sparse_coo_tensor(np.stack([ri, ci]), idf[ci], (NL, len(uc))).coalesce().to(DEV).to_sparse_csr()
        self.mass = torch.zeros(NL, device=DEV).index_add_(0, torch.from_numpy(ri).to(DEV), torch.from_numpy(idf[ci]).to(DEV))
        self.row_ptr = np.searchsorted(ri, np.arange(NL + 1))
        ur = []; uc2 = []; use = np.zeros(NL, dtype=np.float32); mod_use = {}
        for i in train:
            ps = [first[int(c)] for c in gold[gptr[i]:gptr[i + 1]]]
            ur += [item_row[i]] * len(ps); uc2 += ps
            d = mod_use.setdefault(int(lib_mod[item_row[i]]), {})
            for p in ps: use[p] += 1; d[p] = d.get(p, 0) + 1
        self.mod_use = {m: (torch.tensor(list(d.keys()), device=DEV), torch.tensor(list(d.values()), dtype=torch.float32, device=DEV)) for m, d in mod_use.items()}
        self.use = use
        self.used_by = torch.sparse_coo_tensor(np.stack([np.array(uc2), np.array(ur)]), np.ones(len(ur), dtype=np.float32), (NL, NL)).coalesce().to(DEV).to_sparse_csr()
        self.is_train_row = torch.zeros(NL, dtype=torch.bool, device=DEV); self.is_train_row[self.train_rows] = True
        self.lm = torch.from_numpy(lib_mod).to(DEV); self.ld = torch.from_numpy(lib_decl).to(DEV); self.lc = torch.from_numpy(lib_cid).to(DEV)
        self.nmod = int(lib_mod.max()) + 1
        self.reach_t = torch.from_numpy(M['reach']).to(DEV); self.use_t = torch.from_numpy(use).to(DEV)

    def votes(self, sim, k=64):
        """Returns (votes [q, NL], neighbour weights [q, NL])."""
        top = sim.topk(k, dim=1); W = torch.zeros_like(sim).scatter_(1, top.indices, top.values.clamp(min=0))
        return torch.sparse.mm(self.used_by, W.T).T, W

    def expand(self, W):
        """Premise similarity to the neighbour-weighted sum of training query embeddings."""
        q = W[:, self.train_rows] @ self.Qtrain
        return (q / q.norm(dim=1, keepdim=True).clamp(min=1e-6)) @ self.Prow.T

    @torch.no_grad()
    def chunk(self, items, Q):
        """items: item indices, Q: their query embeddings. Returns (cand [q, NL], raw [q, NL, len(RAW)])."""
        M = self.M; item_row = M['item_row']; lm, ld, lc = self.lm, self.ld, self.lc
        r = torch.from_numpy(item_row[items]).to(DEV); tm = lm[r]; td = ld[r]
        samem = lm[None, :] == tm[:, None]
        cand = self.reach_t[tm][:, lm] | (samem & (ld[None, :] < td[:, None]))
        cand &= lc[None, :] != lc[r][:, None]
        qind = torch.zeros(len(items), self.nconst, device=DEV)
        for k, rr in enumerate(item_row[items]): qind[k, torch.from_numpy(self.ci[self.row_ptr[rr]:self.row_ptr[rr + 1]]).to(DEV)] = 1
        ov = torch.sparse.mm(self.wgt, qind.T).T
        idf_s = torch.floor(1024 * ov / (self.mass[None, :] + 1)) + ov
        cos = ov / torch.sqrt((self.mass[None, :] + 1) * (self.mass[r][:, None] + 1))
        voters = self.is_train_row[None, :] & ~samem
        v_idf, W_idf = self.votes(cos * voters); v_idf16, _ = self.votes(cos * voters, 16)
        Qd = Q.to(DEV)
        sim_e = torch.zeros(len(items), self.NL, device=DEV); sim_e[:, self.train_rows] = Qd @ self.Qtrain.T
        v_enc, W_enc = self.votes(sim_e * voters); v_enc16, _ = self.votes(sim_e * voters, 16)
        dense = Qd @ self.Prow.T
        use = self.use_t[None, :].repeat(len(items), 1)
        for k, m in enumerate(tm.tolist()):
            if m in self.mod_use:
                p, c = self.mod_use[m]; use[k, p] -= c
        used = torch.log1p(use)
        gap = torch.where(samem, torch.log1p((td[:, None] - ld[None, :]).clamp(min=0).float()), torch.zeros_like(dense))
        def modsum(V):
            S = torch.zeros(len(items), self.nmod, device=DEV).scatter_add_(1, lm[None, :].expand(len(items), -1), V)
            return S.gather(1, lm[None, :].expand(len(items), -1))
        F = torch.stack([dense, v_idf, v_enc, idf_s, cos, samem.float(), used, gap, modsum(v_idf), modsum(v_enc),
                         v_idf16, v_enc16, self.expand(W_idf), self.expand(W_enc)], 2)
        return cand, F

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('run'); ap.add_argument('out')
    ap.add_argument('--train', type=int, default=16000); ap.add_argument('--seed', type=int, default=0)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    run = torch.load(args.run, weights_only=False)
    FT = Features(run); M = FT.M; item_row, gptr, gold, lib_cid = M['item_row'], M['gold_ptr'], M['gold'], M['lib_cid']
    rows_of = {}
    for r, c in enumerate(lib_cid): rows_of.setdefault(int(c), []).append(r)
    rng = np.random.default_rng(args.seed)
    tsel = np.sort(rng.choice(len(run['train']), args.train, replace=False))
    splits = [('val', run['val'], run['Qval'], True), ('test', run['test'], run['Qtest'], True),
              ('train', run['train'][tsel], run['Qtrain'][tsel], False)]
    g = torch.Generator(device=DEV).manual_seed(args.seed)
    top_idx = [RAW.index(f) for f in POOL_TOP]; gi = RAW.index('gap'); si = RAW.index('same')
    for name, items, Q, full in splits:
        P = dict(ptr=[0], row=[], gold=[], forced=[], X=[]); Fu = dict(ptr=[0], row=[], raw=[])
        for s in range(0, len(items), 32):
            it = items[s:s + 32]
            cand, F = FT.chunk(it, Q[s:s + 32])
            T = transform(F, cand)
            for k, i in enumerate(it):
                ck = cand[k]
                picks = [F[k, :, j].masked_fill(~ck, -float('inf')).topk(300).indices for j in top_idx]
                samec = ck & (F[k, :, si] > 0)
                picks.append((-F[k, :, gi]).masked_fill(~samec, -float('inf')).topk(min(300, int(samec.sum()) or 1)).indices)
                cr = torch.nonzero(ck).flatten()
                picks.append(cr[torch.randint(len(cr), (200,), device=DEV, generator=g)])
                base = torch.unique(torch.cat(picks)); base = base[ck[base]]
                grow = torch.tensor([x for c in gold[gptr[i]:gptr[i + 1]] for x in rows_of[int(c)]], device=DEV, dtype=torch.long)
                grow = grow[ck[grow]] if len(grow) else grow
                sel = torch.unique(torch.cat([base, grow]))
                isg = torch.isin(sel, grow); forced = isg & ~torch.isin(sel, base)
                P['row'].append(sel.int().cpu().numpy()); P['gold'].append(isg.cpu().numpy()); P['forced'].append(forced.cpu().numpy())
                P['X'].append(T[k, sel].half().cpu().numpy()); P['ptr'].append(P['ptr'][-1] + len(sel))
                if full:
                    Fu['row'].append(cr.int().cpu().numpy()); Fu['raw'].append(F[k, cr].cpu().numpy()); Fu['ptr'].append(Fu['ptr'][-1] + len(cr))
            if s % (32 * 80) == 0: log(name, s, 'of', len(items))
        np.save('%s/%s_items.npy' % (args.out, name), items)
        for k, v in P.items():
            np.save('%s/%s_pool_%s.npy' % (args.out, name, k), np.array(v) if k == 'ptr' else np.concatenate(v))
        if full:
            for k, v in Fu.items():
                np.save('%s/%s_full_%s.npy' % (args.out, name, k), np.array(v) if k == 'ptr' else np.concatenate(v))
        log('wrote', name, 'pool per query %.0f' % (P['ptr'][-1] / len(items)))

if __name__ == '__main__':
    main()
