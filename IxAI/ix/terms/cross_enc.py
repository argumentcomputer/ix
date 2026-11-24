"""Held-out-library test of a trained encoder, on the queries, labels,
candidates and metric of `cross.py`, next to its training-free rankers.

    cross_enc.py MODEL.pt [--libs cslib-v4.34.0,flt-v4.34.0,physlean-v4.34.1]
                 [--ntest 2000] [--out DIR]

Each library is read from `pooled-LIB`, the Mathlib dump and the library's
dump merged into one id space by `merge_dump.py` (`graph_nary` exported in
it), so queries and candidates come from one graph. A constant's table row is
found through its address in the training dump; a constant without one is
unseen.

First, on Mathlib (the training dump), the script recomputes the encoder's
validation and test scores the way training reports them, once from the
training graph and once from the first pooled graph, and picks the weight of
the combination `z(encoder) + w * z(usage lookup)` (per-query z-scores over
the candidates) by validation R@10. The usage lookup there is the one of
`cross.py` with the training proofs as memory. Then every library is scored
with the four rankers of `cross.py`, the encoder, and the combinations with
the frozen lookup (chosen `w`, and `w = 1`) and with the online lookup
(chosen `w`), and the hybrid `EW * z(encoder) + w_idf * z(idf)` with weights
fixed in advance. Recall is reported at 10 and 50, overall and by where the
gold premise lives.
"""
import argparse, json, os, random, sys, time
import numpy as np, scipy.sparse as sp, torch
import torch.nn.functional as Fn
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import encoder_gpu as E
from encoder_gpu import load_model, Graph, load_meta, DEV, REF, REC

R = '/opt/dlami/nvme/ix-ai/terms/'
T0 = time.time()
def log(*a): print('[%7.1fs]' % (time.time() - T0), *a, flush=True)
# the lookup's votes are sparse, so its z-scores are large where it votes at
# all; the grid reaches far below 1
WGRID = [0.0, 0.001, 0.002, 0.005, 0.01, 0.02, 0.03, 0.05, 0.07, 0.1, 0.2, 0.5, 1.0, 2.0, 5.0]
NONE = (1 << 32) - 1
# `EW * z(encoder) + w_idf * z(idf)`, weights fitted on Mathlib validation
# modules; the first `w_idf` is the fitted one, the others a sensitivity check
EW = 1.9; IDFW = [0.18, 0.09, 0.36]

def read_consts(d):
    addr = []; kind = []
    for line in open(d + '/consts.tsv'):
        f = line.split('\t', 3); addr.append(f[1]); kind.append(f[2])
    return addr, kind

def idf_of(df, n):
    return np.array([max((n ** 4 // max(int(x), 1) ** 4).bit_length() - 1, 0) for x in df], dtype=np.float32)

def zscore(S, cand):
    """Per-row z-score of `S` over the entries where `cand` holds; 0 elsewhere."""
    c = cand.float(); n = c.sum(1, keepdim=True).clamp(min=1)
    mu = (S * c).sum(1, keepdim=True) / n
    var = (((S - mu) * c) ** 2).sum(1, keepdim=True) / n
    return torch.where(cand, (S - mu) / var.sqrt().clamp(min=1e-12), torch.zeros_like(S))

class Model:
    def __init__(self, path):
        self.enc, self.heads, self.ck = load_model(path)
        self.mf_slots = self.ck['slots']
        self.mf_addr, _ = read_consts(E.ROOT)
        self.mf_id = {a: i for i, a in enumerate(self.mf_addr)}
        self.sub = self.ck['args']['graph']
        self.prem_row = None             # set by `mathlib` when the model has a premise memory
        # addresses of the theorems that were candidates (and premises) in training
        self.train_lib = set(self.mf_addr[c] for c in np.unique(load_meta()['lib_cid']))

    def slots_for(self, addr):
        """Table row of every constant of a dump with addresses `addr` (0 = unseen)."""
        s = np.zeros(len(addr) + 1, dtype=np.int64); pr = np.zeros(len(addr) + 1, dtype=np.int64)
        for i, a in enumerate(addr):
            j = self.mf_id.get(a)
            if j is not None:
                s[i] = self.mf_slots[j]
                if self.prem_row is not None: pr[i] = self.prem_row[j]
        return s, pr

    @torch.no_grad()
    def embed(self, G, slots, prem_row, cids, head):
        """Normalized query (`Aq`) or premise (`Ap`) embeddings of the statements
        `cids`; a constant without a statement gets the zero vector."""
        enc = self.enc; enc.slot = torch.from_numpy(slots).to(DEV); enc.hidden = None; enc.mix = (0x9E3779B1, 0)
        cids = np.asarray(cids, dtype=np.int64)
        u, inv = np.unique(cids, return_inverse=True)
        ok = G.roots[u] != NONE; uo = u[ok]
        out = torch.zeros(len(u), self.heads['Aq'].shape[1], device=DEV)
        parts = []
        for s in range(0, len(uo), 4096):
            roots, _ = enc.encode(G, uo[s:s + 4096], keep=False)
            v = roots @ self.heads[head]
            if head == 'Ap' and 'Em' in self.heads:
                v = v + self.heads['Em'][torch.from_numpy(prem_row[uo[s:s + 4096]]).to(DEV)]
            parts.append(Fn.normalize(v, dim=1))
        if parts: out[torch.from_numpy(np.nonzero(ok)[0]).to(DEV)] = torch.cat(parts)
        return out[torch.from_numpy(inv).to(DEV)], int((~ok).sum())

def mentioned(G, cids):
    """Per statement, the distinct constants its graph nodes refer to."""
    out = []
    for c in cids:
        ns = G.nodes[G.ptr[c]:G.ptr[c + 1]]
        m = (G.tag_np[ns] == REF) | (G.tag_np[ns] == REC)
        out.append(np.unique(G.x_np[ns][m].astype(np.int64)))
    return out

def unseen_stats(G, slots, cids, nm=None):
    ms = mentioned(G, cids)
    occ = np.concatenate(ms) if ms else np.zeros(0, dtype=np.int64)
    dist = np.unique(occ)
    res = dict(distinct=len(dist), distinct_unseen=100 * float((slots[dist] == 0).mean()),
               mentions=len(occ), mentions_unseen=100 * float((slots[occ] == 0).mean()),
               stmts_with_unseen=100 * float(np.mean([(slots[m] == 0).any() for m in ms])))
    if nm is not None:
        res['distinct_unseen_lib'] = 100 * float(((slots[dist] == 0) & (dist >= nm)).mean())
        res['distinct_unseen_mathlib'] = 100 * float(((slots[dist] == 0) & (dist < nm)).mean())
        res['mentions_unseen_lib'] = 100 * float(((slots[occ] == 0) & (occ >= nm)).mean())
    return res

# ------------------------------------------------------------------ Mathlib
def mathlib(model, pooled_dir):
    """Training-style evaluation on Mathlib from two graphs, and the combination weight."""
    M = load_meta()
    lib_mod, lib_decl, lib_cid, reach = M['lib_mod'], M['lib_decl'], M['lib_cid'], M['reach']
    item_row, item_split, gptr, gold = M['item_row'], M['item_split'], M['gold_ptr'], M['gold']
    NL = len(lib_cid); item_mod = lib_mod[item_row]
    is_val = (item_split == 0) & (item_mod % 50 == 7)
    train = np.nonzero((item_split == 0) & ~is_val)[0]; val = np.nonzero(is_val)[0]; test = np.nonzero(item_split == 1)[0]
    rows_of = {}
    for r, c in enumerate(lib_cid): rows_of.setdefault(int(c), []).append(r)
    first = {c: rs[0] for c, rs in rows_of.items()}
    if 'Em' in model.heads:
        usedc = np.unique(np.concatenate([gold[gptr[i]:gptr[i + 1]] for i in train]))
        model.prem_row = np.zeros(len(model.mf_slots), dtype=np.int64); model.prem_row[usedc] = 1 + np.arange(len(usedc))
    lib_u = np.unique(lib_cid); col_of_row = np.searchsorted(lib_u, lib_cid)
    lm_t = torch.from_numpy(lib_mod).to(DEV); ld_t = torch.from_numpy(lib_decl).to(DEV); lc_t = torch.from_numpy(lib_cid).to(DEV)
    reach_t = torch.from_numpy(reach).to(DEV)
    use = np.zeros(NL, dtype=np.int64)
    for i in np.nonzero(item_split == 0)[0]:
        for c in gold[gptr[i]:gptr[i + 1]]: use[first[int(c)]] += 1

    def evaluate(items, scorer):
        """`evaluate` of encoder_gpu.py for every score matrix `scorer` yields."""
        ks = (1, 5, 10); acc = {}
        for s in range(0, len(items), 256):
            it = items[s:s + 256]; r = torch.from_numpy(item_row[it]).to(DEV)
            tm = lm_t[r]; td = ld_t[r]
            cand = reach_t[tm][:, lm_t] | ((lm_t[None, :] == tm[:, None]) & (ld_t[None, :] < td[:, None]))
            cand &= lc_t[None, :] != lc_t[r][:, None]
            for name, S in scorer(s, it, cand).items():
                a = acc.setdefault(name, dict(hits=np.zeros(3), sl=np.zeros(3), tot=np.zeros(3), gold_n=0, rr=0.0))
                S = S.masked_fill(~cand, -1e30)
                top = S.topk(10, dim=1).indices.cpu().numpy()
                for k, i in enumerate(it):
                    gs = gold[gptr[i]:gptr[i + 1]]; gset = set(int(c) for c in gs); a['gold_n'] += len(gs)
                    topc = [int(lib_cid[j]) for j in top[k]]
                    for b, kk in enumerate(ks): a['hits'][b] += len(gset & set(topc[:kk]))
                    t10 = set(topc)
                    for c in gs:
                        gr = first[int(c)]; cl = 0 if lib_mod[gr] == lib_mod[item_row[i]] else (1 if use[gr] > 0 else 2)
                        a['tot'][cl] += 1; a['sl'][cl] += int(c) in t10
                    grow = [x for c in gs for x in rows_of[int(c)]]
                    best = S[k, torch.tensor(grow, device=DEV)].max()
                    if best > -1e29: a['rr'] += 1.0 / (int((S[k] > best).sum()) + 1)
        out = {}
        for name, a in acc.items():
            out[name] = dict(r1=100 * a['hits'][0] / a['gold_n'], r5=100 * a['hits'][1] / a['gold_n'], r10=100 * a['hits'][2] / a['gold_n'],
                             mrr=a['rr'] / len(items), own=100 * a['sl'][0] / max(a['tot'][0], 1),
                             seen=100 * a['sl'][1] / max(a['tot'][1], 1), new=100 * a['sl'][2] / max(a['tot'][2], 1))
        return out

    def show(tag, res):
        log('%-28s R@1 %4.1f  R@5 %4.1f  R@10 %4.1f  MRR %.3f | own module %4.1f  imported, used %4.1f  imported, unused %4.1f' % (
            tag, res['r1'], res['r5'], res['r10'], res['mrr'], res['own'], res['seen'], res['new']))

    report = {}
    # training graph, training slots
    G = Graph(model.sub, E.ROOT); slots = model.mf_slots
    P, _ = model.embed(G, slots, model.prem_row, lib_u, 'Ap'); Prow = P[torch.from_numpy(col_of_row).to(DEV)]
    Qv, _ = model.embed(G, slots, model.prem_row, lib_cid[item_row[val]], 'Aq')
    Qt, _ = model.embed(G, slots, model.prem_row, lib_cid[item_row[test]], 'Aq')
    report['mathlib_unseen_test'] = unseen_stats(G, slots, lib_cid[item_row[test]])
    del G
    rv = evaluate(val, lambda s, it, cand: {'enc': Qv[s:s + 256] @ Prow.T})['enc']; show('validation (training graph)', rv)
    rt = evaluate(test, lambda s, it, cand: {'enc': Qt[s:s + 256] @ Prow.T})['enc']; show('test (training graph)', rt)
    report['mathlib_val'] = rv; report['mathlib_test'] = rt

    # the same statements through a pooled graph and address-mapped slots
    paddr, _ = read_consts(pooled_dir); pid = {a: i for i, a in enumerate(paddr)}
    G2 = Graph(model.sub, pooled_dir); s2, pr2 = model.slots_for(paddr)
    to_p = np.array([pid[model.mf_addr[c]] for c in lib_u], dtype=np.int64)
    P2, _ = model.embed(G2, s2, pr2, to_p, 'Ap')
    Qt2, _ = model.embed(G2, s2, pr2, to_p[np.searchsorted(lib_u, lib_cid[item_row[test]])], 'Aq')
    del G2
    dP = float((P2 - P).abs().max()); dQ = float((Qt2 - Qt).abs().max())
    log('pooled graph vs training graph: largest embedding difference, premises %.2e, test queries %.2e' % (dP, dQ))
    P2row = P2[torch.from_numpy(col_of_row).to(DEV)]
    rt2 = evaluate(test, lambda s, it, cand: {'enc': Qt2[s:s + 256] @ P2row.T})['enc']; show('test (pooled graph)', rt2)
    report['mathlib_test_pooled'] = rt2; report['pooled_max_diff'] = dict(P=dP, Q=dQ)
    del P2, P2row, Qt2

    # usage lookup with the training proofs as memory: the 64 accessible
    # training theorems whose statements share the most IDF-weighted constants
    maddr, mkind = read_consts(E.ROOT); NC = len(maddr)
    tref = {}
    for line in open(E.ROOT + '/trefs.tsv'):
        a, b = line.rstrip('\n').split('\t'); tref[int(a)] = [int(x) for x in b.split()] if b else []
    thm = np.array([k == 'thm' for k in mkind])
    ri = []; ci = []
    for c in np.nonzero(thm)[0]:
        for x in tref.get(int(c), []): ri.append(int(c)); ci.append(x)
    Mc = sp.coo_matrix((np.ones(len(ri), dtype=np.float32), (ri, ci)), shape=(NC, NC)).tocsr(); Mc.data[:] = 1
    df = np.asarray(Mc.sum(axis=0)).ravel().astype(np.int64); idf = idf_of(df, int(thm.sum()))
    Pm = Mc.multiply(idf[None, :]).tocsr(); mass = np.asarray(Pm.sum(axis=1)).ravel().astype(np.float64)
    tc = lib_cid[item_row[train]]; tm_ = lib_mod[item_row[train]]; td_ = lib_decl[item_row[train]]
    PT = Pm[tc].T.tocsr()
    tgold = [gold[gptr[j]:gptr[j + 1]] for j in train]
    def votes_for(items):
        qc = lib_cid[item_row[items]]; O = (Mc[qc] @ PT).toarray()
        V = np.zeros((len(items), NL), dtype=np.float32)
        for k, i in enumerate(items):
            qm = item_mod[i]; qd = lib_decl[item_row[i]]
            acc = reach[qm][tm_] | ((tm_ == qm) & (td_ < qd))
            sim = O[k] / np.sqrt((mass[tc] + 1.0) * (mass[qc[k]] + 1.0))
            sim = np.where(acc & (tc != qc[k]), sim, 0.0)
            order = np.argpartition(-sim, 64)[:64]; order = order[np.argsort(-sim[order])]
            v = {}
            for nb in order:
                if sim[nb] <= 0: break
                for g in tgold[nb]: v[int(g)] = v.get(int(g), 0.0) + sim[nb]
            for g, x in v.items(): V[k, rows_of[g]] = x
        return torch.from_numpy(V).to(DEV)
    def fused(Q):
        def f(s, it, cand):
            Se = Q[s:s + 256] @ Prow.T; Sv = votes_for(it)
            ze = zscore(Se, cand); zv = zscore(Sv, cand)
            out = {'w=%g' % w: ze + w * zv for w in WGRID}
            out['lookup'] = Sv + 1e-6 * Se
            return out
        return f
    fv = evaluate(val, fused(Qv))
    for k, v in fv.items(): show('validation ' + k, v)
    w = max(WGRID, key=lambda w: fv['w=%g' % w]['r10'])
    log('combination weight chosen on Mathlib validation: w = %g' % w)
    ft = evaluate(test, fused(Qt))
    for k in ('lookup', 'w=%g' % w, 'w=1'): show('test ' + k, ft[k])
    report['mathlib_val_fusion'] = fv; report['mathlib_test_fusion'] = {k: ft[k] for k in ('lookup', 'w=%g' % w, 'w=1')}
    report['w'] = w
    return report

# ------------------------------------------------------------------ libraries
def library(model, LIB, NTEST, w):
    """`cross.py` on LIB, with the encoder and its combinations added."""
    def load(s):
        addr, kind = read_consts(R + s)
        def refs(name):
            d = {}
            for line in open(R + s + '/' + name):
                a, b = line.rstrip('\n').split('\t'); d[int(a)] = [int(x) for x in b.split()] if b else []
            return d
        return addr, kind, refs('trefs.tsv'), refs('vrefs.tsv')
    maddr, mkind, mt, mv = load('mathlib-d13f23b'); NM = len(maddr)
    AM = {a: i for i, a in enumerate(maddr)}
    saddr, skind, st, sv = load(LIB)
    pid = []; newc = []
    for i, a in enumerate(saddr):
        j = AM.get(a)
        if j is None: j = NM + len(newc); newc.append(i)
        pid.append(j)
    NP = NM + len(newc)
    kind = mkind + [skind[i] for i in newc]
    tref = [mt.get(i, []) for i in range(NM)] + [[pid[r] for r in st.get(i, [])] for i in newc]
    vref = [mv.get(i, []) for i in range(NM)] + [[pid[r] for r in sv.get(i, [])] for i in newc]
    depth = np.zeros(NP, dtype=np.int64); state = np.zeros(NP, dtype=np.int8)
    for c0 in range(NM, NP):
        if state[c0]: continue
        stack = [(c0, 0)]; state[c0] = 1
        while stack:
            c, k = stack[-1]
            rs = [r for r in tref[c] + vref[c] if r >= NM]
            if k < len(rs):
                stack[-1] = (c, k + 1); r = rs[k]
                if state[r] == 0: state[r] = 1; stack.append((r, 0))
            else:
                depth[c] = 1 + max([depth[r] for r in rs if state[r] == 2], default=0); state[c] = 2; stack.pop()
    thm = np.array([k == 'thm' for k in kind])
    rows = np.nonzero(thm)[0]; NR = rows.size; row_of = np.full(NP, -1, dtype=np.int64); row_of[rows] = np.arange(NR)
    NMR = int(thm[:NM].sum())
    ri = []; ci = []
    for r, c in enumerate(rows):
        for x in tref[c]: ri.append(r); ci.append(x)
    M = sp.coo_matrix((np.ones(len(ri), dtype=np.float32), (ri, ci)), shape=(NR, NP)).tocsr(); M.data[:] = 1
    df = np.asarray(M.sum(axis=0)).ravel().astype(np.int64)
    idf = idf_of(df, NR)
    Pm = M.multiply(idf[None, :]).tocsr(); mass = np.asarray(Pm.sum(axis=1)).ravel().astype(np.int64); PT = Pm.T.tocsr()
    prem = [np.array(sorted(set(int(row_of[x]) for x in vref[c] if thm[x] and x != c)), dtype=np.int64) for c in rows]
    use = np.zeros(NR, dtype=np.int64)
    for r in range(NMR): use[prem[r]] += 1
    rdepth = depth[rows]; isnew = np.arange(NR) >= NMR
    tests = [r for r in range(NMR, NR) if prem[r].size]
    random.seed(7); random.shuffle(tests); tests = sorted(tests[:NTEST])
    log(LIB, 'pooled constants', NP, 'theorems', NR, 'of which new', NR - NMR, '| test theorems', len(tests))

    # encoder embeddings from the pooled graph
    pdir = R + 'pooled-' + LIB
    paddr, _ = read_consts(pdir)
    assert len(paddr) == NP and all(paddr[pid[i]] == saddr[i] for i in range(len(saddr))) and paddr[:NM] == maddr
    G = Graph(model.sub, pdir); slots, pr = model.slots_for(paddr)
    P, nostmt = model.embed(G, slots, pr, rows, 'Ap')
    Q, _ = model.embed(G, slots, pr, rows[tests], 'Aq')
    unseen = dict(new_theorems=unseen_stats(G, slots, rows[NMR:], NM), queries=unseen_stats(G, slots, rows[tests], NM))
    del G
    log('theorems without a statement node %d; unseen constants in the queries: %.1f%% of distinct, %.1f%% of mentions' % (
        nostmt, unseen['queries']['distinct_unseen'], unseen['queries']['mentions_unseen']))

    intrain = np.array([paddr[c] in model.train_lib for c in rows])
    names = ['idf', 'frequency', 'knn frozen', 'knn online', 'encoder', 'enc+frozen w=%g' % w, 'enc+frozen w=1', 'enc+online w=%g' % w,
             'encoder, training-library candidates'] + ['enc+idf %g/%g%s' % (EW, wi, '' if wi == IDFW[0] else ' (sensitivity)') for wi in IDFW]
    top_kind = np.zeros(3, dtype=np.int64); gold_kind = np.zeros(3, dtype=np.int64)   # training library, other Mathlib, own library
    kind_of = np.where(isnew, 2, np.where(intrain, 0, 1))
    hit = {n: np.zeros(3, dtype=np.int64) for n in names}; hitk = {n: np.zeros(3, dtype=np.int64) for n in names}; hit50 = {n: np.zeros(3, dtype=np.int64) for n in names}; rr = {n: 0 for n in names}; tot = np.zeros(3, dtype=np.int64); ncand = 0
    idx = np.arange(NR, dtype=np.int64)
    def votes(sim):
        order = np.argpartition(-sim, 64)[:64]; order = order[np.argsort(-sim[order])]
        v = np.zeros(NR)
        for nb in order:
            if sim[nb] <= 0: break
            if prem[nb].size: np.add.at(v, prem[nb], sim[nb])
        return v
    for s0 in range(0, len(tests), 64):
        chunk = tests[s0:s0 + 64]
        O = (M[chunk] @ PT).toarray().astype(np.int64)
        SE = (Q[s0:s0 + 64] @ P.T).cpu().numpy().astype(np.float64)
        for k, t in enumerate(chunk):
            ov = O[k]; score = (1024 * ov) // (mass + 1) + ov
            cand = (~isnew) | (rdepth < rdepth[t]); cand[t] = False
            ncand += int(cand.sum())
            g = prem[t]; gc = np.where(g >= NMR, 0, np.where(use[g] > 0, 1, 2))
            for c in gc: tot[c] += 1
            sim = ov / np.sqrt((mass + 1.0) * (mass[t] + 1.0))
            vf = votes(np.where(isnew, 0.0, sim)); vo = votes(np.where(cand, sim, 0.0))
            se = SE[k]
            def z(x):
                xc = x[cand]; sd = xc.std()
                return (x - xc.mean()) / sd if sd > 0 else np.zeros_like(x)
            ze = z(se); zf = z(vf); zo = z(vo); zi = z(score.astype(np.float64))
            keys = {'idf': score * NR + (NR - 1 - idx), 'frequency': use * NR + (NR - 1 - idx),
                    'knn frozen': (vf * 1e6).astype(np.int64) * 4096 + np.minimum(score, 4095),
                    'knn online': (vo * 1e6).astype(np.int64) * 4096 + np.minimum(score, 4095),
                    'encoder': se, names[5]: ze + w * zf, names[6]: ze + zf, names[7]: ze + w * zo,
                    names[8]: np.where(intrain | isnew, se, -np.inf)}
            for j, wi in enumerate(IDFW): keys[names[9 + j]] = EW * ze + wi * zi
            gold_kind += np.bincount(kind_of[g], minlength=3)
            ke = np.where(cand, se, -np.inf); top_kind += np.bincount(kind_of[np.argpartition(-ke, 10)[:10]], minlength=3)
            for n, key in keys.items():
                key = np.where(cand, key, -1) if key.dtype.kind == 'i' else np.where(cand, key, -np.inf)
                floor = -1 if key.dtype.kind == 'i' else -np.inf
                t50 = np.argpartition(-key, 50)[:50]; t50 = t50[np.argsort(-key[t50], kind='stable')]
                t50 = [int(j) for j in t50 if key[j] > floor]
                top = set(t50[:10]); top50 = set(t50)
                for x, c in zip(g, gc):
                    if int(x) in top: hit[n][c] += 1; hitk[n][kind_of[x]] += 1
                    if int(x) in top50: hit50[n][c] += 1
                gg = g[cand[g]]
                if gg.size: rr[n] += 1000000 // (int((key > key[gg].max()).sum()) + 1)
    Gn = int(tot.sum()); n = len(tests)
    cls = ['own library', 'Mathlib, used there', 'Mathlib, unused there']
    print('== %s: %d queries, %d candidates on average, gold: %s' % (LIB, n, ncand // n, ', '.join('%s %.1f%%' % (cls[c], 100 * tot[c] / Gn) for c in range(3))))
    print('%-38s %7s %9s %9s %12s %9s %7s %9s %9s' % ('R@10', 'all', 'own', 'Mathlib', 'Mathlib used', 'unused', 'MRR', 'R@50 all', 'R@50 own'))
    res = {}
    for nm in names:
        h = hit[nm]; mt_ = tot[1] + tot[2]
        res[nm] = dict(all=100 * h.sum() / Gn, own=100 * h[0] / max(tot[0], 1), mathlib=100 * (h[1] + h[2]) / max(mt_, 1),
                       used=100 * h[1] / max(tot[1], 1), unused=100 * h[2] / max(tot[2], 1), mrr=rr[nm] / n / 1e6,
                       all50=100 * hit50[nm].sum() / Gn, own50=100 * hit50[nm][0] / max(tot[0], 1))
        r_ = res[nm]
        print('%-38s %6.1f%% %8.1f%% %8.1f%% %11.1f%% %8.1f%% %7.3f %8.1f%% %8.1f%%' % (
            nm, r_['all'], r_['own'], r_['mathlib'], r_['used'], r_['unused'], r_['mrr'], r_['all50'], r_['own50']))
    u = unseen['new_theorems']; q = unseen['queries']
    print('unseen constants (no table row), statements of all %d new theorems: %.1f%% of %d distinct (library-defined %.1f%%, Mathlib %.1f%%), '
          '%.1f%% of mentions, %.1f%% of statements have one' % (NR - NMR, u['distinct_unseen'], u['distinct'], u['distinct_unseen_lib'],
          u['distinct_unseen_mathlib'], u['mentions_unseen'], u['stmts_with_unseen']))
    print('unseen constants, statements of the %d queries: %.1f%% of %d distinct (library-defined %.1f%%, Mathlib %.1f%%), %.1f%% of mentions, '
          '%.1f%% of statements have one' % (n, q['distinct_unseen'], q['distinct'], q['distinct_unseen_lib'], q['distinct_unseen_mathlib'],
          q['mentions_unseen'], q['stmts_with_unseen']), flush=True)
    tk = 100 * top_kind / top_kind.sum(); gk = 100 * gold_kind / gold_kind.sum()
    print('R@10 by where the gold premise is: %.1f%% training library (Mathlib theorems the encoder was trained on as premises), '
          '%.1f%% other Mathlib-environment theorems (core, dependencies, generated), %.1f%% own library' % tuple(gk))
    print('%-38s %9s %9s %9s' % ('R@10', 'training', 'other', 'own'))
    for nm in names:
        h = hitk[nm]; res[nm]['by_kind'] = [100 * h[j] / max(gold_kind[j], 1) for j in range(3)]
        print('%-38s %8.1f%% %8.1f%% %8.1f%%' % (nm, *res[nm]['by_kind']))
    print('encoder top 10: %.1f%% training-library theorems, %.1f%% other Mathlib theorems, %.1f%% own library; '
          'gold: %.1f%% / %.1f%% / %.1f%%; candidates on average: %d training-library theorems, %d other Mathlib' % (
          tk[0], tk[1], tk[2], gk[0], gk[1], gk[2], int(intrain.sum()), int((~intrain & ~isnew).sum())), flush=True)
    return dict(results=res, unseen=unseen, top10_kind=tk.tolist(), gold_kind=gk.tolist(), gold_share={cls[c]: 100 * tot[c] / Gn for c in range(3)}, queries=n,
                candidates=ncand // n, no_statement=nostmt)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('model'); ap.add_argument('--libs', default='cslib-v4.34.0,flt-v4.34.0,physlean-v4.34.1')
    ap.add_argument('--ntest', type=int, default=2000); ap.add_argument('--out', default=R + 'runs/cross')
    ap.add_argument('--w', type=float, default=None, help='skip the Mathlib part and use this combination weight')
    a = ap.parse_args()
    libs = a.libs.split(','); model = Model(a.model)
    log('model', a.model, {k: v for k, v in model.ck['args'].items() if k in ('d', 'pool', 'graph', 'anon', 'prem', 'seed')})
    report = {'model': a.model}
    if a.w is None:
        report.update(mathlib(model, R + 'pooled-' + libs[0])); w = report['w']
    else:
        w = a.w; report['w'] = w
    for L in libs: report[L] = library(model, L, a.ntest, w)
    os.makedirs(a.out, exist_ok=True)
    path = a.out + '/' + os.path.basename(a.model).replace('.model.pt', '') + '.json'
    json.dump(report, open(path, 'w'), indent=1, default=float); log('wrote', path)

if __name__ == '__main__':
    main()
