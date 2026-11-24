"""Combine a trained encoder with usage lookup for premise retrieval.

    fusion_gpu.py RUN.pt [TOP10.tsv] [--online] [--lists val|test:PATH:SAMPLE] [--solver USED.tsv]

`RUN.pt` holds the embeddings `encoder_gpu.py --save` wrote. For every
validation and test theorem this scores each accessible library theorem with

  dense     the encoder's query-premise similarity
  knn-idf   votes of the 64 training theorems nearest by IDF-weighted shared
            constants (the training-free rule), each voting for its premises
  knn-enc   the same vote with neighbours chosen by the encoder's embeddings;
            when the run has a trained lookup head, every training theorem
            votes with a softmax over that head's similarity as its weight
  idf       IDF-weighted overlap of shared constants, as the recorded baseline
  same      1 when the candidate is in the query's module
  used      log(1 + number of training proofs using the candidate)
  near      for a candidate in the query's module, 1 / sqrt(1 + number of
            library theorems declared between the two); 0 elsewhere
  nidf      like idf, over shared nodes of the statement graph: the sub-terms
            (under the same binder types) the two statements have in common

and reports each alone and a linear head over all of them. The head's weights
are fitted on the validation modules and applied unchanged to the test
modules. Scores are standardised per query over its candidates. With a second
argument, the gold premises and the top ten of usage lookup, the encoder, IDF
and the head are written by name for every test theorem.

`--online` changes the protocol: with a trained lookup head, the held-out
theorems accessible to a query (imported, or earlier in its module) vote with
their own proofs' premises alongside the training theorems, as they could when
a library is worked on in order. Only `knn-enc` and the heads change.

`--solver` names a file of lines `THEOREM<TAB>p1,p2,...`: for validation
theorems a solver closed, the listed premises its proofs used (`ix/closure`).
Two more heads are then fitted with those premises as the positives instead of
the gold premises (`hsolver`: encoder, IDF, module and popularity features;
`hsolver8`: all features), and their recall of solver-used premises is printed
for a fit on one half of the validation modules scored on the other.

`--lists` writes, for a fixed random sample of the split's theorems (0 = all),
the top premises of a family of rankers in the same format: the four above,
heads fitted on rarely used gold premises (`headrare`; `hrnear` with the
`near` feature; `hrplain` with neither usage feature; `hrstruct` adding shared
graph nodes; `noenc` the same without the encoder), the untrained `recent`
(same-module theorems by closeness, then IDF), and lists of 20 to 100 (a
name's trailing number is its list length).
"""
import math, sys, time
import numpy as np, torch
from encoder_gpu import load_meta, Graph, REF, REC, DEV, DATA, log

FEATS = ['dense', 'knn-idf', 'knn-enc', 'idf', 'same', 'used', 'near', 'nidf']

def main():
    online = '--online' in sys.argv; sys.argv = [a for a in sys.argv if a != '--online']
    lists = None; solver = None
    if '--solver' in sys.argv: i = sys.argv.index('--solver'); solver = sys.argv[i + 1]; del sys.argv[i:i + 2]
    if '--lists' in sys.argv: i = sys.argv.index('--lists'); lists = sys.argv[i + 1].split(':'); del sys.argv[i:i + 2]
    run = torch.load(sys.argv[1], weights_only=False)
    M = load_meta(); G = Graph()
    lib_mod, lib_decl, lib_cid, reach = M['lib_mod'], M['lib_decl'], M['lib_cid'], M['reach']
    NL = len(lib_cid); item_row, gptr, gold = M['item_row'], M['gold_ptr'], M['gold']
    rows_of = {}
    for r, c in enumerate(lib_cid): rows_of.setdefault(int(c), []).append(r)
    first = {c: rs[0] for c, rs in rows_of.items()}
    train, val, test = run['train'], run['val'], run['test']
    col_of_row = torch.from_numpy(np.searchsorted(run['lib_u'], lib_cid)).to(DEV)
    Prow = run['P'].to(DEV)[col_of_row]
    Qtrain = run['Qtrain'].to(DEV); train_rows = torch.from_numpy(item_row[train]).to(DEV)
    Ktrain = run['Ktrain'].to(DEV) if 'Ktrain' in run else None
    Kval, Ktest = run.get('Kval'), run.get('Ktest')

    # shared constants of every library statement, with the recorded baseline's IDF
    ri = []; ci = []
    for r, c in enumerate(lib_cid):
        ns = G.nodes[G.ptr[c]:G.ptr[c + 1]]; m = (G.tag_np[ns] == REF) | (G.tag_np[ns] == REC)
        cs = np.unique(G.x_np[ns][m]); ri.append(np.full(len(cs), r)); ci.append(cs)
    ri = np.concatenate(ri); ci = np.concatenate(ci).astype(np.int64)
    uc, ci = np.unique(ci, return_inverse=True)
    df = np.bincount(ci, minlength=len(uc))
    idf = np.array([max((NL ** 4 // max(int(x), 1) ** 4).bit_length() - 1, 0) for x in df], dtype=np.float32)
    wgt = torch.sparse_coo_tensor(np.stack([ri, ci]), idf[ci], (NL, len(uc))).coalesce().to(DEV)
    mass = torch.zeros(NL, device=DEV).index_add_(0, torch.from_numpy(ri).to(DEV), torch.from_numpy(idf[ci]).to(DEV))
    wgt_csr = wgt.to_sparse_csr(); row_ptr = np.searchsorted(ri, np.arange(NL + 1))

    # the same over graph nodes that at least two library statements share
    lens = (G.ptr[lib_cid + 1] - G.ptr[lib_cid]).astype(np.int64)
    nri = np.repeat(np.arange(NL), lens); nni = np.concatenate([G.nodes[G.ptr[c]:G.ptr[c + 1]] for c in lib_cid]).astype(np.int64)
    ndf = np.bincount(nni, minlength=G.n); keepn = np.nonzero(ndf >= 2)[0]; col = np.full(G.n, -1, dtype=np.int64); col[keepn] = np.arange(len(keepn))
    ok = col[nni] >= 0; nri = nri[ok]; nni = col[nni[ok]]
    nidf = np.array([max((NL ** 4 // int(x) ** 4).bit_length() - 1, 0) for x in ndf[keepn]], dtype=np.float32)
    nwgt = torch.sparse_coo_tensor(np.stack([nri, nni]), nidf[nni], (NL, len(keepn))).coalesce().to(DEV).to_sparse_csr()
    nmass = torch.zeros(NL, device=DEV).index_add_(0, torch.from_numpy(nri).to(DEV), torch.from_numpy(nidf[nni]).to(DEV))
    nrow_ptr = np.searchsorted(nri, np.arange(NL + 1)); nni_t = torch.from_numpy(nni).to(DEV)
    log('shared graph nodes %d, entries %d' % (len(keepn), len(nni)))

    # who uses what, among the training theorems
    ur = []; uc2 = []; use = np.zeros(NL, dtype=np.float32)
    for i in train:
        ps = [first[int(c)] for c in gold[gptr[i]:gptr[i + 1]]]
        ur += [item_row[i]] * len(ps); uc2 += ps
        for p in ps: use[p] += 1
    used_by = torch.sparse_coo_tensor(np.stack([np.array(uc2), np.array(ur)]), np.ones(len(ur), dtype=np.float32), (NL, NL)).coalesce().to(DEV).to_sparse_csr()
    if online:
        held = np.concatenate([val, test]); held_rows = torch.from_numpy(item_row[held]).to(DEV)
        Kheld = torch.cat([Kval, Ktest]).to(DEV)
        for i in held:
            ps = [first[int(c)] for c in gold[gptr[i]:gptr[i + 1]]]
            ur += [item_row[i]] * len(ps); uc2 += ps
        used_all = torch.sparse_coo_tensor(np.stack([np.array(uc2), np.array(ur)]), np.ones(len(ur), dtype=np.float32), (NL, NL)).coalesce().to(DEV).to_sparse_csr()
    is_train_row = torch.zeros(NL, dtype=torch.bool, device=DEV); is_train_row[train_rows] = True
    lm = torch.from_numpy(lib_mod).to(DEV); ld = torch.from_numpy(lib_decl).to(DEV); lc = torch.from_numpy(lib_cid).to(DEV)
    reach_t = torch.from_numpy(reach).to(DEV); used_t = torch.log1p(torch.from_numpy(use).to(DEV))
    log('library %d  train %d  validation %d  test %d' % (NL, len(train), len(val), len(test)))

    def votes(sim):
        """sim: queries x library rows, zero outside the allowed neighbours."""
        top = sim.topk(64, dim=1); W = torch.zeros_like(sim).scatter_(1, top.indices, top.values.clamp(min=0))
        return torch.sparse.mm(used_by, W.T).T

    @torch.no_grad()
    def features(items, Q, K=None):
        """Yield (items, candidate mask, standardised features [q, rows, len(FEATS)]) per chunk."""
        for s in range(0, len(items), 128):
            it = items[s:s + 128]; r = torch.from_numpy(item_row[it]).to(DEV); tm = lm[r]; td = ld[r]
            cand = reach_t[tm][:, lm] | ((lm[None, :] == tm[:, None]) & (ld[None, :] < td[:, None]))
            cand &= lc[None, :] != lc[r][:, None]
            qind = torch.zeros(len(it), len(uc), device=DEV)
            for k, rr in enumerate(item_row[it]): qind[k, torch.from_numpy(ci[row_ptr[rr]:row_ptr[rr + 1]]).to(DEV)] = 1
            ov = torch.sparse.mm(wgt_csr, qind.T).T                         # IDF mass shared with each row
            idf_s = torch.floor(1024 * ov / (mass[None, :] + 1)) + ov
            qn = torch.zeros(len(it), len(keepn), device=DEV)
            for k, rr in enumerate(item_row[it]): qn[k, nni_t[nrow_ptr[rr]:nrow_ptr[rr + 1]]] = 1
            ovn = torch.sparse.mm(nwgt, qn.T).T; del qn
            nidf_s = torch.floor(1024 * ovn / (nmass[None, :] + 1)) + ovn
            sim = ov / torch.sqrt((mass[None, :] + 1) * (mass[r][:, None] + 1))
            v_idf = votes(sim * is_train_row[None, :])
            sim_e = torch.zeros(len(it), NL, device=DEV)
            if K is None:
                sim_e[:, train_rows] = Q[s:s + 128].to(DEV) @ Qtrain.T; v_enc = votes(sim_e)
            elif not online:
                sim_e[:, train_rows] = torch.softmax(run['lk'] * (K[s:s + 128].to(DEV) @ Ktrain.T), 1)
                v_enc = torch.sparse.mm(used_by, sim_e.T).T
            else:
                Kq = K[s:s + 128].to(DEV); lh = (run['lk'] * (Kq @ Kheld.T)).masked_fill(~cand[:, held_rows], -1e30)
                A = torch.softmax(torch.cat([run['lk'] * (Kq @ Ktrain.T), lh], 1), 1)
                sim_e[:, train_rows] = A[:, :len(train)]; sim_e[:, held_rows] = A[:, len(train):]
                v_enc = torch.sparse.mm(used_all, sim_e.T).T
            dense = Q[s:s + 128].to(DEV) @ Prow.T
            same = (lm[None, :] == tm[:, None]).float()
            near = same / torch.sqrt(1 + (td[:, None] - ld[None, :] - 1).clamp(min=0).float())
            F = torch.stack([dense, v_idf, v_enc, idf_s, same, used_t[None, :].expand(len(it), -1), near, nidf_s], 2)
            cf = cand[:, :, None].float(); n = cf.sum(1, keepdim=True).clamp(min=1)
            mean = (F * cf).sum(1, keepdim=True) / n; var = (((F - mean) ** 2) * cf).sum(1, keepdim=True) / n
            yield it, cand, (F - mean) / var.sqrt().clamp(min=1e-6)

    def metrics(items, Q, K, weights):
        """weights: name -> one weight per feature. Returns name -> result dict."""
        acc = {k: dict(hits=np.zeros(3), sl=np.zeros(3), rr=0.0, rare=0) for k in weights}; tot = np.zeros(3); gold_n = 0; rare_n = 0
        for it, cand, F in features(items, Q, K):
            for name, w in weights.items():
                S = (F @ w).masked_fill(~cand, -1e30); top = S.topk(10, dim=1).indices.cpu().numpy(); a = acc[name]
                for k, i in enumerate(it):
                    gs = gold[gptr[i]:gptr[i + 1]]; gset = set(int(c) for c in gs); topc = [int(lib_cid[j]) for j in top[k]]
                    for x, kk in enumerate((1, 5, 10)): a['hits'][x] += len(gset & set(topc[:kk]))
                    t10 = set(topc)
                    for c in gs:
                        gr = first[int(c)]; cl = 0 if lib_mod[gr] == lib_mod[item_row[i]] else (1 if use[gr] > 0 else 2)
                        a['sl'][cl] += int(c) in t10; a['rare'] += use[gr] <= 20 and int(c) in t10
                    grow = torch.tensor([x for c in gs for x in rows_of[int(c)]], device=DEV); best = S[k, grow].max()
                    if best > -1e29: a['rr'] += 1.0 / (int((S[k] > best).sum()) + 1)
            for i in it:
                for c in gold[gptr[i]:gptr[i + 1]]:
                    gr = first[int(c)]; tot[0 if lib_mod[gr] == lib_mod[item_row[i]] else (1 if use[gr] > 0 else 2)] += 1; gold_n += 1
                    rare_n += use[gr] <= 20
        return {k: dict(r1=100 * a['hits'][0] / gold_n, r5=100 * a['hits'][1] / gold_n, r10=100 * a['hits'][2] / gold_n, mrr=a['rr'] / len(items),
                        own=100 * a['sl'][0] / max(tot[0], 1), seen=100 * a['sl'][1] / max(tot[1], 1), new=100 * a['sl'][2] / max(tot[2], 1),
                        rare=100 * a['rare'] / max(rare_n, 1)) for k, a in acc.items()}

    def show(title, res):
        print(title); print('  %-22s %5s %5s %5s %6s | %10s %14s %16s | %s' % ('ranker', 'R@1', 'R@5', 'R@10', 'MRR', 'own module', 'imported, used', 'imported, unused', 'used by <= 20 proofs'))
        for k, r in res.items():
            print('  %-22s %5.1f %5.1f %5.1f %6.3f | %10.1f %14.1f %16.1f | %5.1f' % (k, r['r1'], r['r5'], r['r10'], r['mrr'], r['own'], r['seen'], r['new'], r['rare']), flush=True)

    one = lambda j: torch.eye(len(FEATS), device=DEV)[j]
    singles = {FEATS[j]: one(j) for j in (0, 1, 2, 3, 7)}

    # fit the head on the validation modules: listwise softmax over gold, the top 100 of each score and 200 random candidates
    Xs = []; Ys = []; Yr = []; Ysol = []; Xmod = []; use_t = torch.from_numpy(use).to(DEV)
    used_rows = {}
    if solver:
        row_of_name = {}; nrow = 0
        for line in open(DATA + '/mathlib-full/decls.tsv'):
            if line.startswith('lib\t'): row_of_name.setdefault(line.split('\t', 2)[1], nrow); nrow += 1
        item_of_row = {int(item_row[i]): int(i) for i in val}
        for line in open(solver):
            f = line.rstrip('\n').split('\t')
            if f[0] in row_of_name and row_of_name[f[0]] in item_of_row and len(f) > 1 and f[1]:
                used_rows[item_of_row[row_of_name[f[0]]]] = [row_of_name[p] for p in f[1].split(',') if p in row_of_name]
        log('solver-used premises for %d validation theorems' % len(used_rows))
    with torch.no_grad():
        for it, cand, F in features(val, run['Qval'], Kval):
            for k, i in enumerate(it):
                pick = [F[k, :, j].masked_fill(~cand[k], -1e30).topk(100).indices for j in (0, 1, 2, 3, 7)]
                rnd = torch.nonzero(cand[k]).flatten(); rnd = rnd[torch.randint(len(rnd), (200,), device=DEV)]
                grow = torch.tensor([first[int(c)] for c in gold[gptr[i]:gptr[i + 1]]], device=DEV); grow = grow[cand[k][grow]]
                urow = torch.tensor(used_rows.get(int(i), []), device=DEV, dtype=torch.long); urow = urow[cand[k][urow]]
                sel = torch.unique(torch.cat(pick + [rnd, grow, urow]))
                if len(grow) == 0: continue
                y = torch.zeros(len(sel), device=DEV); y[torch.searchsorted(sel, grow)] = 1
                Xs.append(F[k, sel]); Ys.append(y)
                # 1 for gold that at most 20 training proofs use, -1 for other gold, which the rare fit leaves out
                Yr.append(torch.where(y == 0, y, torch.where(use_t[sel] <= 20, y, -y)))
                # 1 for a premise the solver used, -1 for gold it did not use, which the solver fit leaves out
                ys = None
                if len(urow):
                    ys = torch.zeros(len(sel), device=DEV); ys[torch.searchsorted(sel, urow)] = 1; ys = torch.where((ys == 0) & (y > 0), -y, ys)
                Ysol.append(ys); Xmod.append(int(lib_mod[item_row[i]]) // 50)
    def fit(mask, rare=False, sol=None):
        """`sol`: fit on solver-used premises, of all validation modules ('all') or of every other one ('even')."""
        torch.manual_seed(0); mask = torch.tensor(mask, device=DEV, dtype=torch.float32)
        w = torch.zeros(len(FEATS), device=DEV, requires_grad=True); opt = torch.optim.Adam([w], lr=0.05)
        pool = list(range(len(Xs)))
        if sol: pool = [j for j in pool if Ysol[j] is not None and (sol == 'all' or Xmod[j] % 2 == 0)]
        for step in range(300):
            opt.zero_grad(); loss = 0.0
            for j in [pool[x] for x in torch.randint(len(pool), (256,)).tolist()]:
                sc = Xs[j] @ (w * mask); y = Ys[j]
                if sol:
                    y = Ysol[j]; sc = sc.masked_fill(y < 0, -1e30)
                elif rare:
                    y = Yr[j]
                    if not bool((y > 0).any()): continue
                    sc = sc.masked_fill(y < 0, -1e30)
                loss = loss + (torch.logsumexp(sc, 0) - torch.logsumexp(sc.masked_fill(y <= 0, -1e30), 0))
            (loss / 256).backward(); opt.step()
        w = (w * mask).detach(); log('head weights: ' + '  '.join('%s %.2f' % (FEATS[j], float(w[j])) for j in range(len(FEATS))))
        return w
    heads = {'head, all six': fit([1, 1, 1, 1, 1, 1, 0, 0]), 'head, no encoder': fit([0, 1, 0, 1, 1, 1, 0, 0]),
             'head, encoder only': fit([1, 0, 1, 0, 1, 1, 0, 0]), 'head, rare gold': fit([1, 1, 1, 1, 1, 1, 0, 0], True),
             'head, rare gold, near': fit([1, 1, 1, 1, 1, 1, 1, 0], True), 'head, rare, no usage': fit([1, 0, 0, 1, 1, 0, 1, 0], True),
             'head, rare, structure': fit([1, 0, 0, 1, 1, 0, 1, 1], True), 'head, rare, no encoder': fit([0, 0, 0, 1, 1, 0, 1, 1], True)}
    if solver:
        m5 = [1, 0, 0, 1, 1, 1, 1, 0]; m8 = [1] * 8
        heads['head, solver'] = fit(m5, sol='all'); heads['head, solver, all features'] = fit(m8, sol='all')
        def used_recall(w):
            """Share of solver-used premises of the held-back validation modules in the top 10 of their candidate pool."""
            hit = tot = 0
            for j in range(len(Xs)):
                if Ysol[j] is None or Xmod[j] % 2 == 0: continue
                top = (Xs[j] @ w).topk(10).indices; hit += int((Ysol[j][top] > 0).sum()); tot += int((Ysol[j] > 0).sum())
            return 100 * hit / max(tot, 1)
        for name, w in (('rare gold, no usage', heads['head, rare, no usage']), ('solver, fitted on the other half', fit(m5, sol='even')),
                        ('solver, all features, other half', fit(m8, sol='even')), ('encoder alone', one(0))):
            log('solver-used premises of held-back validation modules in the top 10: %-36s %.1f%%' % (name, used_recall(w)))

    def dump(path, items, Q, K, weights, ks={}):
        """Write `THEOREM<TAB>MODULE<TAB>RANKER<TAB>names` for every item: its gold
        premises and each ranker's top ten (or `ks[name]`)."""
        mod_name = []; row_name = []
        for line in open(DATA + '/mathlib-full/decls.tsv'):
            f = line.rstrip('\n').split('\t')
            if f[0] == 'mod': mod_name.append(f[2])
            elif f[0] == 'lib': row_name.append(f[1])
        with open(path, 'w') as out:
            for it, cand, F in features(items, Q, K):
                tops = {name: (F @ w).masked_fill(~cand, -1e30).topk(ks.get(name, 10), dim=1).indices.cpu().numpy() for name, w in weights.items()}
                for k, i in enumerate(it):
                    thm = row_name[item_row[i]]; mod = mod_name[lib_mod[item_row[i]]]
                    out.write('%s\t%s\tgold\t%s\n' % (thm, mod, ','.join(row_name[first[int(c)]] for c in gold[gptr[i]:gptr[i + 1]])))
                    for name, top in tops.items():
                        out.write('%s\t%s\t%s\t%s\n' % (thm, mod, name, ','.join(row_name[j] for j in top[k])))
        log('wrote', path)

    show('validation', metrics(val, run['Qval'], Kval, {**singles, **heads}))
    show('test', metrics(test, run['Qtest'], Ktest, {**singles, **heads}))
    if len(sys.argv) > 2: dump(sys.argv[2], test, run['Qtest'], Ktest, {'knn': singles['knn-idf'], 'encoder': singles['dense'],
                                                                   'idf': singles['idf'], 'head': heads['head, all six']})
    if lists:
        split, path, sample = lists; its = val if split == 'val' else test
        if int(sample): its = its[np.sort(np.random.default_rng(0).permutation(len(its))[:int(sample)])]
        fam = {'knn': singles['knn-idf'], 'encoder': singles['dense'], 'idf': singles['idf'], 'head': heads['head, all six'],
               'headrare': heads['head, rare gold'], 'hrnear': heads['head, rare gold, near'], 'hrplain': heads['head, rare, no usage'],
               'hrstruct': heads['head, rare, structure'], 'noenc': heads['head, rare, no encoder'], 'nidf': singles['nidf']}
        if solver: fam['hsolver'] = heads['head, solver']; fam['hsolver8'] = heads['head, solver, all features']
        # no trained model: the theorems declared most recently before the query in its module, then IDF overlap
        recent = torch.zeros(len(FEATS), device=DEV); recent[FEATS.index('near')] = 1.0; recent[FEATS.index('idf')] = 1e-3
        fam['recent'] = recent; fam['recent50'] = recent; fam['idf50'] = singles['idf']
        ks = {'recent50': 50, 'idf50': 50}
        for n in (20, 30, 50, 100):
            for nm in ('encoder', 'headrare', 'hrnear', 'hrplain', 'hrstruct', 'noenc') + (('hsolver', 'hsolver8') if solver else ()):
                short = 'enc' if nm == 'encoder' else nm
                fam['%s%d' % (short, n)] = fam[nm]; ks['%s%d' % (short, n)] = n
        Qs = (run['Qval'], Kval) if split == 'val' else (run['Qtest'], Ktest)
        pos = {int(i): j for j, i in enumerate(val if split == 'val' else test)}
        sel = torch.tensor([pos[int(i)] for i in its])
        dump(path, its, Qs[0][sel], None if Qs[1] is None else Qs[1][sel], fam, ks)

if __name__ == '__main__':
    main()
