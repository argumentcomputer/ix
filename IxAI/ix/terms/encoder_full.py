"""The recursive encoder trained against every accessible premise at once.

    encoder_full.py [--usage usage.npz] [--epochs 30] [--refresh 100] ...

`encoder_gpu.py` scores a query against the batch's gold premises and a
sample of others; because most of that sample is other queries' gold, popular
premises are negatives far more often than rare ones. Here each query's
softmax runs over all library premises it can use. The premises a step
encodes afresh (its gold premises, same-module theorems and a random sample)
carry gradient; the rest come from a bank of embeddings recomputed every
`--refresh` steps.

With `--usage`, two terms are added to every logit and trained with the
encoder, so that it learns what usage lookup does not already give: the vote
of the query's nearest training theorems for the premise, and the number of
training proofs using it, both with the query's own module left out.
"""
import argparse, math, time
import numpy as np, torch
import torch.nn.functional as Fn
from encoder_gpu import load_meta, Graph, Encoder, REF, REC, DEV, log

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--d', type=int, default=128); ap.add_argument('--out', type=int, default=128)
    ap.add_argument('--epochs', type=int, default=30); ap.add_argument('--queries', type=int, default=512)
    ap.add_argument('--random', type=int, default=512); ap.add_argument('--lr', type=float, default=1e-3)
    ap.add_argument('--seed', type=int, default=1); ap.add_argument('--pool', default='meanmax')
    ap.add_argument('--refresh', type=int, default=100); ap.add_argument('--usage', default='')
    ap.add_argument('--save', default=''); ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--graph', default='graph', help='graph or graph_nary')
    args = ap.parse_args()
    torch.manual_seed(args.seed); rng = np.random.default_rng(args.seed)
    M = load_meta(); G = Graph(args.graph)
    lib_mod, lib_decl, lib_cid, reach = M['lib_mod'], M['lib_decl'], M['lib_cid'], M['reach']
    NL = len(lib_cid); item_row, item_split, gptr, gold = M['item_row'], M['item_split'], M['gold_ptr'], M['gold']
    rows_of = {}
    for r, c in enumerate(lib_cid): rows_of.setdefault(int(c), []).append(r)
    first = {c: rs[0] for c, rs in rows_of.items()}
    item_mod = lib_mod[item_row]
    is_val = (item_split == 0) & (item_mod % 50 == 7)
    train = np.nonzero((item_split == 0) & ~is_val)[0]; val = np.nonzero(is_val)[0]; test = np.nonzero(item_split == 1)[0]
    held = np.zeros(reach.shape[0], dtype=bool); held[np.unique(item_mod[np.concatenate([val, test])])] = True

    # premises as columns: one per distinct library constant, placed at its first declaration
    lib_u = np.unique(lib_cid); NU = len(lib_u)
    u_row = np.array([first[int(c)] for c in lib_u]); col_of = np.full(len(G.roots) + 1, -1, dtype=np.int64); col_of[lib_u] = np.arange(NU)
    um = torch.from_numpy(lib_mod[u_row]).to(DEV); ud = torch.from_numpy(lib_decl[u_row]).to(DEV)
    reach_t = torch.from_numpy(reach).to(DEV)
    log('premises %d  train %d  validation %d  test %d' % (NU, len(train), len(val), len(test)))

    seen_rows = np.nonzero(~held[lib_mod])[0]; cnt = np.zeros(len(G.roots), dtype=np.int64)
    for c in np.unique(lib_cid[seen_rows]):
        ns = G.nodes[G.ptr[c]:G.ptr[c + 1]]; m = (G.tag_np[ns] == REF) | (G.tag_np[ns] == REC)
        cs = G.x_np[ns][m]; cnt[cs[cs < len(cnt)]] += 1
    slots = np.zeros(len(G.roots) + 1, dtype=np.int64); keep = np.nonzero(cnt >= 3)[0]; slots[keep] = 1 + np.arange(len(keep))
    enc = Encoder(args.d, torch.from_numpy(slots).to(DEV), args.seed, torch.float32, args.pool, G.nary)
    g = torch.Generator().manual_seed(args.seed + 100)
    mk = lambda: torch.nn.Parameter((torch.randn(enc.width, args.out, generator=g, dtype=torch.float64) / math.sqrt(enc.width)).to(DEV, torch.float32))
    heads = {'Aq': mk(), 'Ap': mk(), 'ls': torch.nn.Parameter(torch.tensor(math.log(20.0), device=DEV))}
    groups = [{'params': list(enc.p.values()) + list(heads.values()), 'lr': args.lr}]

    use_u = torch.zeros(NU, device=DEV); U = None
    if args.usage:
        U = np.load(args.usage)
        use_u[torch.from_numpy(col_of[U['use_cid']]).to(DEV)] = torch.from_numpy(U['use_count']).float().to(DEV)
        heads['wv'] = torch.nn.Parameter(torch.tensor(2.0, device=DEV)); heads['wu'] = torch.nn.Parameter(torch.tensor(0.5, device=DEV))
        groups.append({'params': [heads['wv'], heads['wu']], 'lr': 10 * args.lr})
    opt = torch.optim.Adam(groups)
    log('parameters', sum(v.numel() for gq in groups for v in gq['params']))

    by_mod = {}
    for r in np.argsort(lib_mod * 100000 + lib_decl, kind='stable'): by_mod.setdefault(int(lib_mod[r]), []).append(int(r))
    pos_in_mod = np.zeros(NL, dtype=np.int64)
    for rs in by_mod.values():
        for k, r in enumerate(rs): pos_in_mod[r] = k
    t = lambda a: torch.from_numpy(np.asarray(a)).to(DEV)

    @torch.no_grad()
    def embed(cids, head):
        out = []
        for s in range(0, len(cids), 4096):
            roots, _ = enc.forward(G, G.batch(cids[s:s + 4096]), keep=False)
            out.append(Fn.normalize(roots @ heads[head], dim=1))
        return torch.cat(out)

    def usage_terms(items):
        """[queries, premises] logit terms from usage lookup, the query's own module left out."""
        if U is None: return 0.0
        n = len(items); vp = U['vote_ptr']
        lens = vp[items + 1] - vp[items]; idx = np.concatenate([np.arange(vp[i], vp[i + 1]) for i in items])
        q = np.repeat(np.arange(n), lens); col = col_of[U['vote_cid'][idx]]; ok = col >= 0
        V = torch.zeros(n, NU, device=DEV); V[t(q[ok]), t(col[ok])] = t(U['vote_val'][idx][ok])
        cntm = use_u[None, :].repeat(n, 1); mp = U['mod_ptr']; mods = item_mod[items]
        lens = mp[mods + 1] - mp[mods]
        if lens.sum():
            idx = np.concatenate([np.arange(mp[m], mp[m + 1]) for m in mods]); q = np.repeat(np.arange(n), lens)
            col = col_of[U['mod_cid'][idx]]; ok = col >= 0
            cntm[t(q[ok]), t(col[ok])] -= t(U['mod_count'][idx][ok]).float()
        return heads['wv'] * torch.log1p(V) + heads['wu'] * torch.log1p(cntm.clamp(min=0))

    def accessible(items):
        r = t(item_row[items]); tm = t(lib_mod[item_row[items]]); td = t(lib_decl[item_row[items]])
        acc = reach_t[tm][:, um] | ((um[None, :] == tm[:, None]) & (ud[None, :] < td[:, None]))
        self_col = t(col_of[lib_cid[item_row[items]]])
        acc[torch.arange(len(items), device=DEV), self_col] = False
        return acc

    def run_step(items, bank):
        qc = lib_cid[item_row[items]]; golds = [gold[gptr[i]:gptr[i + 1]] for i in items]; hard = []
        for i in items:
            r = item_row[i]; k = pos_in_mod[r]
            if k > 0:
                rs = by_mod[int(lib_mod[r])]; hard += [lib_cid[rs[j]] for j in rng.integers(0, k, size=min(2, k))]
        fresh = np.unique(np.concatenate(golds + [np.array(hard, dtype=np.int64), lib_u[rng.integers(0, NU, size=args.random)]]))
        allc = np.unique(np.concatenate([qc, fresh]))
        roots, state = enc.forward(G, G.batch(allc))
        R = roots.detach().requires_grad_(True)
        q = Fn.normalize(R[t(np.searchsorted(allc, qc))] @ heads['Aq'], dim=1)
        pf = Fn.normalize(R[t(np.searchsorted(allc, fresh))] @ heads['Ap'], dim=1)
        scale = heads['ls'].exp()
        S = (scale * (q @ bank.T)).index_copy(1, t(col_of[fresh]), scale * (q @ pf.T)) + usage_terms(items)
        pq = t(np.repeat(np.arange(len(items)), [len(x) for x in golds])); pc = t(col_of[np.concatenate(golds)])
        acc = accessible(items); acc[pq, pc] = True
        S = S.masked_fill(~acc, -1e30)
        neg = S.clone(); neg[pq, pc] = -1e30
        lse = torch.logsumexp(neg, 1)
        per = torch.logaddexp(S[pq, pc], lse[pq]) - S[pq, pc]
        w = 1.0 / torch.bincount(pq, minlength=len(items)).clamp(min=1).float()
        loss = (per * w[pq]).sum() / len(items)
        opt.zero_grad(set_to_none=True); loss.backward(); enc.backward(state, R.grad); opt.step()
        with torch.no_grad(): heads['ls'].clamp_(math.log(5.0), math.log(100.0))
        return float(loss.detach())

    use_first = np.zeros(NL, dtype=np.int64)
    for i in np.nonzero(item_split == 0)[0]:
        for c in gold[gptr[i]:gptr[i + 1]]: use_first[first[int(c)]] += 1

    @torch.no_grad()
    def evaluate(items, bank, name):
        Q = embed(lib_cid[item_row[items]], 'Aq'); scale = heads['ls'].exp()
        hits = np.zeros(3); sl = np.zeros(3); tot = np.zeros(3); gold_n = 0; rr = 0.0
        for s in range(0, len(items), 256):
            it = items[s:s + 256]
            S = scale * (Q[s:s + 256] @ bank.T) + usage_terms(it)
            S = S.masked_fill(~accessible(it), -1e30)
            top = S.topk(10, dim=1).indices.cpu().numpy()
            for k, i in enumerate(it):
                gs = gold[gptr[i]:gptr[i + 1]]; gset = set(int(c) for c in gs); gold_n += len(gs)
                topc = [int(lib_u[j]) for j in top[k]]
                for a, kk in enumerate((1, 5, 10)): hits[a] += len(gset & set(topc[:kk]))
                t10 = set(topc)
                for c in gs:
                    gr = first[int(c)]; cl = 0 if lib_mod[gr] == lib_mod[item_row[i]] else (1 if use_first[gr] > 0 else 2)
                    tot[cl] += 1; sl[cl] += int(c) in t10
                best = S[k, t(col_of[gs])].max()
                if best > -1e29: rr += 1.0 / (int((S[k] > best).sum()) + 1)
        res = dict(r1=100 * hits[0] / gold_n, r5=100 * hits[1] / gold_n, r10=100 * hits[2] / gold_n, mrr=rr / len(items),
                   own=100 * sl[0] / max(tot[0], 1), seen=100 * sl[1] / max(tot[1], 1), new=100 * sl[2] / max(tot[2], 1))
        log('%-10s R@1 %4.1f  R@5 %4.1f  R@10 %4.1f  MRR %.3f | own module %4.1f  imported, used %4.1f  imported, unused %4.1f' % (
            name, res['r1'], res['r5'], res['r10'], res['mrr'], res['own'], res['seen'], res['new']))
        return res

    best = (-1, None)
    for ep in range(args.epochs):
        order = rng.permutation(train)
        if args.limit: order = order[:args.limit]
        for k, gq in enumerate(opt.param_groups): gq['lr'] = args.lr * (10 if k else 1) * (1 - 0.9 * ep / args.epochs)
        tl = 0.0; nb = 0; t0 = time.time(); bank = None
        for s in range(0, len(order) - args.queries + 1, args.queries):
            if nb % args.refresh == 0: bank = embed(lib_u, 'Ap')
            tl += run_step(order[s:s + args.queries], bank); nb += 1
        extra = '  vote weight %.2f  use weight %.2f' % (float(heads['wv']), float(heads['wu'])) if U is not None else ''
        log('epoch %d  loss %.4f  %.2fs/step  scale %.1f%s' % (ep + 1, tl / nb, (time.time() - t0) / nb, float(heads['ls'].exp()), extra))
        bank = embed(lib_u, 'Ap')
        v = evaluate(val, bank, 'validation'); tres = evaluate(test, bank, 'test')
        if v['r10'] > best[0]:
            best = (v['r10'], (ep + 1, tres))
            if args.save:
                torch.save({'lib_u': lib_u, 'P': bank.cpu(), 'train': train, 'val': val, 'test': test,
                            'Qtrain': embed(lib_cid[item_row[train]], 'Aq').cpu(), 'Qval': embed(lib_cid[item_row[val]], 'Aq').cpu(),
                            'Qtest': embed(lib_cid[item_row[test]], 'Aq').cpu()}, args.save)
    ep, tres = best[1]
    log('selected epoch %d by validation R@10 %.1f: test R@1 %.1f R@5 %.1f R@10 %.1f MRR %.3f | own %.1f used %.1f unused %.1f' % (
        ep, best[0], tres['r1'], tres['r5'], tres['r10'], tres['mrr'], tres['own'], tres['seen'], tres['new']))

if __name__ == '__main__':
    main()
