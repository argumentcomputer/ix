"""Usage lookup for every item of the premise dataset, written once for reuse.

    usage_gpu.py OUT.npz

For each item (training, validation and test theorems alike) this stores the
votes of its 64 nearest training theorems, nearest by IDF-weighted shared
constants, each voting for the premises its proof uses. A training theorem's
neighbours exclude its own module, because at test time a whole module is
unseen and its theorems cannot vote for one another.

The file holds, per item, the voted premises as constant ids with their vote
(`vote_ptr`, `vote_cid`, `vote_val`); the number of training proofs using each
library constant (`use_cid`, `use_count`); and for each training module the
premises its own theorems use (`mod_ptr`, `mod_cid`, `mod_count`, indexed by
module), so a count can be taken with the query's module left out.
"""
import sys
import numpy as np, torch
from encoder_gpu import load_meta, Graph, REF, REC, DEV, log

def main():
    M = load_meta(); G = Graph()
    lib_mod, lib_cid = M['lib_mod'], M['lib_cid']; NL = len(lib_cid)
    item_row, item_split, gptr, gold = M['item_row'], M['item_split'], M['gold_ptr'], M['gold']
    first = {}
    for r, c in enumerate(lib_cid): first.setdefault(int(c), r)
    item_mod = lib_mod[item_row]
    is_val = (item_split == 0) & (item_mod % 50 == 7)
    train = np.nonzero((item_split == 0) & ~is_val)[0]

    ri = []; ci = []
    for r, c in enumerate(lib_cid):
        ns = G.nodes[G.ptr[c]:G.ptr[c + 1]]; m = (G.tag_np[ns] == REF) | (G.tag_np[ns] == REC)
        cs = np.unique(G.x_np[ns][m]); ri.append(np.full(len(cs), r)); ci.append(cs)
    ri = np.concatenate(ri); ci = np.concatenate(ci).astype(np.int64)
    uc, ci = np.unique(ci, return_inverse=True)
    df = np.bincount(ci, minlength=len(uc))
    idf = np.array([max((NL ** 4 // max(int(x), 1) ** 4).bit_length() - 1, 0) for x in df], dtype=np.float32)
    wgt = torch.sparse_coo_tensor(np.stack([ri, ci]), idf[ci], (NL, len(uc))).coalesce().to(DEV).to_sparse_csr()
    mass = torch.zeros(NL, device=DEV).index_add_(0, torch.from_numpy(ri).to(DEV), torch.from_numpy(idf[ci]).to(DEV))
    row_ptr = np.searchsorted(ri, np.arange(NL + 1))

    ur = []; up = []; use = np.zeros(NL, dtype=np.int64); per_mod = {}
    for i in train:
        ps = [first[int(c)] for c in gold[gptr[i]:gptr[i + 1]]]
        ur += [item_row[i]] * len(ps); up += ps
        d = per_mod.setdefault(int(item_mod[i]), {})
        for p in ps: use[p] += 1; d[int(lib_cid[p])] = d.get(int(lib_cid[p]), 0) + 1
    used_by = torch.sparse_coo_tensor(np.stack([np.array(up), np.array(ur)]), np.ones(len(ur), dtype=np.float32), (NL, NL)).coalesce().to(DEV).to_sparse_csr()
    is_train_row = torch.zeros(NL, dtype=torch.bool, device=DEV); is_train_row[torch.from_numpy(item_row[train]).to(DEV)] = True
    lm = torch.from_numpy(lib_mod).to(DEV); lc = torch.from_numpy(lib_cid)

    ptr = [0]; cids = []; vals = []
    n = len(item_row)
    with torch.no_grad():
        for s in range(0, n, 128):
            rows = item_row[s:s + 128]; r = torch.from_numpy(rows).to(DEV)
            qind = torch.zeros(len(rows), len(uc), device=DEV)
            for k, rr in enumerate(rows): qind[k, torch.from_numpy(ci[row_ptr[rr]:row_ptr[rr + 1]]).to(DEV)] = 1
            ov = torch.sparse.mm(wgt, qind.T).T
            sim = ov / torch.sqrt((mass[None, :] + 1) * (mass[r][:, None] + 1))
            sim = sim * (is_train_row[None, :] & (lm[None, :] != lm[r][:, None]))
            top = sim.topk(64, dim=1); W = torch.zeros_like(sim).scatter_(1, top.indices, top.values.clamp(min=0))
            V = torch.sparse.mm(used_by, W.T).T
            nz = torch.nonzero(V > 0)
            v = V[nz[:, 0], nz[:, 1]].cpu().numpy(); q = nz[:, 0].cpu().numpy(); c = lc[nz[:, 1].cpu()].numpy()
            cnt = np.bincount(q, minlength=len(rows))
            for k in range(len(rows)): ptr.append(ptr[-1] + int(cnt[k]))
            cids.append(c); vals.append(v)
            if s % (128 * 200) == 0: log('items', s, 'of', n)
    nm = int(lib_mod.max()) + 1; mp = [0]; mc = []; mv = []
    for m in range(nm):
        d = per_mod.get(m, {}); ks = sorted(d); mc += ks; mv += [d[k] for k in ks]; mp.append(len(mc))
    urow = np.nonzero(use)[0]
    np.savez(sys.argv[1], vote_ptr=np.array(ptr), vote_cid=np.concatenate(cids), vote_val=np.concatenate(vals).astype(np.float32),
             use_cid=lib_cid[urow], use_count=use[urow], mod_ptr=np.array(mp), mod_cid=np.array(mc, dtype=np.int64), mod_count=np.array(mv, dtype=np.int64))
    log('wrote', sys.argv[1], 'votes per item %.0f' % (ptr[-1] / n))

if __name__ == '__main__':
    main()
