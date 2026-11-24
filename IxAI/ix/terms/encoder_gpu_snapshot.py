"""The form of `encoder_gpu.py` that `encoder_cert.py` reproduces in exact
integer arithmetic, and the module it takes its data loading and loss from:
a recursive encoder over the shared statement graph of a library, trained for
premise retrieval, in floating point on the GPU. It has none of the options
`encoder_gpu.py` has beyond these.

    encoder_gpu_snapshot.py [--d 128] [--epochs 8] [--queries 512] [--random 1024]
                            [--lr 1e-3] [--seed 1] [--check]

The graph comes from `graph_export` (one node per distinct sub-term under the
types of its free variables' binders). A node's vector is computed bottom-up,
once per batch: a constant is a table row, a bound variable its index
embedding plus a linear map of its binder type's vector, and every other node
`relu([children] W_kind + b_kind)` plus the mean of two children, clamped.
A statement is its root's vector; two linear heads give the query and premise
embeddings, trained with a multi-positive softmax loss over the batch's gold
premises, same-module negatives and random library theorems.

Evaluation follows the recorded baselines: every accessible library theorem
(imported, or earlier in the same module) is a candidate; recall@k is the
share of gold premises in the top k and MRR the reciprocal rank of the first.
"""
import argparse, math, os, random, sys, time
import numpy as np, torch
import torch.nn.functional as Fn

ROOT = '/opt/dlami/nvme/ix-ai/terms/mathlib-full'
DATA = '/home/sam/repos/ix-ai-pipeline/.truthmines/datasets'
DEV = 'cuda'
T0 = time.time()
def log(*a): print('[%7.1fs]' % (time.time() - T0), *a, flush=True)

SORT, VAR, REF, REC, PRJ, STR, NAT, APP, LAM, ALL, LET = range(11)
CLAMP = 8.0

# ------------------------------------------------------------------ data
def load_meta():
    cache = ROOT + '/graph/meta.npz'
    if os.path.exists(cache):
        z = np.load(cache)
        return {k: z[k] for k in z.files}
    addr2id = {}
    for line in open(ROOT + '/consts.tsv'):
        f = line.split('\t', 2); addr2id[f[1]] = int(f[0])
    name2addr = {}
    for line in open(DATA + '/mathlib-full/names.tsv'):
        n, a = line.rstrip('\n').split('\t'); name2addr[n] = a
    mods = []; lib_mod = []; lib_decl = []; lib_cid = []
    for line in open(DATA + '/mathlib-full/decls.tsv'):
        if line.startswith('mod\t'):
            f = line.rstrip('\n').split('\t')
            mods.append([int(x) for x in f[3].split(',') if x] if len(f) > 3 else [])
        elif line.startswith('lib\t'):
            f = line.split('\t', 4)
            lib_mod.append(int(f[2])); lib_decl.append(int(f[3])); lib_cid.append(addr2id[name2addr[f[1]]])
    nm = len(mods); reach = np.zeros((nm, nm), dtype=bool)
    for i, imps in enumerate(mods):
        for j in imps:
            reach[i] |= reach[j]; reach[i, j] = True
    lib_cid = np.array(lib_cid, dtype=np.int64)
    first = {}
    for r, c in enumerate(lib_cid): first.setdefault(int(c), r)
    split = []; row = []; gptr = [0]; gflat = []
    for line in open(DATA + '/mathlib-full.items.tsv'):
        f = line.rstrip('\n').split('\t')
        c = addr2id[f[1]]
        gold = [addr2id[p] for p in f[3].split(',') if p]
        gold = [g for g in gold if g in first]
        split.append(0 if f[0] == 'train' else 1); row.append(first[c]); gflat += gold; gptr.append(len(gflat))
    meta = dict(lib_mod=np.array(lib_mod), lib_decl=np.array(lib_decl), lib_cid=lib_cid, reach=reach,
                item_split=np.array(split), item_row=np.array(row), gold_ptr=np.array(gptr), gold=np.array(gflat, dtype=np.int64))
    np.savez(cache, **meta)
    return meta

class Graph:
    """`sub` is `graph` (binary applications) or `graph_nary` (an application
    with all its arguments is one node; `x` is its head, `y` the offset of its
    arguments in `args`, `z` their number)."""
    def __init__(self, sub='graph'):
        base = ROOT + '/' + sub
        self.nary = os.path.exists(base + '/args.bin')
        if self.nary: self.args = torch.from_numpy(np.fromfile(base + '/args.bin', dtype='<u4').astype(np.int64)).to(DEV)
        g = np.fromfile(base + '/gnodes.bin', dtype='<u4').reshape(-1, 5)
        self.tag = torch.from_numpy(g[:, 0].astype(np.uint8)).to(DEV)
        self.x = torch.from_numpy(g[:, 1].astype(np.int64)).to(DEV)
        self.y = torch.from_numpy(g[:, 2].astype(np.int64)).to(DEV)
        self.z = torch.from_numpy(g[:, 3].astype(np.int64)).to(DEV)
        self.level = torch.from_numpy(g[:, 4].astype(np.int16)).to(DEV)
        self.n = g.shape[0]
        self.roots = np.fromfile(base + '/roots.bin', dtype='<u4').astype(np.int64)
        self.ptr = np.fromfile(base + '/stmt_ptr.bin', dtype='<u8').astype(np.int64)
        self.nodes = np.fromfile(base + '/stmt_nodes.bin', dtype='<u4')
        self.tag_np = g[:, 0].astype(np.uint8); self.x_np = g[:, 1]

    def batch(self, cids):
        """The nodes of the statements `cids`, grouped by level and kind, and
        for pooling the position of every node of every statement."""
        parts = [self.nodes[self.ptr[c]:self.ptr[c + 1]] for c in cids]
        allnodes = torch.from_numpy(np.concatenate(parts).astype(np.int64)).to(DEV)
        ids = torch.unique(allnodes)
        key = self.level[ids].long() * 16 + self.tag[ids].long()
        order = torch.argsort(key, stable=True)
        keys, counts = torch.unique_consecutive(key[order], return_counts=True)
        rootpos = torch.searchsorted(ids, torch.from_numpy(self.roots[cids]).to(DEV))
        lens = torch.tensor([len(x) for x in parts], device=DEV)
        seg = torch.repeat_interleave(torch.arange(len(parts), device=DEV), lens)
        return ids, order, (keys % 16).tolist(), counts.tolist(), rootpos, seg, torch.searchsorted(ids, allnodes), lens

# ------------------------------------------------------------------ model
class Encoder:
    def __init__(self, d, slots, seed, dtype=torch.float32, pool='none', nary=False):
        g = torch.Generator().manual_seed(seed); s = 1.0 / math.sqrt(d)
        def rn(*shape): return torch.nn.Parameter((torch.randn(*shape, generator=g, dtype=torch.float64) * s).to(DEV, dtype))
        def zs(*shape): return torch.nn.Parameter(torch.zeros(*shape, device=DEV, dtype=dtype))
        self.d = d; self.dtype = dtype; self.pool = pool
        self.width = d * {'none': 1, 'mean': 2, 'meanmax': 3}[pool]
        self.slot = slots                       # constant id -> table row (0 = unseen)
        self.p = {'Esort': rn(20, d), 'Econst': rn(int(slots.max()) + 1, d), 'Evar': rn(64, d), 'Elit': rn(40, d),
                  'P': rn(d, d), 'Wp': rn(d, d), 'bp': zs(d), 'W10': rn(3 * d, d), 'b10': zs(d)}
        self.nary = nary
        for k in ((LAM, ALL) if nary else (APP, LAM, ALL)):
            self.p['W%d' % k] = rn(2 * d, d); self.p['b%d' % k] = zs(d)
        if nary:
            # one matrix for the head and one per argument slot: the last three
            # arguments, then the first three of the rest, then all others
            self.p['Wh'] = rn(d, d); self.p['Wa'] = rn(7, d, d); self.p['ba'] = zs(d)

    def leaf(self, tag, x):
        """(table name, row) of a leaf node."""
        if tag == SORT: return 'Esort', x.clamp(max=19)
        if tag in (REF, REC): return 'Econst', self.slot[x.clamp(max=self.slot.numel() - 1)]
        if tag == NAT: return 'Elit', 1 + x.clamp(max=37)
        return 'Elit', torch.zeros_like(x)

    @torch.no_grad()
    def forward(self, G, batch, keep=True):
        ids, order, tags, counts, rootpos, seg, npos, lens = batch; p = self.p
        H = torch.zeros(ids.numel(), self.d, device=DEV, dtype=self.dtype); cache = []; s = 0
        pos = lambda gid: torch.searchsorted(ids, gid)
        for tag, n in zip(tags, counts):
            idx = order[s:s + n]; s += n; gid = ids[idx]
            if tag in (SORT, REF, REC, STR, NAT):
                name, row = self.leaf(tag, G.x[gid]); H[idx] = p[name][row]; rec = (tag, idx, name, row)
            elif tag == VAR:
                vi = G.x[gid].clamp(max=63); ty = G.y[gid]; has = ty < G.n
                raw = p['Evar'][vi]
                tp = pos(ty[has]); raw[has] += H[tp] @ p['P']
                H[idx] = raw.clamp(-CLAMP, CLAMP); rec = (tag, idx, vi, has, tp, raw.abs() < CLAMP)
            elif tag == APP and self.nary:
                head = pos(G.x[gid]); na = G.z[gid]; hh = H[head]
                node = torch.repeat_interleave(torch.arange(n, device=DEV), na)
                off = torch.arange(node.numel(), device=DEV) - (torch.cumsum(na, 0) - na)[node]
                apos = pos(G.args[G.y[gid][node] + off]); back = na[node] - 1 - off
                slot = torch.where(back < 3, back, torch.where(off < 3, 3 + off, torch.full_like(off, 6)))
                Ha = H[apos]; lin = hh @ p['Wh']
                for sl in range(7):
                    sel = torch.nonzero(slot == sl).flatten()
                    if sel.numel(): lin.index_add_(0, node[sel], Ha[sel] @ p['Wa'][sl])
                # scale the sum by a power of two that grows with the argument count
                naf = na.to(self.dtype); f = torch.pow(2.0, -torch.floor(torch.log2(naf + 1) / 2))[:, None]
                c = torch.pow(2.0, -(1 + torch.ceil(torch.log2(naf))))[:, None]
                pre = lin * f + p['ba']
                raw = pre.clamp(min=0) + 0.5 * hh + torch.zeros_like(hh).index_add_(0, node, Ha) * c
                H[idx] = raw.clamp(-CLAMP, CLAMP); rec = (tag, idx, head, hh, node, apos, slot, Ha, f, c, pre > 0, raw.abs() < CLAMP)
            elif tag in (APP, LAM, ALL):
                a = pos(G.x[gid]); b = pos(G.y[gid]); ha = H[a]; hb = H[b]
                X = torch.cat([ha, hb], 1); pre = X @ p['W%d' % tag] + p['b%d' % tag]
                raw = pre.clamp(min=0) + 0.5 * (ha + hb)
                H[idx] = raw.clamp(-CLAMP, CLAMP); rec = (tag, idx, a, b, X, pre > 0, raw.abs() < CLAMP)
            elif tag == LET:
                a = pos(G.x[gid]); b = pos(G.y[gid]); c = pos(G.z[gid])
                X = torch.cat([H[a], H[b], H[c]], 1); pre = X @ p['W10'] + p['b10']
                raw = pre.clamp(min=0) + 0.5 * (H[b] + H[c])
                H[idx] = raw.clamp(-CLAMP, CLAMP); rec = (tag, idx, a, b, c, X, pre > 0, raw.abs() < CLAMP)
            else:                               # projection
                c = pos(G.z[gid]); hc = H[c]; pre = hc @ p['Wp'] + p['bp']
                raw = pre.clamp(min=0) + hc
                H[idx] = raw.clamp(-CLAMP, CLAMP); rec = (tag, idx, c, hc, pre > 0, raw.abs() < CLAMP)
            if keep: cache.append(rec)
        out = [H[rootpos]]; pc = None
        if self.pool != 'none':
            Hn = H[npos]; n = lens.numel(); lf = lens.to(self.dtype)[:, None]
            out.append(torch.zeros(n, self.d, device=DEV, dtype=self.dtype).index_add_(0, seg, Hn) / lf)
            if self.pool == 'meanmax':
                mx = torch.full((n, self.d), -1e30, device=DEV, dtype=self.dtype).scatter_reduce_(
                    0, seg[:, None].expand(-1, self.d), Hn, 'amax', include_self=True)
                out.append(mx); at = Hn == mx[seg]
                pc = (at, torch.zeros(n, self.d, device=DEV, dtype=self.dtype).index_add_(0, seg, at.to(self.dtype)))
            else:
                pc = ()
        return torch.cat(out, 1), (H, cache, rootpos, seg, npos, lens, pc)

    @torch.no_grad()
    def backward(self, state, droots):
        """Set every parameter's gradient from the gradient of the loss in the root vectors."""
        H, cache, rootpos, seg, npos, lens, pc = state; p = self.p; d = self.d
        g = {k: torch.zeros_like(v) for k, v in p.items()}
        droots = droots.to(self.dtype)
        dH = torch.zeros_like(H); dH.index_add_(0, rootpos, droots[:, :d])
        if self.pool != 'none':
            dH.index_add_(0, npos, (droots[:, d:2 * d] / lens.to(self.dtype)[:, None])[seg])
            if self.pool == 'meanmax':
                at, ties = pc; dH.index_add_(0, npos, (droots[:, 2 * d:] / ties)[seg] * at)
        for rec in reversed(cache):
            tag, idx = rec[0], rec[1]; dh = dH[idx]
            if tag in (SORT, REF, REC, STR, NAT):
                g[rec[2]].index_add_(0, rec[3], dh)
            elif tag == VAR:
                _, _, vi, has, tp, inside = rec; dr = dh * inside
                g['Evar'].index_add_(0, vi, dr)
                drh = dr[has]; g['P'] += H[tp].T @ drh; dH.index_add_(0, tp, drh @ p['P'].T)
            elif tag == APP and self.nary:
                _, _, head, hh, node, apos, slot, Ha, f, c, act, inside = rec; dr = dh * inside; gp = dr * act
                g['ba'] += gp.sum(0); gl = gp * f
                g['Wh'] += hh.T @ gl; dH.index_add_(0, head, gl @ p['Wh'].T + 0.5 * dr)
                dA = (dr * c)[node]; gn = gl[node]
                for sl in range(7):
                    sel = torch.nonzero(slot == sl).flatten()
                    if sel.numel():
                        g['Wa'][sl] += Ha[sel].T @ gn[sel]; dA[sel] += gn[sel] @ p['Wa'][sl].T
                dH.index_add_(0, apos, dA)
            elif tag in (APP, LAM, ALL):
                _, _, a, b, X, act, inside = rec; dr = dh * inside; gp = dr * act
                g['W%d' % tag] += X.T @ gp; g['b%d' % tag] += gp.sum(0)
                dX = gp @ p['W%d' % tag].T
                dH.index_add_(0, a, dX[:, :d] + 0.5 * dr); dH.index_add_(0, b, dX[:, d:] + 0.5 * dr)
            elif tag == LET:
                _, _, a, b, c, X, act, inside = rec; dr = dh * inside; gp = dr * act
                g['W10'] += X.T @ gp; g['b10'] += gp.sum(0); dX = gp @ p['W10'].T
                dH.index_add_(0, a, dX[:, :d]); dH.index_add_(0, b, dX[:, d:2 * d] + 0.5 * dr); dH.index_add_(0, c, dX[:, 2 * d:] + 0.5 * dr)
            else:
                _, _, c, hc, act, inside = rec; dr = dh * inside; gp = dr * act
                g['Wp'] += hc.T @ gp; g['bp'] += gp.sum(0); dH.index_add_(0, c, gp @ p['Wp'].T + dr)
        for k, v in p.items(): v.grad = g[k]

def retrieval_loss(q, p, pos_q, pos_c, self_q, self_c, scale):
    """Multi-positive softmax loss. `pos_q[i], pos_c[i]` are the (query, candidate)
    pairs that are gold; `self_q, self_c` the pairs where the candidate is the query."""
    S = scale * (q @ p.T)
    neg = S.clone(); neg[pos_q, pos_c] = -1e30; neg[self_q, self_c] = -1e30
    lse = torch.logsumexp(neg, 1)
    per = torch.logaddexp(S[pos_q, pos_c], lse[pos_q]) - S[pos_q, pos_c]
    w = 1.0 / torch.bincount(pos_q, minlength=q.shape[0]).clamp(min=1).to(S.dtype)
    return (per * w[pos_q]).sum() / q.shape[0]

# ------------------------------------------------------------------ main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--d', type=int, default=128); ap.add_argument('--out', type=int, default=128)
    ap.add_argument('--epochs', type=int, default=8); ap.add_argument('--queries', type=int, default=512)
    ap.add_argument('--random', type=int, default=1024); ap.add_argument('--lr', type=float, default=1e-3)
    ap.add_argument('--seed', type=int, default=1); ap.add_argument('--check', action='store_true')
    ap.add_argument('--limit', type=int, default=0, help='train on this many queries per epoch (0 = all)')
    ap.add_argument('--pool', default='none', choices=['none', 'mean', 'meanmax'])
    ap.add_argument('--graph', default='graph', help='graph or graph_nary')
    ap.add_argument('--prem', action='store_true', help='add a learned vector to every premise used in training')
    ap.add_argument('--save', default='', help='write the embeddings of the selected epoch to this file')
    args = ap.parse_args()
    torch.manual_seed(args.seed); rng = np.random.default_rng(args.seed)
    M = load_meta(); G = Graph(args.graph)
    lib_mod, lib_decl, lib_cid, reach = M['lib_mod'], M['lib_decl'], M['lib_cid'], M['reach']
    NL = len(lib_cid)
    rows_of = {}
    for r, c in enumerate(lib_cid): rows_of.setdefault(int(c), []).append(r)
    first = {c: rs[0] for c, rs in rows_of.items()}
    item_row, item_split, gptr, gold = M['item_row'], M['item_split'], M['gold_ptr'], M['gold']
    item_mod = lib_mod[item_row]
    is_val = (item_split == 0) & (item_mod % 50 == 7)
    train = np.nonzero((item_split == 0) & ~is_val)[0]; val = np.nonzero(is_val)[0]; test = np.nonzero(item_split == 1)[0]
    held = np.zeros(reach.shape[0], dtype=bool); held[np.unique(item_mod[np.concatenate([val, test])])] = True
    log('library %d  train %d  validation %d  test %d  graph nodes %d' % (NL, len(train), len(val), len(test), G.n))

    # constant table: constants that at least 3 statements outside the held-out modules mention
    seen_rows = np.nonzero(~held[lib_mod])[0]
    cnt = np.zeros(len(G.roots), dtype=np.int64)
    for c in np.unique(lib_cid[seen_rows]):
        ns = G.nodes[G.ptr[c]:G.ptr[c + 1]]
        m = (G.tag_np[ns] == REF) | (G.tag_np[ns] == REC)
        cs = G.x_np[ns][m]; cnt[cs[cs < len(cnt)]] += 1
    slots = np.zeros(len(G.roots) + 1, dtype=np.int64); keep = np.nonzero(cnt >= 3)[0]; slots[keep] = 1 + np.arange(len(keep))
    log('constant table rows', len(keep))
    enc = Encoder(args.d, torch.from_numpy(slots).to(DEV), args.seed, torch.float64 if args.check else torch.float32, args.pool, G.nary)
    dt = enc.dtype
    g = torch.Generator().manual_seed(args.seed + 100)
    heads = {'Aq': torch.nn.Parameter((torch.randn(enc.width, args.out, generator=g, dtype=torch.float64) / math.sqrt(args.d)).to(DEV, dt)),
             'Ap': torch.nn.Parameter((torch.randn(enc.width, args.out, generator=g, dtype=torch.float64) / math.sqrt(args.d)).to(DEV, dt)),
             'ls': torch.nn.Parameter(torch.tensor(math.log(20.0), device=DEV, dtype=dt))}
    # premise memory: one learned vector per premise that some training proof uses; row 0 stays zero
    prem_row = np.zeros(len(G.roots) + 1, dtype=np.int64)
    if args.prem:
        usedc = np.unique(np.concatenate([gold[gptr[i]:gptr[i + 1]] for i in train]))
        prem_row[usedc] = 1 + np.arange(len(usedc))
        heads['Em'] = torch.nn.Parameter(torch.zeros(len(usedc) + 1, args.out, device=DEV, dtype=dt))
        log('premise memory rows', len(usedc))
    prem_row_t = torch.from_numpy(prem_row).to(DEV)
    def premise(R, cids):
        v = R @ heads['Ap']
        if args.prem: v = v + heads['Em'][prem_row_t[cids]]
        return Fn.normalize(v, dim=1)
    params = list(enc.p.values()) + list(heads.values())
    log('parameters', sum(v.numel() for v in params))
    opt = torch.optim.Adam(params, lr=args.lr)

    # same-module earlier theorems, for hard negatives
    by_mod = {}
    for r in np.argsort(lib_mod * 100000 + lib_decl, kind='stable'): by_mod.setdefault(int(lib_mod[r]), []).append(int(r))
    pos_in_mod = np.zeros(NL, dtype=np.int64)
    for rs in by_mod.values():
        for k, r in enumerate(rs): pos_in_mod[r] = k

    def step_batch(items):
        qc = lib_cid[item_row[items]]
        cand = [gold[gptr[i]:gptr[i + 1]] for i in items]
        hard = []
        for i in items:
            r = item_row[i]; k = pos_in_mod[r]
            if k > 0:
                rs = by_mod[int(lib_mod[r])]; hard += [lib_cid[rs[j]] for j in rng.integers(0, k, size=min(2, k))]
        cands = np.unique(np.concatenate(cand + [np.array(hard, dtype=np.int64), lib_cid[rng.integers(0, NL, size=args.random)]]))
        allc = np.unique(np.concatenate([qc, cands]))
        qi = np.searchsorted(allc, qc); ci = np.searchsorted(allc, cands)
        pq = np.repeat(np.arange(len(items)), [len(c) for c in cand]); pc = np.searchsorted(cands, np.concatenate(cand))
        sc = np.searchsorted(cands, qc); ok = (sc < len(cands)) & (cands[np.minimum(sc, len(cands) - 1)] == qc)
        return allc, qi, ci, pq, pc, np.nonzero(ok)[0], sc[ok]

    def run_step(items, train_mode=True):
        allc, qi, ci, pq, pc, sq, sc = step_batch(items)
        roots, state = enc.forward(G, G.batch(allc))
        R = roots.detach().requires_grad_(True)
        t = lambda a: torch.from_numpy(a).to(DEV)
        q = Fn.normalize(R[t(qi)] @ heads['Aq'], dim=1); p = premise(R[t(ci)], t(allc[ci]))
        loss = retrieval_loss(q, p, t(pq), t(pc), t(sq), t(sc), heads['ls'].exp())
        if train_mode:
            opt.zero_grad(set_to_none=True); loss.backward(); enc.backward(state, R.grad); opt.step()
            with torch.no_grad():
                heads['ls'].clamp_(math.log(5.0), math.log(100.0))
                if args.prem: heads['Em'][0].zero_()
        return float(loss.detach()), state[0].shape[0], len(allc)

    if args.check:
        items = train[:6]; allc, qi, ci, pq, pc, sq, sc = step_batch(items)
        t = lambda a: torch.from_numpy(a).to(DEV); batch = G.batch(allc)
        def value():
            roots, state = enc.forward(G, batch)
            R = roots.detach().requires_grad_(True)
            q = Fn.normalize(R[t(qi)] @ heads['Aq'], dim=1); p = premise(R[t(ci)], t(allc[ci]))
            return retrieval_loss(q, p, t(pq), t(pc), t(sq), t(sc), heads['ls'].exp()), R, state
        loss, R, state = value(); loss.backward(); enc.backward(state, R.grad); worst = 0.0
        for k, v in enc.p.items():
            gflat = v.grad.reshape(-1); flat = v.data.reshape(-1); err = 0.0
            for j in torch.topk(gflat.abs(), min(4, gflat.numel())).indices.tolist():
                if abs(float(gflat[j])) < 1e-7: continue
                old = float(flat[j])
                flat[j] = old + 1e-5; lp = float(value()[0].detach()); flat[j] = old - 1e-5; lm = float(value()[0].detach()); flat[j] = old
                num = (lp - lm) / 2e-5; err = max(err, abs(num - float(gflat[j])) / (abs(num) + abs(float(gflat[j]))))
            log('  %-7s largest gradient %.2e  relative error %.1e' % (k, float(gflat.abs().max()), err)); worst = max(worst, err)
        log('gradient check over %d statements, %d nodes: worst relative error %.2e' % (len(allc), state[0].shape[0], worst))
        return

    lib_u = np.unique(lib_cid); col_of_row = np.searchsorted(lib_u, lib_cid)
    lm_t = torch.from_numpy(lib_mod).to(DEV); ld_t = torch.from_numpy(lib_decl).to(DEV); lc_t = torch.from_numpy(lib_cid).to(DEV)
    reach_t = torch.from_numpy(reach).to(DEV)
    use = np.zeros(NL, dtype=np.int64)
    for i in np.nonzero(item_split == 0)[0]:
        for c in gold[gptr[i]:gptr[i + 1]]: use[first[int(c)]] += 1

    @torch.no_grad()
    def embed(cids, head):
        out = []
        for s in range(0, len(cids), 4096):
            roots, _ = enc.forward(G, G.batch(cids[s:s + 4096]), keep=False)
            out.append(premise(roots, torch.from_numpy(cids[s:s + 4096]).to(DEV)) if head == 'Ap' else Fn.normalize(roots @ heads[head], dim=1))
        return torch.cat(out)

    @torch.no_grad()
    def evaluate(items, P, name):
        """Dense ranking of every accessible library theorem."""
        Q = embed(lib_cid[item_row[items]], 'Aq')        # item order
        Prow = P[torch.from_numpy(col_of_row).to(DEV)]
        hits = np.zeros(3); sl = np.zeros(3); tot = np.zeros(3); gold_n = 0; rr = 0.0; ks = (1, 5, 10)
        for s in range(0, len(items), 256):
            it = items[s:s + 256]; r = torch.from_numpy(item_row[it]).to(DEV)
            S = Q[s:s + 256] @ Prow.T
            tm = lm_t[r]; td = ld_t[r]
            cand = reach_t[tm][:, lm_t] | ((lm_t[None, :] == tm[:, None]) & (ld_t[None, :] < td[:, None]))
            cand &= lc_t[None, :] != lc_t[r][:, None]
            S = S.masked_fill(~cand, -1e30)
            top = S.topk(10, dim=1).indices.cpu().numpy()
            for k, i in enumerate(it):
                gs = gold[gptr[i]:gptr[i + 1]]; gset = set(int(c) for c in gs); gold_n += len(gs)
                topc = [int(lib_cid[j]) for j in top[k]]
                for a, kk in enumerate(ks): hits[a] += len(gset & set(topc[:kk]))
                t10 = set(topc)
                for c in gs:
                    gr = first[int(c)]; cl = 0 if lib_mod[gr] == lib_mod[item_row[i]] else (1 if use[gr] > 0 else 2)
                    tot[cl] += 1; sl[cl] += int(c) in t10
                grow = [x for c in gs for x in rows_of[int(c)]]
                best = S[k, torch.tensor(grow, device=DEV)].max()
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
        for gq in opt.param_groups: gq['lr'] = args.lr * (1 - 0.9 * ep / args.epochs)
        tl = 0.0; nb = 0; t0 = time.time(); nn = 0
        for s in range(0, len(order) - args.queries + 1, args.queries):
            l, nodes, stm = run_step(order[s:s + args.queries]); tl += l; nb += 1; nn += nodes
            if nb == 1 and ep == 0: log('first step: %d statements, %d distinct nodes, loss %.3f' % (stm, nodes, l))
        log('epoch %d  loss %.4f  %.2fs/step  %.0f nodes/step  scale %.1f' % (ep + 1, tl / nb, (time.time() - t0) / nb, nn / nb, float(heads['ls'].exp())))
        P = embed(lib_u, 'Ap')
        v = evaluate(val, P, 'validation'); tres = evaluate(test, P, 'test')
        if v['r10'] > best[0]:
            best = (v['r10'], (ep + 1, tres))
            if args.save:
                torch.save({'lib_u': lib_u, 'P': P.cpu(), 'train': train, 'val': val, 'test': test,
                            'Qtrain': embed(lib_cid[item_row[train]], 'Aq').cpu(), 'Qval': embed(lib_cid[item_row[val]], 'Aq').cpu(),
                            'Qtest': embed(lib_cid[item_row[test]], 'Aq').cpu()}, args.save)
    ep, tres = best[1]
    log('selected epoch %d by validation R@10 %.1f: test R@1 %.1f R@5 %.1f R@10 %.1f MRR %.3f | own %.1f used %.1f unused %.1f' % (
        ep, best[0], tres['r1'], tres['r5'], tres['r10'], tres['mrr'], tres['own'], tres['seen'], tres['new']))

if __name__ == '__main__':
    main()
