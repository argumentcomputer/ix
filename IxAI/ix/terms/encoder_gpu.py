"""A recursive encoder over the shared statement graph of a library, trained
for premise retrieval, in floating point on the GPU.

    encoder_gpu.py [--d 128] [--out 128] [--epochs 8] [--graph graph_nary]
                   [--pool none|mean|meanmax|spine] [--anon P] [--types]
                   [--hard N] [--rare T] [--knn W] [--select r10|rare]
                   [--save RUN.pt] [--save-model MODEL.pt] [--check]

The graph comes from `graph_export` (one node per distinct sub-term under the
types of its free variables' binders; with `--nary` an application and its
arguments are one node). A node's vector is computed bottom-up, once per
batch: a constant is a table row, a bound variable its index embedding plus a
linear map of its binder type's vector, and every other node
`relu([children] W_kind + b_kind)` plus a mean of its children, clamped.

A statement is read out as its root's vector, optionally with the mean and
maximum over its nodes (`meanmax`) and the vectors of its conclusion and of
its hypotheses (`spine`). Two linear heads give the query and premise
embeddings, trained with a multi-positive softmax loss over the batch's gold
premises, negatives from earlier in the query's module, and random library
theorems.

`--anon` gives a constant without a table row an identity vector, and in
training hides the constants of some query modules so the model meets such
constants; `--types` adds a vector from the encoding of the constant's type
(the graph must hold every constant's type: `graph_export --all`).
`--rare` weights a gold premise down by how many training proofs use it.

Evaluation ranks every accessible library theorem (imported, or earlier in the
same module): recall@k is the share of gold premises in the top k and MRR the
reciprocal rank of the first. "Earlier in the same module" follows the
recorded baselines by default and source positions with `IX_ORDER=source`
(see `load_meta`).
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
def source_order(lib_mod):
    """For every library theorem, the rank of its source position within its
    module, from `positions.tsv` (`ix/premises/Positions.lean`). Theorems at one
    position (one command) share a rank; one without a position ranks last."""
    cache = ROOT + '/graph/source_order.npy'
    if os.path.exists(cache): return np.load(cache)
    pos = {}
    for line in open(DATA + '/mathlib-full/positions.tsv'):
        n, l, c, _ = line.rstrip('\n').split('\t'); pos[n] = (int(l), int(c))
    key = []
    for line in open(DATA + '/mathlib-full/decls.tsv'):
        if line.startswith('lib\t'):
            l, c = pos.get(line.split('\t', 2)[1], (-1, -1)); key.append(l * 100000 + c if l >= 0 else -1)
    key = np.array(key, dtype=np.int64); out = np.full(len(key), 1 << 20, dtype=np.int64)
    for m in np.unique(lib_mod):
        rows = np.nonzero((lib_mod == m) & (key >= 0))[0]
        out[rows] = np.unique(key[rows], return_inverse=True)[1]
    np.save(cache, out)
    return out

def load_meta():
    """The premise dataset as arrays. `lib_decl` orders the theorems of a module:
    by default it is the index in the module's table of names, as the recorded
    baselines use, which does not follow source order; with `IX_ORDER=source` in
    the environment it is the rank of the theorem's source position."""
    meta = load_meta_index()
    if os.environ.get('IX_ORDER') == 'source': meta['lib_decl'] = source_order(meta['lib_mod'])
    return meta

def load_meta_index():
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
    def __init__(self, sub='graph', root=ROOT):
        base = root + '/' + sub
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
        self.typed = torch.from_numpy(self.roots != 0xFFFFFFFF).to(DEV)

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
    def __init__(self, d, slots, seed, dtype=torch.float32, pool='none', nary=False, anon=False, types=False):
        g = torch.Generator().manual_seed(seed); s = 1.0 / math.sqrt(d)
        def rn(*shape): return torch.nn.Parameter((torch.randn(*shape, generator=g, dtype=torch.float64) * s).to(DEV, dtype))
        def zs(*shape): return torch.nn.Parameter(torch.zeros(*shape, device=DEV, dtype=dtype))
        self.d = d; self.dtype = dtype; self.pool = pool
        self.width = d * {'none': 1, 'mean': 2, 'meanmax': 3, 'spine': 5}[pool]
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
        # A constant without a table row is the unseen row plus a fixed random
        # vector picked by its id, so two mentions of one unseen constant agree
        # and mentions of different ones differ. `hidden` marks constants to
        # treat as unseen in the current pass, `mix` the multiplier and offset
        # of the id hash.
        self.anon = anon; self.hidden = None; self.mix = (0x9E3779B1, 0)
        if anon:
            self.p['ga'] = torch.nn.Parameter(torch.ones(1, device=DEV, dtype=dtype))
            self.R = (torch.randn(1 << 16, d, generator=torch.Generator().manual_seed(977), dtype=torch.float64) * s).to(DEV, dtype)
        # `tvec` holds, during a pass, constant ids and a vector for each made
        # from the encoding of that constant's type; `dtv` collects its gradient
        self.types = types; self.tvec = None; self.dtv = None; self.tcap = 512
        if types: self.p['Pd'] = torch.nn.Parameter(0.3 * rn(self.width, d).data)

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
            if tag in (REF, REC) and self.anon:
                cid = G.x[gid].clamp(max=self.slot.numel() - 1); row = self.slot[cid]
                if self.hidden is not None: row = torch.where(self.hidden[cid], torch.zeros_like(row), row)
                Rv = self.R[(cid * self.mix[0] + self.mix[1]) & 0xFFFF] * (row == 0)[:, None]
                h = p['Econst'][row] + p['ga'] * Rv; tj = None
                if self.tvec is not None:
                    D, TV = self.tvec; j = torch.searchsorted(D, cid).clamp(max=D.numel() - 1)
                    ok = (row == 0) & (D[j] == cid); h = h + TV[j] * ok[:, None]; tj = (j, ok)
                H[idx] = h; rec = (tag, idx, 'Econst', row, Rv, tj)
            elif tag in (SORT, REF, REC, STR, NAT):
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
            if self.pool in ('meanmax', 'spine'):
                mx = torch.full((n, self.d), -1e30, device=DEV, dtype=self.dtype).scatter_reduce_(
                    0, seg[:, None].expand(-1, self.d), Hn, 'amax', include_self=True)
                out.append(mx); at = Hn == mx[seg]
                pc = (at, torch.zeros(n, self.d, device=DEV, dtype=self.dtype).index_add_(0, seg, at.to(self.dtype)))
            else:
                pc = ()
            if self.pool == 'spine':
                # a statement `forall x1 : T1, ..., xn : Tn, C` also reads out C and the mean of the Ti
                cur = ids[rootpos]; ar = torch.arange(n, device=DEV); ds = [ar[:0]]; dn = [cur[:0]]
                while True:
                    m = G.tag[cur] == ALL
                    if not bool(m.any()): break
                    ds.append(ar[m]); dn.append(G.x[cur[m]]); cur = torch.where(m, G.y[cur], cur)
                cpos = pos(cur); dstmt = torch.cat(ds); dpos = pos(torch.cat(dn))
                ndom = torch.bincount(dstmt, minlength=n).clamp(min=1).to(self.dtype)[:, None]
                out.append(H[cpos]); out.append(torch.zeros(n, self.d, device=DEV, dtype=self.dtype).index_add_(0, dstmt, H[dpos]) / ndom)
                pc = pc + (cpos, dstmt, dpos, ndom)
        return torch.cat(out, 1), (H, cache, rootpos, seg, npos, lens, pc)

    @torch.no_grad()
    def encode(self, G, cids, keep=True):
        """Root vectors of the statements `cids` (ascending constant ids). With
        `types`, a constant without a table row first gets a vector from the
        encoding of its own type, inside which such constants are identities."""
        batch = G.batch(cids); self.tvec = None; aux = None
        if self.types:
            ids = batch[0]; tg = G.tag[ids]; c = torch.unique(G.x[ids][(tg == REF) | (tg == REC)])
            c = c[c < G.typed.numel()]; row = self.slot[c]
            if self.hidden is not None: row = torch.where(self.hidden[c], torch.zeros_like(row), row)
            D = c[(row == 0) & G.typed[c]]
            # in training, at most `tcap` of the hidden constants get a type vector, which bounds the extra pass
            if self.hidden is not None and D.numel() > self.tcap:
                D = D[torch.randperm(D.numel(), device=DEV)[:self.tcap]].sort().values
            if D.numel():
                ra, sa = self.forward(G, G.batch(D.cpu().numpy()), keep)
                pre = ra @ self.p['Pd']; self.tvec = (D, pre.clamp(-CLAMP, CLAMP)); aux = (ra, sa, pre)
        roots, state = self.forward(G, batch, keep); self.tvec = None
        return roots, (state, aux)

    @torch.no_grad()
    def learn(self, st, droots):
        """Set every parameter's gradient from the gradient of the loss in the root vectors `encode` returned."""
        state, aux = st
        if aux is None: return self.backward(state, droots)
        ra, sa, pre = aux; self.dtv = torch.zeros_like(pre)
        self.backward(state, droots)
        dpre = self.dtv * (pre.abs() < CLAMP); gPd = ra.T @ dpre
        self.backward(sa, dpre @ self.p['Pd'].T, add=True)
        self.p['Pd'].grad += gPd

    @torch.no_grad()
    def backward(self, state, droots, add=False):
        """Set every parameter's gradient from the gradient of the loss in the
        root vectors of one `forward` pass, or with `add` accumulate into it."""
        H, cache, rootpos, seg, npos, lens, pc = state; p = self.p; d = self.d
        g = {k: torch.zeros_like(v) for k, v in p.items()}
        droots = droots.to(self.dtype)
        dH = torch.zeros_like(H); dH.index_add_(0, rootpos, droots[:, :d])
        if self.pool != 'none':
            dH.index_add_(0, npos, (droots[:, d:2 * d] / lens.to(self.dtype)[:, None])[seg])
            if self.pool in ('meanmax', 'spine'):
                at, ties = pc[:2]; dH.index_add_(0, npos, (droots[:, 2 * d:3 * d] / ties)[seg] * at)
            if self.pool == 'spine':
                cpos, dstmt, dpos, ndom = pc[2:]
                dH.index_add_(0, cpos, droots[:, 3 * d:4 * d]); dH.index_add_(0, dpos, (droots[:, 4 * d:] / ndom)[dstmt])
        for rec in reversed(cache):
            tag, idx = rec[0], rec[1]; dh = dH[idx]
            if tag in (SORT, REF, REC, STR, NAT):
                g[rec[2]].index_add_(0, rec[3], dh)
                if len(rec) > 4:
                    g['ga'] += (dh * rec[4]).sum()
                    if rec[5] is not None: self.dtv.index_add_(0, rec[5][0][rec[5][1]], dh[rec[5][1]])
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
        for k, v in p.items(): v.grad = v.grad + g[k] if add else g[k]

def retrieval_loss(q, p, pos_q, pos_c, self_q, self_c, scale, pw=None):
    """Multi-positive softmax loss. `pos_q[i], pos_c[i]` are the (query, candidate)
    pairs that are gold, with weight `pw[i]` if given; `self_q, self_c` the
    pairs where the candidate is the query."""
    S = scale * (q @ p.T)
    neg = S.clone(); neg[pos_q, pos_c] = -1e30; neg[self_q, self_c] = -1e30
    lse = torch.logsumexp(neg, 1)
    per = torch.logaddexp(S[pos_q, pos_c], lse[pos_q]) - S[pos_q, pos_c]
    w = 1.0 / torch.bincount(pos_q, minlength=q.shape[0]).clamp(min=1).to(S.dtype)
    if pw is not None: per = per * pw
    return (per * w[pos_q]).sum() / q.shape[0]

def save_model(path, enc, heads, slots, args):
    torch.save({'enc': {k: v.detach().cpu() for k, v in enc.p.items()}, 'heads': {k: v.detach().cpu() for k, v in heads.items()},
                'slots': slots, 'args': vars(args)}, path)

def load_model(path):
    """The encoder and heads `--save-model` wrote. `enc.slot` maps the training
    library's constant ids to table rows; `ck['slots']` is the same as an array."""
    ck = torch.load(path, weights_only=False); a = ck['args']
    enc = Encoder(a['d'], torch.from_numpy(ck['slots']).to(DEV), a['seed'], torch.float32, a['pool'], 'Wh' in ck['enc'],
                  a.get('anon', 0) > 0, a.get('types', False))
    for k, v in ck['enc'].items(): enc.p[k].data.copy_(v.to(DEV))
    return enc, {k: v.to(DEV) for k, v in ck['heads'].items()}, ck

# ------------------------------------------------------------------ main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--d', type=int, default=128); ap.add_argument('--out', type=int, default=128)
    ap.add_argument('--epochs', type=int, default=8); ap.add_argument('--queries', type=int, default=512)
    ap.add_argument('--random', type=int, default=1024); ap.add_argument('--lr', type=float, default=1e-3)
    ap.add_argument('--seed', type=int, default=1); ap.add_argument('--check', action='store_true')
    ap.add_argument('--limit', type=int, default=0, help='train on this many queries per epoch (0 = all)')
    ap.add_argument('--pool', default='none', choices=['none', 'mean', 'meanmax', 'spine'])
    ap.add_argument('--graph', default='graph', help='graph or graph_nary')
    ap.add_argument('--prem', action='store_true', help='add a learned vector to every premise used in training')
    ap.add_argument('--save', default='', help='write the embeddings of the selected epoch to this file')
    ap.add_argument('--save-model', default='', help='write the parameters of the selected epoch to this file')
    ap.add_argument('--hard', type=int, default=2, help='negatives per query drawn from the theorems before it in its module')
    ap.add_argument('--rare', type=float, default=0.0, help='weight a gold premise that n training proofs use by T / (T + n)')
    ap.add_argument('--select', default='r10', choices=['r10', 'rare'], help='validation score that picks the epoch: recall@10 of all '
                    'gold premises, or of those that at most 20 training proofs use')
    ap.add_argument('--types', action='store_true', help='with --anon and a graph exported with --all: give a constant without '
                    'a table row a vector from the encoding of its type')
    ap.add_argument('--knn', type=float, default=0.0, help='weight of the usage-lookup loss: a third head embeds theorems so '
                    'that the training theorems nearest a query, outside its module, use the premises its proof uses')
    ap.add_argument('--wdense', type=float, default=1.0, help='weight of the query-premise loss')
    ap.add_argument('--anon', type=float, default=0.0, help='give unseen constants an identity vector, and in training '
                    'treat the constants of each query module as unseen with this probability')
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
    # `home` is the earliest module with a statement mentioning the constant,
    # which stands in for the module that defines it
    cnt = np.zeros(len(G.roots), dtype=np.int64); home = np.full(len(G.roots) + 1, 1 << 30, dtype=np.int64)
    seen_c = set(np.unique(lib_cid[seen_rows]).tolist())
    for c in np.unique(lib_cid):
        ns = G.nodes[G.ptr[c]:G.ptr[c + 1]]
        m = (G.tag_np[ns] == REF) | (G.tag_np[ns] == REC)
        cs = G.x_np[ns][m]; cs = cs[cs < len(cnt)]
        if c in seen_c: cnt[cs] += 1
        home[cs] = np.minimum(home[cs], lib_mod[first[int(c)]])
    slots = np.zeros(len(G.roots) + 1, dtype=np.int64); keep = np.nonzero(cnt >= 3)[0]; slots[keep] = 1 + np.arange(len(keep))
    log('constant table rows', len(keep))
    enc = Encoder(args.d, torch.from_numpy(slots).to(DEV), args.seed, torch.float64 if args.check else torch.float32, args.pool, G.nary, args.anon > 0, args.types)
    dt = enc.dtype
    g = torch.Generator().manual_seed(args.seed + 100)
    heads = {'Aq': torch.nn.Parameter((torch.randn(enc.width, args.out, generator=g, dtype=torch.float64) / math.sqrt(args.d)).to(DEV, dt)),
             'Ap': torch.nn.Parameter((torch.randn(enc.width, args.out, generator=g, dtype=torch.float64) / math.sqrt(args.d)).to(DEV, dt)),
             'ls': torch.nn.Parameter(torch.tensor(math.log(20.0), device=DEV, dtype=dt))}
    if args.knn > 0:
        heads['Ak'] = torch.nn.Parameter((torch.randn(enc.width, args.out, generator=g, dtype=torch.float64) / math.sqrt(args.d)).to(DEV, dt))
        heads['lk'] = torch.nn.Parameter(torch.tensor(math.log(20.0), device=DEV, dtype=dt))
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
    for r in np.argsort(lib_mod * (1 << 21) + lib_decl, kind='stable'): by_mod.setdefault(int(lib_mod[r]), []).append(int(r))
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
                rs = by_mod[int(lib_mod[r])]; hard += [lib_cid[rs[j]] for j in rng.integers(0, k, size=min(args.hard, k))]
        cands = np.unique(np.concatenate(cand + [np.array(hard, dtype=np.int64), lib_cid[rng.integers(0, NL, size=args.random)]]))
        allc = np.unique(np.concatenate([qc, cands]))
        qi = np.searchsorted(allc, qc); ci = np.searchsorted(allc, cands)
        pq = np.repeat(np.arange(len(items)), [len(c) for c in cand]); pc = np.searchsorted(cands, np.concatenate(cand))
        sc = np.searchsorted(cands, qc); ok = (sc < len(cands)) & (cands[np.minimum(sc, len(cands) - 1)] == qc)
        return allc, qi, ci, pq, pc, np.nonzero(ok)[0], sc[ok]

    def hide(items):
        """Treat the constants of a random share of the query modules as unseen, under a fresh id hash."""
        qm = np.unique(item_mod[items]); sel = qm[rng.random(len(qm)) < args.anon]
        enc.hidden = torch.from_numpy(np.isin(home, sel)).to(DEV)
        enc.mix = (int(rng.integers(1 << 30)) * 2 + 1, int(rng.integers(1 << 16)))

    if args.rare > 0:
        used_n = np.bincount(np.concatenate([gold[gptr[i]:gptr[i + 1]] for i in train]), minlength=len(G.roots) + 1)
        rare_w = args.rare / (args.rare + used_n)
    # usage memory: the premises (columns of `lib_u`) each training theorem uses,
    # and `bank`, the lookup embedding of every training theorem
    mem = {}
    if args.knn > 0:
        lib_u0 = np.unique(lib_cid)
        tj = np.repeat(np.arange(len(train)), [gptr[i + 1] - gptr[i] for i in train])
        tp = np.searchsorted(lib_u0, np.concatenate([gold[gptr[i]:gptr[i + 1]] for i in train]))
        mem['U'] = torch.sparse_coo_tensor(np.stack([tp, tj]), np.ones(len(tj), dtype=np.float32), (len(lib_u0), len(train))).coalesce().to(DEV)
        mem['mod'] = torch.from_numpy(item_mod[train]).to(DEV)
        pos_in_train = np.zeros(len(item_row), dtype=np.int64); pos_in_train[train] = np.arange(len(train))

    def votes(K, mods):
        """Soft usage lookup, queries x premises: every training theorem outside
        the query's module votes for the premises its proof uses, with a
        softmax over its similarity to the query as the weight."""
        S = heads['lk'].exp() * (K @ mem['bank'].T)
        S = S.masked_fill(mem['mod'][None, :] == mods[:, None], -1e30)
        return torch.sparse.mm(mem['U'], torch.softmax(S, 1).T).T

    def run_step(items, train_mode=True):
        allc, qi, ci, pq, pc, sq, sc = step_batch(items)
        if args.anon > 0: hide(items)
        roots, state = enc.encode(G, allc)
        R = roots.detach().requires_grad_(True)
        t = lambda a: torch.from_numpy(a).to(DEV)
        q = Fn.normalize(R[t(qi)] @ heads['Aq'], dim=1); p = premise(R[t(ci)], t(allc[ci]))
        pw = t(rare_w[allc[ci][pc]]).to(dt) if args.rare > 0 else None
        loss = args.wdense * retrieval_loss(q, p, t(pq), t(pc), t(sq), t(sc), heads['ls'].exp(), pw)
        if args.knn > 0:
            kq = Fn.normalize(R[t(qi)] @ heads['Ak'], dim=1)
            V = votes(kq, t(item_mod[items]))
            tq = t(pq); v = V[tq, t(np.searchsorted(lib_u0, allc[ci][pc]))]; has = v > 0
            w = 1.0 / torch.bincount(tq[has], minlength=len(items)).clamp(min=1).to(v.dtype)
            loss = loss - args.knn * (torch.log(v[has].clamp(min=1e-12)) * w[tq[has]]).sum() / len(items)
        if train_mode:
            opt.zero_grad(set_to_none=True); loss.backward(); enc.learn(state, R.grad); opt.step()
            with torch.no_grad():
                heads['ls'].clamp_(math.log(5.0), math.log(100.0))
                if args.prem: heads['Em'][0].zero_()
                if args.knn > 0:
                    heads['lk'].clamp_(math.log(5.0), math.log(200.0))
                    mem['bank'][t(pos_in_train[items])] = kq.detach()
        return float(loss.detach()), state[0][0].shape[0], len(allc)

    if args.check:
        items = train[:6]; allc, qi, ci, pq, pc, sq, sc = step_batch(items)
        if args.anon > 0: hide(items)
        t = lambda a: torch.from_numpy(a).to(DEV)
        def value():
            roots, state = enc.encode(G, allc)
            R = roots.detach().requires_grad_(True)
            q = Fn.normalize(R[t(qi)] @ heads['Aq'], dim=1); p = premise(R[t(ci)], t(allc[ci]))
            return retrieval_loss(q, p, t(pq), t(pc), t(sq), t(sc), heads['ls'].exp()), R, state
        loss, R, state = value(); loss.backward(); enc.learn(state, R.grad); worst = 0.0
        for k, v in enc.p.items():
            gflat = v.grad.reshape(-1); flat = v.data.reshape(-1); err = 0.0
            for j in torch.topk(gflat.abs(), min(4, gflat.numel())).indices.tolist():
                if abs(float(gflat[j])) < 1e-7: continue
                old = float(flat[j])
                flat[j] = old + 1e-5; lp = float(value()[0].detach()); flat[j] = old - 1e-5; lm = float(value()[0].detach()); flat[j] = old
                num = (lp - lm) / 2e-5; err = max(err, abs(num - float(gflat[j])) / (abs(num) + abs(float(gflat[j]))))
            log('  %-7s largest gradient %.2e  relative error %.1e' % (k, float(gflat.abs().max()), err)); worst = max(worst, err)
        log('gradient check over %d statements, %d nodes: worst relative error %.2e' % (len(allc), state[0][0].shape[0], worst))
        return

    lib_u = np.unique(lib_cid); col_of_row = np.searchsorted(lib_u, lib_cid)
    lm_t = torch.from_numpy(lib_mod).to(DEV); ld_t = torch.from_numpy(lib_decl).to(DEV); lc_t = torch.from_numpy(lib_cid).to(DEV)
    reach_t = torch.from_numpy(reach).to(DEV)
    use = np.zeros(NL, dtype=np.int64)
    for i in np.nonzero(item_split == 0)[0]:
        for c in gold[gptr[i]:gptr[i + 1]]: use[first[int(c)]] += 1

    @torch.no_grad()
    def embed(cids, head):
        out = []; enc.hidden = None; enc.mix = (0x9E3779B1, 0)
        for s in range(0, len(cids), 4096):
            roots, _ = enc.encode(G, cids[s:s + 4096], keep=False)
            out.append(premise(roots, torch.from_numpy(cids[s:s + 4096]).to(DEV)) if head == 'Ap' else Fn.normalize(roots @ heads[head], dim=1))
        return torch.cat(out)

    @torch.no_grad()
    def evaluate(items, P, name, lookup=False):
        """Ranking of every accessible library theorem, by query-premise
        similarity or, with `lookup`, by the votes of the usage lookup."""
        Q = embed(lib_cid[item_row[items]], 'Ak' if lookup else 'Aq')        # item order
        col_t = torch.from_numpy(col_of_row).to(DEV)
        Prow = None if lookup else P[col_t]
        hits = np.zeros(3); sl = np.zeros(3); tot = np.zeros(3); gold_n = 0; rr = 0.0; ks = (1, 5, 10); rare = np.zeros(2)
        for s in range(0, len(items), 256):
            it = items[s:s + 256]; r = torch.from_numpy(item_row[it]).to(DEV)
            tm = lm_t[r]; td = ld_t[r]
            S = votes(Q[s:s + 256], tm)[:, col_t] if lookup else Q[s:s + 256] @ Prow.T
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
                    if use[gr] <= 20: rare += (int(c) in t10, 1)
                grow = [x for c in gs for x in rows_of[int(c)]]
                best = S[k, torch.tensor(grow, device=DEV)].max()
                if best > -1e29: rr += 1.0 / (int((S[k] > best).sum()) + 1)
        res = dict(r1=100 * hits[0] / gold_n, r5=100 * hits[1] / gold_n, r10=100 * hits[2] / gold_n, mrr=rr / len(items),
                   own=100 * sl[0] / max(tot[0], 1), seen=100 * sl[1] / max(tot[1], 1), new=100 * sl[2] / max(tot[2], 1),
                   rare=100 * rare[0] / max(rare[1], 1))
        log('%-10s R@1 %4.1f  R@5 %4.1f  R@10 %4.1f  MRR %.3f | own module %4.1f  imported, used %4.1f  imported, unused %4.1f | rare %4.1f' % (
            name, res['r1'], res['r5'], res['r10'], res['mrr'], res['own'], res['seen'], res['new'], res['rare']))
        return res

    best = (-1, None)
    for ep in range(args.epochs):
        order = rng.permutation(train)
        if args.limit: order = order[:args.limit]
        if args.knn > 0 and 'bank' not in mem: mem['bank'] = embed(lib_cid[item_row[train]], 'Ak')
        for gq in opt.param_groups: gq['lr'] = args.lr * (1 - 0.9 * ep / args.epochs)
        tl = 0.0; nb = 0; t0 = time.time(); nn = 0
        for s in range(0, len(order) - args.queries + 1, args.queries):
            l, nodes, stm = run_step(order[s:s + args.queries]); tl += l; nb += 1; nn += nodes
            if nb == 1 and ep == 0: log('first step: %d statements, %d distinct nodes, loss %.3f' % (stm, nodes, l))
        log('epoch %d  loss %.4f  %.2fs/step  %.0f nodes/step  scale %.1f' % (ep + 1, tl / nb, (time.time() - t0) / nb, nn / nb, float(heads['ls'].detach().exp())))
        P = embed(lib_u, 'Ap')
        v = evaluate(val, P, 'validation'); tres = evaluate(test, P, 'test'); score = v[args.select]
        if args.knn > 0:
            mem['bank'] = embed(lib_cid[item_row[train]], 'Ak')
            log('lookup scale %.1f' % float(heads['lk'].detach().exp()))
            score += evaluate(val, P, 'val lookup', True)['r10']; evaluate(test, P, 'test lookup', True)
        if score > best[0]:
            best = (score, (ep + 1, tres))
            if args.save_model: save_model(args.save_model, enc, heads, slots, args)
            if args.save:
                out = {'lib_u': lib_u, 'P': P.cpu(), 'train': train, 'val': val, 'test': test}
                for hd in ('Aq', 'Ak') if args.knn > 0 else ('Aq',):
                    for nm, its in (('train', train), ('val', val), ('test', test)):
                        out[hd[1].upper() + nm] = embed(lib_cid[item_row[its]], hd).cpu()
                if args.knn > 0: out['lk'] = float(heads['lk'].detach().exp())
                torch.save(out, args.save)
    ep, tres = best[1]
    log('selected epoch %d by validation score %.1f: test R@1 %.1f R@5 %.1f R@10 %.1f MRR %.3f | own %.1f used %.1f unused %.1f | rare %.1f' % (
        ep, best[0], tres['r1'], tres['r5'], tres['r10'], tres['mrr'], tres['own'], tres['seen'], tres['new'], tres['rare']))

if __name__ == '__main__':
    main()
