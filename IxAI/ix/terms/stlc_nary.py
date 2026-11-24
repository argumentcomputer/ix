"""Two structural variants of the `stlc_toy` encoder.

Shared graphs: terms are hash-consed into one node table per batch (or per
pool). A node's key is (kind, children, payload, binder annotation node), all
children already canonical, so two occurrences share a node exactly when the
sub-terms are equal and the annotations of the binders of their free
variables are equal: with `mode='binder'` a variable's vector is a function
of its index and its binder's annotation vector, so equal keys mean equal
vectors.

N-ary applications: a spine `f a1 ... an` becomes one node with ordered
children (head, a1, ..., an) and the cell

    X    = [h_f ; a1 ; a2 ; a3 ; a4 + a5 + ... + an]       (zero blocks when absent)
    pre  = (X W_napp) * 2^-s(n) + b_napp
    skip = h_f / 2 + (a1 + ... + an) / 2^(1 + ceil(log2 n))
    h    = clamp(relu(pre) + skip)

W_napp is (K+1)d x d: one block for the head, one per argument position below
K, and one shared by positions K and beyond (summing those arguments before
the product is the same as applying the shared block to each). With n = 1
the skip is the binary cell's mean of the two children. s(n) is 0 unless
`scale='sqrt'`, where it is floor(log2(n + 1) / 2).

Usage: python stlc_nary.py check|share|data|float|int|sharetrain
"""
import numpy as np, random, sys, time, os, math
import stlc_toy as T
from stlc_toy import (N, B, arrow, TN, TB, ARR, CONST, VAR, LAM, APP, Encoder, IntEncoder, Batch, F, S, WORD,
                      rshift, imat, halvings, rand_type, result_chain, infer, mutate, flatten, accuracy)

NAPP = 7
K = 4

# ---------------------------------------------------------------- wider constants
EXTRA = [('cmp4', arrow(N, arrow(N, arrow(B, arrow(B, B))))),
         ('sel4', arrow(B, arrow(arrow(B, N), arrow(N, arrow(N, N))))),
         ('iter5', arrow(arrow(N, N), arrow(N, arrow(B, arrow(N, arrow(N, N)))))),
         ('mix6', arrow(B, arrow(N, arrow(B, arrow(N, arrow(N, arrow(B, B)))))))]

def extend_consts():
    """Add the 4- to 6-argument constants to the toy's tables (in this process)."""
    if 'cmp4' in T.CTYPE: return
    for name, ty in EXTRA:
        T.CID[name] = len(T.CONSTS); T.CONSTS.append((name, ty)); T.CTYPE[name] = ty

def gen(rng, ctx, Ty, depth):
    """`stlc_toy.gen` with one more chain step: a wide constant whose deep
    argument sits at a random base-typed position."""
    if not isinstance(Ty, tuple) and getattr(rng, 'chain', 0) > 0 and rng.random() < 0.5:
        rng.chain -= 1; c = rng.random()
        if c < 0.4:
            cands = [(n, A) for n, A in EXTRA if result_chain(A)[-1][1] == Ty]
            name, A = rng.choice(cands); args = result_chain(A)[-1][0]
            deep = rng.choice([i for i, a in enumerate(args) if not isinstance(a, tuple)])
            t = ('const', name)
            for i, a in enumerate(args): t = ('app', t, gen(rng, ctx, a, depth if i == deep else 0))
            return t
        c = (c - 0.4) / 0.6
        if Ty == N:
            if c < 0.5: return ('app', ('const', 'succ'), gen(rng, ctx, N, depth))
            if c < 0.75: return ('app', ('app', ('const', 'add'), gen(rng, ctx, N, depth)), gen(rng, ctx, N, 0))
            return ('app', ('app', ('app', ('const', 'ite'), gen(rng, ctx, B, depth)), gen(rng, ctx, N, 0)), gen(rng, ctx, N, 0))
        if c < 0.5: return ('app', ('const', 'not'), gen(rng, ctx, B, depth))
        return ('app', ('const', 'iszero'), gen(rng, ctx, N, depth))
    heads = []
    for i, A in enumerate(ctx):
        for args, res in result_chain(A):
            if res == Ty: heads.append((('var', i), args))
    for name, A in T.CONSTS:
        for args, res in result_chain(A):
            if res == Ty: heads.append((('const', name), args))
    flat = [h for h in heads if not h[1]]
    if depth <= 0:
        if flat: return rng.choice(flat)[0]
        if isinstance(Ty, tuple): return ('lam', Ty[1], gen(rng, [Ty[1]] + ctx, Ty[2], 0))
        return ('const', 'zero' if Ty == N else 'tt')
    r = rng.random()
    if isinstance(Ty, tuple) and r < 0.5:
        return ('lam', Ty[1], gen(rng, [Ty[1]] + ctx, Ty[2], depth - 1))
    applied = [h for h in heads if h[1]]
    if r < 0.12 and flat: return rng.choice(flat)[0]
    if r < 0.75 and applied:
        head, args = rng.choice(applied)
        t = head
        if len(args) < 4:
            for A in args: t = ('app', t, gen(rng, ctx, A, depth - 1))
            return t
        # wide heads recurse into one argument only, keeping term size near the toy's
        deep = rng.randrange(len(args))
        for i, A in enumerate(args): t = ('app', t, gen(rng, ctx, A, depth - 1 if i == deep else 0))
        return t
    A = rand_type(rng, 1)
    return ('app', gen(rng, ctx, arrow(A, Ty), depth - 1), gen(rng, ctx, A, depth - 1))

def sample(rng, depth, chain=0):
    ctx = [rand_type(rng, 1) for _ in range(5)]
    rng.chain = chain
    t = gen(rng, ctx, rand_type(rng, 1), depth)
    for A in ctx: t = ('lam', A, t)
    if rng.random() < 0.5:
        for _ in range(6):
            t = mutate(rng, t)
            if infer([], t) is None: break
    return t, int(infer([], t) is not None)

def make_items(rng, n, depth, chain, sampler):
    items = []; need = {0: n // 2, 1: n - n // 2}
    while need[0] + need[1] > 0:
        t, y = sampler(rng, rng.randint(3, depth), rng.randint(*chain))
        if need[y] > 0: items.append((t, y)); need[y] -= 1
    rng.shuffle(items)
    return items

# ---------------------------------------------------------------- graphs
class Graph:
    """Node table; with `share`, equal keys give one node. `cond=False` drops
    the binder annotation from variable keys (only for counting what the
    conditioning costs; the vectors would then be wrong in binder mode)."""
    def __init__(self, share, nary=False, cond=True):
        self.share = share; self.nary = nary; self.cond = cond; self.rows = []; self.ids = {}

    def node(self, kind, ch, pay, bt):
        key = (kind, ch, pay, bt if self.cond else -2)
        if self.share:
            i = self.ids.get(key)
            if i is not None: return i
        if kind == VAR: lvl = 1 + (self.rows[bt][4] if bt >= 0 else 0)
        else: lvl = max((self.rows[c][4] + 1 for c in ch), default=0)
        self.rows.append((kind, ch, pay, bt, lvl))
        if self.share: self.ids[key] = len(self.rows) - 1
        return len(self.rows) - 1

    def ty(self, t):
        if t == N: return self.node(TN, (), 0, -1)
        if t == B: return self.node(TB, (), 0, -1)
        return self.node(ARR, (self.ty(t[1]), self.ty(t[2])), 0, -1)

    def term(self, t, env=()):
        k = t[0]
        if k == 'var': return self.node(VAR, (), min(t[1], 31), env[t[1]] if t[1] < len(env) else -1)
        if k == 'const': return self.node(CONST, (), T.CID[t[1]], -1)
        if k == 'lam':
            a = self.ty(t[1]); return self.node(LAM, (a, self.term(t[2], (a,) + env)), 0, -1)
        if not self.nary: return self.node(APP, (self.term(t[1], env), self.term(t[2], env)), 0, -1)
        args = []
        while t[0] == 'app': args.append(t[2]); t = t[1]
        h = self.term(t, env)
        return self.node(NAPP, (h,) + tuple(self.term(a, env) for a in reversed(args)), 0, -1)

def counts(g):
    kinds = np.array([r[0] for r in g.rows])
    return dict(nodes=len(g.rows), cells=int(np.isin(kinds, (ARR, LAM, APP, NAPP)).sum()), types=int((kinds == ARR).sum()),
                vars=int((kinds == VAR).sum()))

class GBatch:
    def __init__(self, items, share, nary=False):
        g = Graph(share, nary); self.roots = np.array([g.term(t) for t, _ in items])
        self.y = np.where(np.array([y for _, y in items]) == 1, 1.0, -1.0)
        rows = g.rows; self.n = len(rows); self.counts = counts(g)
        kind = np.array([r[0] for r in rows]); lvl = np.array([r[4] for r in rows])
        pay = np.array([r[2] for r in rows]); bt = np.array([r[3] for r in rows])
        self.groups = []
        for lv in range(int(lvl.max()) + 1):
            for k in range(8):
                idx = np.nonzero((lvl == lv) & (kind == k))[0]
                if not idx.size: continue
                if k in (ARR, LAM, APP): ex = (np.array([rows[i][1][0] for i in idx]), np.array([rows[i][1][1] for i in idx]))
                elif k == NAPP:
                    ar = np.array([len(rows[i][1]) - 1 for i in idx]); A = np.full((idx.size, ar.max()), -1)
                    for j, i in enumerate(idx): A[j, :ar[j]] = rows[i][1][1:]
                    ex = (np.array([rows[i][1][0] for i in idx]), A, ar)
                else: ex = (pay[idx], bt[idx])
                self.groups.append((k, idx, ex))
        self.depth = int(lvl.max())

def napp_consts(ar, scale):
    s = np.floor(np.log2(ar + 1) / 2).astype(np.int64) if scale == 'sqrt' else np.zeros_like(ar)
    c = np.ceil(np.log2(ar)).astype(np.int64)
    return s[:, None], c[:, None]

# ---------------------------------------------------------------- float model
class GEncoder(Encoder):
    """`Encoder` over a `GBatch`: shared nodes, duplicate roots, n-ary cells."""
    def __init__(self, d, mode, seed, nary=False, scale='none', **kw):
        super().__init__(d, mode, seed, **kw); self.nary = nary; self.scale = scale
        if nary:
            r = np.random.default_rng(seed + 1000)
            del self.p['W%d' % APP], self.p['b%d' % APP]
            self.p['W7'] = r.normal(0, np.sqrt(1.0 / d), ((K + 1) * d, d)); self.p['b7'] = np.zeros(d)
            self.m = {k: np.zeros_like(v) for k, v in self.p.items()}; self.v = {k: np.zeros_like(v) for k, v in self.p.items()}

    def napp_x(self, H, head, A):
        d = self.d; X = np.zeros((len(head), (K + 1) * d)); X[:, :d] = H[head]; tot = np.zeros((len(head), d))
        for j in range(A.shape[1]):
            sel = A[:, j] >= 0; sl = 1 + min(j, K - 1); a = H[A[sel, j]]
            X[sel, sl * d:(sl + 1) * d] += a; tot[sel] += a
        return X, tot

    def forward(self, b):
        p = self.p; H = np.zeros((b.n, self.d)); cache = []
        for kind, idx, ex in b.groups:
            if kind in (TN, TB): H[idx] = p['Et'][kind]; cache.append(None)
            elif kind == CONST: H[idx] = p['Ec'][ex[0]]; cache.append(None)
            elif kind == VAR:
                pay, bt = ex; raw = p['Ev'][pay] + (H[bt] @ p['P'] if self.mode == 'binder' else 0.0)
                H[idx] = self.clip(raw); cache.append(raw)
            elif kind == NAPP:
                head, A, ar = ex; s, c = napp_consts(ar, self.scale)
                X, tot = self.napp_x(H, head, A); pre = (X @ p['W7']) * 2.0 ** -s + p['b7']
                raw = np.maximum(pre, 0) + ((0.5 * H[head] + tot * 2.0 ** -(c + 1)) if self.res else 0.0)
                H[idx] = self.clip(raw); cache.append((X, pre, raw))
            else:
                c1, c2 = ex; X = np.concatenate([H[c1], H[c2]], axis=1); pre = X @ p['W%d' % kind] + p['b%d' % kind]
                raw = np.maximum(pre, 0) + (0.5 * (H[c1] + H[c2]) if self.res else 0.0)
                H[idx] = self.clip(raw); cache.append((X, pre, raw))
        return H[b.roots] @ p['w'] + p['b0'][0], H, cache

    def grads(self, b):
        p = self.p; out, H, cache = self.forward(b); d = self.d
        err = out - b.y; loss = float(np.mean(err ** 2))
        g = {k: np.zeros_like(v) for k, v in p.items()}
        dy = 2 * err / len(err)
        g['w'] = H[b.roots].T @ dy; g['b0'][0] = dy.sum()
        dH = np.zeros_like(H); np.add.at(dH, b.roots, np.outer(dy, p['w']))
        for (kind, idx, ex), c in zip(reversed(b.groups), reversed(cache)):
            if kind in (TN, TB): g['Et'][kind] += dH[idx].sum(0)
            elif kind == CONST: np.add.at(g['Ec'], ex[0], dH[idx])
            elif kind == VAR:
                pay, bt = ex; dr = dH[idx] * self.inside(c)
                np.add.at(g['Ev'], pay, dr)
                if self.mode == 'binder':
                    g['P'] += H[bt].T @ dr; np.add.at(dH, bt, dr @ p['P'].T)
            elif kind == NAPP:
                head, A, ar = ex; s, cc = napp_consts(ar, self.scale)
                X, pre, raw = c; dr = dH[idx] * self.inside(raw); gp = dr * (pre > 0) * 2.0 ** -s
                g['W7'] += X.T @ gp; g['b7'] += (dr * (pre > 0)).sum(0)
                dX = gp @ p['W7'].T
                dh = dX[:, :d] + (0.5 * dr if self.res else 0.0); np.add.at(dH, head, dh)
                da = dr * 2.0 ** -(cc + 1) if self.res else 0.0
                for j in range(A.shape[1]):
                    sel = A[:, j] >= 0; sl = 1 + min(j, K - 1)
                    np.add.at(dH, A[sel, j], dX[sel, sl * d:(sl + 1) * d] + (da[sel] if self.res else 0.0))
            else:
                c1, c2 = ex; X, pre, raw = c; dr = dH[idx] * self.inside(raw); gp = dr * (pre > 0)
                g['W%d' % kind] += X.T @ gp; g['b%d' % kind] += gp.sum(0)
                dX = gp @ p['W%d' % kind].T
                if self.res: dX = dX + np.concatenate([0.5 * dr, 0.5 * dr], axis=1)
                np.add.at(dH, c1, dX[:, :d]); np.add.at(dH, c2, dX[:, d:])
        return loss, g, out

# ---------------------------------------------------------------- integer model
class GIntEncoder(IntEncoder):
    """`IntEncoder` over a `GBatch`. The n-ary product is one int64 product
    with one rounding; the skip is one rounding of (h_f << c) + sum a_i."""
    def __init__(self, d, mode, seed, lr_shift=7, nary=False, scale='none'):
        ref = GEncoder(d, mode, seed, nary=nary, scale=scale, res=True, clamp=WORD / (1 << F))
        self.d = d; self.mode = mode; self.k = lr_shift; self.nary = nary; self.scale = scale
        self.p = {k: np.round(v * (1 << (F + S))).astype(np.int64) for k, v in ref.p.items()}
        self.m = {k: np.zeros_like(v) for k, v in self.p.items()}
        self.peak = 0

    def napp_x(self, H, head, A):
        d = self.d; X = np.zeros((len(head), (K + 1) * d), dtype=np.int64); X[:, :d] = H[head]
        tot = np.zeros((len(head), d), dtype=np.int64)
        for j in range(A.shape[1]):
            sel = A[:, j] >= 0; sl = 1 + min(j, K - 1); a = H[A[sel, j]]
            X[sel, sl * d:(sl + 1) * d] += a; tot[sel] += a
        return X, tot

    def forward(self, b):
        w = {k: self.fw(k) for k in self.p}; H = np.zeros((b.n, self.d), dtype=np.int64); cache = []
        for kind, idx, ex in b.groups:
            if kind in (TN, TB): H[idx] = w['Et'][kind]; cache.append(None)
            elif kind == CONST: H[idx] = w['Ec'][ex[0]]; cache.append(None)
            elif kind == VAR:
                pay, bt = ex; raw = w['Ev'][pay] + (rshift(imat(H[bt], w['P']), F) if self.mode == 'binder' else 0)
                H[idx] = np.clip(raw, -WORD - 1, WORD); cache.append(raw)
            elif kind == NAPP:
                head, A, ar = ex; s, c = napp_consts(ar, self.scale)
                X, tot = self.napp_x(H, head, A); pre = rshift(imat(X, w['W7']), F + s) + w['b7']
                raw = np.maximum(pre, 0) + rshift((H[head] << c) + tot, c + 1)
                H[idx] = np.clip(raw, -WORD - 1, WORD); cache.append((X, pre, raw))
            else:
                c1, c2 = ex; X = np.concatenate([H[c1], H[c2]], axis=1); pre = rshift(imat(X, w['W%d' % kind]), F) + w['b%d' % kind]
                raw = np.maximum(pre, 0) + rshift(H[c1] + H[c2], 1)
                H[idx] = np.clip(raw, -WORD - 1, WORD); cache.append((X, pre, raw))
        out = rshift(imat(H[b.roots], w['w'][:, None])[:, 0], F) + w['b0'][0]
        return out, H, cache, w

    def grads(self, b):
        out, H, cache, w = self.forward(b)
        y = (b.y * (1 << F)).astype(np.int64); err = out - y
        g = {k: np.zeros_like(v) for k, v in self.p.items()}
        dy = err << (S + 1 - 6)
        g['w'] = imat(H[b.roots].T, dy[:, None])[:, 0]; g['b0'][0] = dy.sum()
        dH = np.zeros_like(H); np.add.at(dH, b.roots, rshift(np.outer(dy, w['w']), F))
        d = self.d; inside = lambda raw: (raw >= -WORD - 1) & (raw <= WORD)
        for (kind, idx, ex), c in zip(reversed(b.groups), reversed(cache)):
            if kind in (TN, TB): g['Et'][kind] += dH[idx].sum(0)
            elif kind == CONST: np.add.at(g['Ec'], ex[0], dH[idx])
            elif kind == VAR:
                pay, bt = ex; dr = dH[idx] * inside(c)
                np.add.at(g['Ev'], pay, dr)
                if self.mode == 'binder':
                    g['P'] += imat(H[bt].T, dr); np.add.at(dH, bt, rshift(imat(dr, w['P'].T), F))
            elif kind == NAPP:
                head, A, ar = ex; s, cc = napp_consts(ar, self.scale); smax = int(s.max())
                X, pre, raw = c; dr = dH[idx] * inside(raw); gp = dr * (pre > 0)
                gw = imat(X.T, gp << (smax - s))
                g['W7'] += rshift(gw, smax) if smax else gw; g['b7'] += gp.sum(0)
                dX = rshift(imat(gp, w['W7'].T), F + s)
                np.add.at(dH, head, dX[:, :d] + rshift(dr, 1))
                da = rshift(dr, cc + 1)
                for j in range(A.shape[1]):
                    sel = A[:, j] >= 0; sl = 1 + min(j, K - 1)
                    np.add.at(dH, A[sel, j], dX[sel, sl * d:(sl + 1) * d] + da[sel])
            else:
                c1, c2 = ex; X, pre, raw = c; dr = dH[idx] * inside(raw); gp = dr * (pre > 0)
                g['W%d' % kind] += imat(X.T, gp); g['b%d' % kind] += gp.sum(0)
                dX = rshift(imat(gp, w['W%d' % kind].T), F) + np.concatenate([rshift(dr, 1), rshift(dr, 1)], axis=1)
                np.add.at(dH, c1, dX[:, :d]); np.add.at(dH, c2, dX[:, d:])
        self.peak = max(self.peak, max(int(np.abs(v).max()) for v in g.values()), int(np.abs(dH).max()))
        return float(np.mean((err / (1 << F)) ** 2)), g

    def step(self, b, halve=0):
        assert len(b.y) == 64
        loss, g = self.grads(b)
        unit = 1 << (F + S - self.k - halve)
        for k in self.p:
            self.p[k] -= unit * np.sign(7 * self.m[k] + g[k])
            self.m[k] = rshift(127 * self.m[k] + g[k], 7)
        return loss

# ---------------------------------------------------------------- data
def toy_items():
    """The exact train/test/deeper items of `stlc_toy`'s main."""
    rng = random.Random(20261123)
    tr, _ = T.make(rng, 20032, 6, (0, 40)); te, _ = T.make(rng, 3008, 6, (0, 40)); de, _ = T.make(rng, 3008, 6, (40, 80))
    return tr, te, de

def wide_items():
    extend_consts(); rng = random.Random(20261124)
    return (make_items(rng, 20032, 6, (0, 40), sample), make_items(rng, 3008, 6, (0, 40), sample),
            make_items(rng, 3008, 6, (40, 80), sample))

def batches(items, share, nary, bs=64):
    return [GBatch(items[i:i + bs], share, nary) for i in range(0, len(items) - len(items) % bs, bs)]

def tbatches(items, bs=64):
    return [Batch([flatten(t) for t, _ in items[i:i + bs]], [y for _, y in items[i:i + bs]])
            for i in range(0, len(items) - len(items) % bs, bs)]

def term_size(t):
    return 1 + (term_size(t[2]) if t[0] == 'lam' else term_size(t[1]) + term_size(t[2]) if t[0] == 'app' else 0)

# ---------------------------------------------------------------- checks
def check():
    """Shared graph against tree: float outputs and gradients, integer
    outputs and gradients, and this file's tree models against `stlc_toy`."""
    tr, te, de = toy_items()
    sets = [('train', tr[:64 * 8]), ('deeper', de[:64 * 8])]
    for name, items in sets:
        tb = tbatches(items); gt = batches(items, False, False); gs = batches(items, True, False)
        fo = fg = 0.0; ftree = 0.0; gmax = 0.0
        for b0, b1, b2 in zip(tb, gt, gs):
            ref = Encoder(64, 'binder', 1, res=True, clamp=8.0); m = GEncoder(64, 'binder', 1, res=True, clamp=8.0)
            l0, g0, o0 = ref.grads(b0); l1, g1, o1 = m.grads(b1); l2, g2, o2 = m.grads(b2)
            ftree = max(ftree, np.abs(o1 - o0).max(), *(np.abs(g1[k] - g0[k]).max() for k in g0))
            fo = max(fo, np.abs(o2 - o0).max() / np.abs(o0).max())
            for k in g0:
                gmax = max(gmax, np.abs(g2[k] - g0[k]).max() / max(np.abs(g0[k]).max(), 1e-300))
        print('[%s] float: GEncoder tree vs stlc_toy largest abs diff %.1e; shared vs tree: outputs rel %.1e, gradients rel (per tensor, max-normalised) %.1e'
              % (name, ftree, fo, gmax))
        # integer
        same_tree = True; out_eq = True; gd = []; signdiff = []; tot = 0; diffent = 0
        for b0, b1, b2 in zip(tb, gt, gs):
            ref = IntEncoder(64, 'binder', 1, lr_shift=12); m1 = GIntEncoder(64, 'binder', 1, lr_shift=12)
            m2 = GIntEncoder(64, 'binder', 1, lr_shift=12)
            o0 = ref.forward(b0)[0]; o1 = m1.forward(b1)[0]; o2 = m2.forward(b2)[0]
            out_eq &= bool(np.array_equal(o0, o2))
            ref.step(b0); m1.step(b1)
            same_tree &= all(np.array_equal(ref.p[k], m1.p[k]) for k in ref.p)
            _, ga = GIntEncoder(64, 'binder', 1).grads(b1); _, gb = GIntEncoder(64, 'binder', 1).grads(b2)
            for k in ga:
                dd = np.abs(ga[k] - gb[k]); gd.append(dd.max() / max(np.abs(ga[k]).max(), 1))
                tot += ga[k].size; diffent += int((dd > 0).sum())
                signdiff.append(int((np.sign(ga[k]) != np.sign(gb[k])).sum()))
            maxunits = max(int(np.abs(ga[k] - gb[k]).max()) for k in ga)
        print('[%s] int: GIntEncoder tree step == stlc_toy IntEncoder step: %s; shared forward bit-identical to tree: %s'
              % (name, same_tree, out_eq))
        print('[%s] int gradients shared vs tree: %d of %d entries differ, largest diff %.1e of the tensor max, %d sign flips; largest diff in units of 2^-24 in last batch %d'
              % (name, diffent, tot, max(gd), sum(signdiff), maxunits))
    # n-ary model: finite-difference gradient check and tree/shared agreement
    extend_consts()
    rng = random.Random(5); items = [sample(rng, 4, 6) for _ in range(8)]
    for scale in ('none', 'sqrt'):
        b = GBatch(items, False, True); m = GEncoder(6, 'binder', 1, nary=True, scale=scale, res=True)
        _, g, _ = m.grads(b); worst = 0.0
        for k in m.p:
            flat = m.p[k].reshape(-1); gf = g[k].reshape(-1)
            for j in range(0, flat.size, max(1, flat.size // 7)):
                old = flat[j]; flat[j] = old + 1e-6; lp = m.grads(b)[0]; flat[j] = old - 1e-6; lm = m.grads(b)[0]; flat[j] = old
                num = (lp - lm) / 2e-6
                if abs(num) + abs(gf[j]) > 1e-7: worst = max(worst, abs(num - gf[j]) / (abs(num) + abs(gf[j])))
        print('n-ary gradient check (scale %s): worst relative error %.1e' % (scale, worst))
    _, te, de = wide_items()
    for share in (False, True):
        b = GBatch(te[:64], share, True)
        im = GIntEncoder(16, 'binder', 5, nary=True); fm = GEncoder(16, 'binder', 5, nary=True, res=True, clamp=WORD / (1 << F))
        fm.p = {k: im.fw(k) / (1 << F) for k in im.p}
        oi = im.forward(b)[0] / (1 << F); of = fm.forward(b)[0]
        print('n-ary integer forward vs float, same weights (share=%s): largest difference %.4f of %.2f' % (share, np.abs(oi - of).max(), np.abs(of).max()))
    bt, bs = GBatch(te[:64], False, True), GBatch(te[:64], True, True)
    m = GIntEncoder(64, 'binder', 1, nary=True)
    print('n-ary int shared forward bit-identical to tree:', bool(np.array_equal(m.forward(bt)[0], m.forward(bs)[0])))
    mf = GEncoder(64, 'binder', 1, nary=True, res=True, clamp=8.0); a, b_ = mf.grads(bt), mf.grads(bs)
    print('n-ary float shared vs tree: outputs %.1e, gradients %.1e (max abs)' % (np.abs(a[2] - b_[2]).max(), max(np.abs(a[1][k] - b_[1][k]).max() for k in a[1])))

# ---------------------------------------------------------------- sharing numbers and timing
def share_stats(items, nary, label):
    bs = 64; nb = len(items) // bs
    agg = {m: {'nodes': 0, 'cells': 0, 'types': 0, 'vars': 0} for m in ('tree', 'per-term', 'batch', 'batch-nocond')}
    for i in range(nb):
        chunk = items[i * bs:(i + 1) * bs]
        for mode, gs in (('tree', [Graph(False, nary)]), ('batch', [Graph(True, nary)]), ('batch-nocond', [Graph(True, nary, cond=False)])):
            for t, _ in chunk: gs[0].term(t)
            for k, v in counts(gs[0]).items(): agg[mode][k] += v
        for t, _ in chunk:
            g = Graph(True, nary); g.term(t)
            for k, v in counts(g).items(): agg['per-term'][k] += v
    print('%s, mean per batch of 64 (%d batches):' % (label, nb))
    for mode, v in agg.items():
        print('   %-13s nodes %8.1f  cells %8.1f (of which arrow %6.1f)  var projections %7.1f' % (mode, v['nodes'] / nb, v['cells'] / nb, v['types'] / nb, v['vars'] / nb))
    pool = {}
    for mode, g in (('tree', Graph(False, nary)), ('pool', Graph(True, nary)), ('pool-nocond', Graph(True, nary, cond=False))):
        for t, _ in items: g.term(t)
        pool[mode] = counts(g)
    print('   all %d terms as one pool:' % len(items))
    for mode, v in pool.items(): print('   %-13s nodes %9d  cells %9d (of which arrow %6d)  var projections %8d' % (mode, v['nodes'], v['cells'], v['types'], v['vars']))

def timing(items, nary, reps=40):
    tb = batches(items[:64 * reps], False, nary); t0 = time.time(); sb = batches(items[:64 * reps], True, nary)
    build_s = (time.time() - t0) / reps; t0 = time.time(); batches(items[:64 * reps], False, nary); build_t = (time.time() - t0) / reps
    res = {}
    for name, bl in (('tree', tb), ('shared', sb)):
        for kind in ('float', 'int'):
            m = GEncoder(64, 'binder', 1, nary=nary, res=True, clamp=8.0) if kind == 'float' else GIntEncoder(64, 'binder', 1, lr_shift=12, nary=nary)
            m.step(bl[0]); t0 = time.time()
            for b in bl: m.step(b)
            res[(name, kind)] = (time.time() - t0) / len(bl)
    print('   time per training step (ms): float tree %.1f shared %.1f | int tree %.1f shared %.1f | graph build per batch tree %.1f shared %.1f'
          % tuple(1000 * x for x in (res[('tree', 'float')], res[('shared', 'float')], res[('tree', 'int')], res[('shared', 'int')], build_t, build_s)))
    print('   mean levels per batch: %.1f' % np.mean([b.depth + 1 for b in tb]))

# ---------------------------------------------------------------- training
DATA = {}
def run(cfg):
    name, kind, d, seed, kw, epochs, key = cfg
    train, test, deep = DATA[key]
    t0 = time.time(); order = list(range(len(train))); r = random.Random(seed); tot = 0.0
    m = GIntEncoder(d, 'binder', seed, **kw) if kind == 'int' else GEncoder(d, 'binder', seed, **kw)
    for ep in range(epochs):
        r.shuffle(order); tot = 0.0
        for i in order:
            if kind == 'int': tot += m.step(train[i], halvings(ep, epochs))
            else: tot += m.step(train[i], 1 - 0.95 * ep / epochs)
    peak = (' peak 2^%.0f' % np.log2(max(m.peak, 1))) if kind == 'int' else ''
    npar = sum(v.size for v in m.p.values())
    return name, seed, tot / len(order), accuracy(m, test), accuracy(m, deep), (time.time() - t0) / (epochs * len(order)), peak, npar

def table(res):
    by = {}
    for name, seed, loss, a, ad, t, peak, npar in res: by.setdefault(name, []).append((seed, a, ad, loss, t, peak, npar))
    print('%-28s %-30s %7s %-30s %7s %8s %9s %s' % ('variant', 'test acc by seed', 'mean', 'deeper by seed', 'mean', 'params', 'ms/step', 'final loss by seed'))
    for name, rs in by.items():
        print('%-28s %-30s %6.1f%% %-30s %6.1f%% %8d %9.1f %s%s' % (name, ' '.join('%.1f' % (100 * x[1]) for x in rs), 100 * np.mean([x[1] for x in rs]),
              ' '.join('%.1f' % (100 * x[2]) for x in rs), 100 * np.mean([x[2] for x in rs]), rs[0][6], 1000 * np.mean([x[4] for x in rs]),
              ' '.join('%.3f' % x[3] for x in rs), rs[0][5]))
    sys.stdout.flush()

def describe(tr, te, de):
    for nm, it in (('train', tr), ('test', te), ('deeper', de)):
        sz = [term_size(t) for t, _ in it]
        print('%-6s %5d terms, size median %d p90 %d max %d' % (nm, len(it), np.median(sz), np.percentile(sz, 90), max(sz)))
    for nm, it in (('test', te), ('deeper', de)):
        for nary in (False, True):
            bl = batches(it, False, nary); ng = [len(b.groups) for b in bl]; lv = [b.depth + 1 for b in bl]
            cells = np.mean([b.counts['cells'] for b in bl])
            print('%-6s %-6s levels per batch mean %.1f max %d | groups (sequential matmul steps) mean %.1f | cells per batch %.0f | nodes %.0f'
                  % (nm, 'n-ary' if nary else 'binary', np.mean(lv), max(lv), np.mean(ng), cells, np.mean([b.n for b in bl])))
    ar = {}
    def walk(t):
        if t[0] == 'lam': walk(t[2]); return
        if t[0] == 'app':
            n = 0
            while t[0] == 'app': walk(t[2]); t = t[1]; n += 1
            ar[n] = ar.get(n, 0) + 1; walk(t)
    for t, _ in tr: walk(t)
    print('application arity histogram (train):', dict(sorted(ar.items())))

def train_main(which):
    sys.setrecursionlimit(100000)
    tr, te, de = toy_items() if which.startswith('toy') else wide_items()
    if which in ('data',):
        describe(tr, te, de); share_stats(tr, False, 'wide data, binary'); share_stats(tr, True, 'wide data, n-ary'); return
    for nary in (False, True):
        DATA['nary' if nary else 'bin'] = (batches(tr, False, nary), batches(te, False, nary), batches(de, False, nary))
    seeds = tuple(int(x) for x in os.environ.get('SEEDS', '1,2,3,4').split(',')); cfgs = []; base = dict(res=True, clamp=8.0)
    if which == 'float':
        cfgs += [('binary', 'float', 64, s, base, 12, 'bin') for s in seeds]
        cfgs += [('n-ary', 'float', 64, s, dict(base, nary=True), 12, 'nary') for s in seeds]
        cfgs += [('n-ary sqrt-scaled', 'float', 64, s, dict(base, nary=True, scale='sqrt'), 12, 'nary') for s in seeds]
    elif which == 'ctrl':
        cfgs += [('binary d=76 24ep', 'float', 76, s, base, 24, 'bin') for s in seeds]
    elif which == 'toy':
        cfgs += [('toy binary', 'float', 64, s, base, 12, 'bin') for s in seeds]
        cfgs += [('toy n-ary', 'float', 64, s, dict(base, nary=True), 12, 'nary') for s in seeds]
    elif which == 'int':
        cfgs += [('int binary', 'int', 64, s, dict(lr_shift=12), 24, 'bin') for s in seeds]
        cfgs += [('int n-ary sqrt', 'int', 64, s, dict(lr_shift=12, nary=True, scale='sqrt'), 24, 'nary') for s in seeds]
    elif which == 'float24':
        cfgs += [('binary 24ep', 'float', 64, s, base, 24, 'bin') for s in seeds]
        cfgs += [('n-ary sqrt 24ep', 'float', 64, s, dict(base, nary=True, scale='sqrt'), 24, 'nary') for s in seeds]
    with __import__('multiprocessing').get_context('fork').Pool(10) as pool:
        res = []
        for r in pool.imap_unordered(run, cfgs):
            res.append(r); print('done', r[0], 'seed', r[1], '%.3f %.3f %.0fs' % (r[3], r[4], r[5] * 313 * 12), flush=True)
    res.sort(key=lambda r: ([c[0] for c in cfgs].index(r[0]), r[1]))
    table(res)

def sharetrain():
    """Training on shared graphs against trees, original toy data."""
    sys.setrecursionlimit(100000)
    tr, te, de = toy_items()
    DATA['tree'] = (batches(tr, False, False), batches(te, False, False), batches(de, False, False))
    DATA['shared'] = (batches(tr, True, False), batches(te, True, False), batches(de, True, False))
    cfgs = [('int tree', 'int', 64, s, dict(lr_shift=12), 24, 'tree') for s in (1, 2, 3, 4)]
    cfgs += [('int shared', 'int', 64, s, dict(lr_shift=12), 24, 'shared') for s in (1, 2, 3, 4)]
    with __import__('multiprocessing').get_context('fork').Pool(8) as pool:
        res = pool.map(run, cfgs, chunksize=1)
    table(res)

if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    which = sys.argv[1] if len(sys.argv) > 1 else 'check'
    if which == 'check': check()
    elif which == 'share':
        tr, _, _ = toy_items(); share_stats(tr, False, 'toy data (stlc_toy train set)'); timing(tr, False)
    elif which == 'sharetrain': sharetrain()
    else: train_main(which)
