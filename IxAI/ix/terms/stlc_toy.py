"""Structural test of a recursive term encoder on a task with exact labels:
does a closed simply typed lambda term typecheck?

A term is a tree over seven node kinds (two base types, arrow, constant,
bound variable by de Bruijn index, lambda with its annotation, application).
The five context variables are bound by five outer lambdas, so the question is
a property of a closed term. Half the terms are mutated until they stop
typechecking. Labels come from `infer`.

Encoders compared, all with the same cell `h = relu([h1; h2] W_kind + b_kind)`:
  bag      counts of node kinds, variables and constants (no structure)
  index    bottom-up; a variable is its index embedding (cacheable per subterm)
  binder   bottom-up; a variable also receives its binder's annotation vector
"""
import numpy as np, random, sys, time

# ---------------------------------------------------------------- terms
N, B = 'N', 'B'
def arrow(a, b): return ('->', a, b)
CONSTS = [('zero', N), ('succ', arrow(N, N)), ('tt', B), ('ff', B), ('not', arrow(B, B)),
          ('iszero', arrow(N, B)), ('add', arrow(N, arrow(N, N))), ('ite', arrow(B, arrow(N, arrow(N, N))))]
CTYPE = dict(CONSTS); CID = {n: i for i, (n, _) in enumerate(CONSTS)}

def rand_type(rng, depth):
    r = rng.random()
    if depth == 0 or r < 0.65:
        return N if rng.random() < 0.55 else B
    return arrow(rand_type(rng, depth - 1), rand_type(rng, depth - 1))

def result_chain(t):
    """[(argument types, result)] for every way of applying a value of type t."""
    out = [([], t)]; args = []
    while isinstance(t, tuple):
        args = args + [t[1]]; t = t[2]; out.append((list(args), t))
    return out

def gen(rng, ctx, T, depth):
    """A term of type T under ctx (innermost binder first). While `rng.chain`
    lasts, base-type positions are wrapped in type-changing unary steps that
    add depth without spending `depth`."""
    if not isinstance(T, tuple) and getattr(rng, 'chain', 0) > 0 and rng.random() < 0.5:
        rng.chain -= 1; c = rng.random()
        if T == N:
            if c < 0.5: return ('app', ('const', 'succ'), gen(rng, ctx, N, depth))
            if c < 0.75: return ('app', ('app', ('const', 'add'), gen(rng, ctx, N, depth)), gen(rng, ctx, N, 0))
            return ('app', ('app', ('app', ('const', 'ite'), gen(rng, ctx, B, depth)), gen(rng, ctx, N, 0)), gen(rng, ctx, N, 0))
        if c < 0.5: return ('app', ('const', 'not'), gen(rng, ctx, B, depth))
        return ('app', ('const', 'iszero'), gen(rng, ctx, N, depth))
    heads = []
    for i, A in enumerate(ctx):
        for args, res in result_chain(A):
            if res == T: heads.append((('var', i), args))
    for name, A in CONSTS:
        for args, res in result_chain(A):
            if res == T: heads.append((('const', name), args))
    flat = [h for h in heads if not h[1]]
    if depth <= 0:
        if flat: return rng.choice(flat)[0]
        if isinstance(T, tuple): return ('lam', T[1], gen(rng, [T[1]] + ctx, T[2], 0))
        return ('const', 'zero' if T == N else 'tt')
    r = rng.random()
    if isinstance(T, tuple) and r < 0.5:
        return ('lam', T[1], gen(rng, [T[1]] + ctx, T[2], depth - 1))
    applied = [h for h in heads if h[1]]
    if r < 0.12 and flat: return rng.choice(flat)[0]
    if r < 0.75 and applied:
        head, args = rng.choice(applied)
        t = head
        for A in args: t = ('app', t, gen(rng, ctx, A, depth - 1))
        return t
    A = rand_type(rng, 1)
    return ('app', gen(rng, ctx, arrow(A, T), depth - 1), gen(rng, ctx, A, depth - 1))

def infer(ctx, t):
    k = t[0]
    if k == 'var': return ctx[t[1]] if t[1] < len(ctx) else None
    if k == 'const': return CTYPE[t[1]]
    if k == 'lam':
        b = infer([t[1]] + ctx, t[2]); return None if b is None else arrow(t[1], b)
    f = infer(ctx, t[1]); a = infer(ctx, t[2])
    if f is None or a is None or not isinstance(f, tuple) or f[1] != a: return None
    return f[2]

def positions(t, binders=0, path=()):
    yield path, t, binders
    if t[0] == 'lam': yield from positions(t[2], binders + 1, path + (2,))
    elif t[0] == 'app':
        yield from positions(t[1], binders, path + (1,)); yield from positions(t[2], binders, path + (2,))

def replace(t, path, new):
    if not path: return new
    l = list(t); l[path[0]] = replace(t[path[0]], path[1:], new); return tuple(l)

def mutate(rng, t):
    ps = list(positions(t)); path, sub, binders = rng.choice(ps)
    if sub[0] == 'var' and binders > 1:
        return replace(t, path, ('var', rng.choice([i for i in range(binders) if i != sub[1]])))
    if sub[0] == 'lam':
        A = rand_type(rng, 1)
        return replace(t, path, ('lam', A, sub[2])) if A != sub[1] else t
    if sub[0] == 'const':
        return replace(t, path, ('const', rng.choice([n for n, _ in CONSTS if n != sub[1]])))
    return replace(t, path, gen(rng, [N] * binders, rand_type(rng, 1), 1)) if rng.random() < 0.3 else t

def sample(rng, depth, chain=0):
    ctx = [rand_type(rng, 1) for _ in range(5)]
    rng.chain = chain
    body = gen(rng, ctx, rand_type(rng, 1), depth)
    t = body
    for A in ctx: t = ('lam', A, t)
    if rng.random() < 0.5:
        for _ in range(6):
            t = mutate(rng, t)
            if infer([], t) is None: break
    return t, int(infer([], t) is not None)

# ---------------------------------------------------------------- graphs
TN, TB, ARR, CONST, VAR, LAM, APP = range(7)
def flatten(t):
    """Nodes as (kind, c1, c2, payload, binder annotation node, level), root last."""
    nodes = []
    def ty(T):
        if T == N: nodes.append((TN, -1, -1, 0, -1, 0))
        elif T == B: nodes.append((TB, -1, -1, 0, -1, 0))
        else:
            a = ty(T[1]); b = ty(T[2]); nodes.append((ARR, a, b, 0, -1, 1 + max(nodes[a][5], nodes[b][5])))
        return len(nodes) - 1
    def go(t, env):
        k = t[0]
        if k == 'var':
            bt = env[t[1]] if t[1] < len(env) else -1
            nodes.append((VAR, -1, -1, min(t[1], 31), bt, 1 + (nodes[bt][5] if bt >= 0 else 0)))
        elif k == 'const': nodes.append((CONST, -1, -1, CID[t[1]], -1, 0))
        elif k == 'lam':
            a = ty(t[1]); b = go(t[2], [a] + env); nodes.append((LAM, a, b, 0, -1, 1 + max(nodes[a][5], nodes[b][5])))
        else:
            f = go(t[1], env); a = go(t[2], env); nodes.append((APP, f, a, 0, -1, 1 + max(nodes[f][5], nodes[a][5])))
        return len(nodes) - 1
    go(t, [])
    return np.array(nodes, dtype=np.int64)

class Batch:
    def __init__(self, graphs, labels):
        offs = np.cumsum([0] + [len(g) for g in graphs])
        alln = np.concatenate(graphs)
        shift = np.repeat(offs[:-1], [len(g) for g in graphs])
        for col in (1, 2, 4):
            m = alln[:, col] >= 0; alln[m, col] += shift[m]
        self.n = len(alln); self.roots = offs[1:] - 1
        self.y = np.where(np.array(labels) == 1, 1.0, -1.0)
        self.groups = []
        for lv in range(int(alln[:, 5].max()) + 1):
            for kind in range(7):
                idx = np.nonzero((alln[:, 5] == lv) & (alln[:, 0] == kind))[0]
                if idx.size: self.groups.append((kind, idx, alln[idx, 1], alln[idx, 2], alln[idx, 3], alln[idx, 4]))
        self.depth = int(alln[:, 5].max())

# ---------------------------------------------------------------- model
CELLS = (ARR, LAM, APP)

class Encoder:
    """Float reference. Options: `res` adds the mean of the two children to the
    cell's output; `clamp` bounds every vector entry (the fixed-point word
    range); `opt` is 'adam' or 'sgdm' (momentum 7/8, the form shifts can do)."""
    def __init__(self, d, mode, seed, res=False, clamp=None, opt='adam', lr=2e-3, clipg=None):
        r = np.random.default_rng(seed); self.d = d; self.mode = mode
        self.res = res; self.clamp = clamp; self.opt = opt; self.lr = lr; self.clipg = clipg
        s = 1.0 / np.sqrt(d)
        self.p = {'Et': r.normal(0, s, (2, d)), 'Ec': r.normal(0, s, (len(CONSTS), d)), 'Ev': r.normal(0, s, (32, d)),
                  'P': r.normal(0, s, (d, d)), 'w': r.normal(0, s, d), 'b0': np.zeros(1)}
        for k in CELLS:
            self.p['W%d' % k] = r.normal(0, np.sqrt(1.0 / d), (2 * d, d)); self.p['b%d' % k] = np.zeros(d)
        self.m = {k: np.zeros_like(v) for k, v in self.p.items()}; self.v = {k: np.zeros_like(v) for k, v in self.p.items()}
        self.t = 0

    def clip(self, x):
        return x if self.clamp is None else np.clip(x, -self.clamp, self.clamp)

    def forward(self, b):
        p = self.p; H = np.zeros((b.n, self.d)); cache = []
        for kind, idx, c1, c2, pay, bt in b.groups:
            if kind in (TN, TB): H[idx] = p['Et'][kind]; cache.append(None)
            elif kind == CONST: H[idx] = p['Ec'][pay]; cache.append(None)
            elif kind == VAR:
                raw = p['Ev'][pay] + (H[bt] @ p['P'] if self.mode == 'binder' else 0.0)
                H[idx] = self.clip(raw); cache.append(raw)
            else:
                X = np.concatenate([H[c1], H[c2]], axis=1); pre = X @ p['W%d' % kind] + p['b%d' % kind]
                raw = np.maximum(pre, 0) + (0.5 * (H[c1] + H[c2]) if self.res else 0.0)
                H[idx] = self.clip(raw); cache.append((X, pre, raw))
        out = H[b.roots] @ p['w'] + p['b0'][0]
        return out, H, cache

    def inside(self, raw):
        return 1.0 if self.clamp is None else (np.abs(raw) < self.clamp)

    def grads(self, b):
        p = self.p; out, H, cache = self.forward(b)
        err = out - b.y; loss = float(np.mean(err ** 2))
        g = {k: np.zeros_like(v) for k, v in p.items()}
        dy = 2 * err / len(err)
        g['w'] = H[b.roots].T @ dy; g['b0'][0] = dy.sum()
        dH = np.zeros_like(H); dH[b.roots] = np.outer(dy, p['w'])
        d = self.d
        for (kind, idx, c1, c2, pay, bt), c in zip(reversed(b.groups), reversed(cache)):
            if kind in (TN, TB): g['Et'][kind] += dH[idx].sum(0)
            elif kind == CONST: np.add.at(g['Ec'], pay, dH[idx])
            elif kind == VAR:
                dr = dH[idx] * self.inside(c)
                np.add.at(g['Ev'], pay, dr)
                if self.mode == 'binder':
                    g['P'] += H[bt].T @ dr; np.add.at(dH, bt, dr @ p['P'].T)
            else:
                X, pre, raw = c; dr = dH[idx] * self.inside(raw); gp = dr * (pre > 0)
                g['W%d' % kind] += X.T @ gp; g['b%d' % kind] += gp.sum(0)
                dX = gp @ p['W%d' % kind].T
                if self.res: dX = dX + np.concatenate([0.5 * dr, 0.5 * dr], axis=1)
                np.add.at(dH, c1, dX[:, :d]); np.add.at(dH, c2, dX[:, d:])
        return loss, g, out

    def step(self, b, lr_scale=1.0):
        loss, g, out = self.grads(b); lr = self.lr * lr_scale
        self.t += 1
        for k in self.p:
            if self.opt == 'adam':
                self.m[k] = 0.9 * self.m[k] + 0.1 * g[k]; self.v[k] = 0.999 * self.v[k] + 0.001 * g[k] ** 2
                mh = self.m[k] / (1 - 0.9 ** self.t); vh = self.v[k] / (1 - 0.999 ** self.t)
                self.p[k] -= lr * mh / (np.sqrt(vh) + 1e-8)
            elif self.opt == 'lion':
                # sign of an interpolated momentum: every weight moves by exactly lr
                self.p[k] -= lr * np.sign(0.875 * self.m[k] + 0.125 * g[k])
                self.m[k] = 0.9921875 * self.m[k] + 0.0078125 * g[k]
            else:
                gk = g[k] if self.clipg is None else np.clip(g[k], -self.clipg, self.clipg)
                self.m[k] = 0.875 * self.m[k] + gk; self.p[k] -= lr * self.m[k]
        return loss


F = 12                       # fractional bits of values and of the weights the forward pass uses
S = 12                       # extra fractional bits of the stored weights and of gradients
WORD = (1 << 15) - 1         # 16-bit signed words

def rshift(x, k):
    """Divide by 2^k, rounding to nearest (ties up)."""
    return (x + (1 << (k - 1))) >> k

def imat(A, B):
    """Exact int64 matrix product. A product whose every partial sum stays
    below 2^52 is exact in float64; otherwise B is split into 16-bit limbs."""
    ma = int(np.abs(A).max()) if A.size else 0; mb = int(np.abs(B).max()) if B.size else 0
    if ma * mb * max(A.shape[-1], 1) < (1 << 52):
        return np.rint(A.astype(np.float64) @ B.astype(np.float64)).astype(np.int64)
    if mb >= ma:
        return imat(A, B & 0xFFFF) + (imat(A, B >> 16) << 16)
    return imat(A & 0xFFFF, B) + (imat(A >> 16, B) << 16)

def halvings(ep, epochs):
    """Step schedule of the learning rate: halved at 50, 70, 85 and 95% of the run."""
    return sum(ep >= f * epochs for f in (0.5, 0.7, 0.85, 0.95))

class IntEncoder:
    """The `res` + clamp model in exact integers: 16-bit forward words with 12
    fractional bits, stored weights and gradients with 24, sums exact in
    int64 and one rounding per dot product. The update moves every weight by
    exactly 2^-lr_shift in the direction of the sign of an interpolated
    momentum. Batches must hold 64 terms."""
    def __init__(self, d, mode, seed, lr_shift=7):
        ref = Encoder(d, mode, seed, res=True, clamp=WORD / (1 << F))
        self.d = d; self.mode = mode; self.k = lr_shift
        self.p = {k: np.round(v * (1 << (F + S))).astype(np.int64) for k, v in ref.p.items()}
        self.m = {k: np.zeros_like(v) for k, v in self.p.items()}
        self.peak = 0

    def fw(self, k):
        return np.clip(rshift(self.p[k], S), -WORD - 1, WORD)

    def forward(self, b):
        w = {k: self.fw(k) for k in self.p}; H = np.zeros((b.n, self.d), dtype=np.int64); cache = []
        for kind, idx, c1, c2, pay, bt in b.groups:
            if kind in (TN, TB): H[idx] = w['Et'][kind]; cache.append(None)
            elif kind == CONST: H[idx] = w['Ec'][pay]; cache.append(None)
            elif kind == VAR:
                raw = w['Ev'][pay] + (rshift(imat(H[bt], w['P']), F) if self.mode == 'binder' else 0)
                H[idx] = np.clip(raw, -WORD - 1, WORD); cache.append(raw)
            else:
                X = np.concatenate([H[c1], H[c2]], axis=1); pre = rshift(imat(X, w['W%d' % kind]), F) + w['b%d' % kind]
                raw = np.maximum(pre, 0) + rshift(H[c1] + H[c2], 1)
                H[idx] = np.clip(raw, -WORD - 1, WORD); cache.append((X, pre, raw))
        out = rshift(imat(H[b.roots], w['w'][:, None])[:, 0], F) + w['b0'][0]
        return out, H, cache, w

    def step(self, b, halve=0):
        assert len(b.y) == 64
        out, H, cache, w = self.forward(b)
        y = (b.y * (1 << F)).astype(np.int64); err = out - y
        g = {k: np.zeros_like(v) for k, v in self.p.items()}
        dy = err << (S + 1 - 6)                                  # 2 err / 64 with F + S fractional bits
        g['w'] = imat(H[b.roots].T, dy[:, None])[:, 0]; g['b0'][0] = dy.sum()
        dH = np.zeros_like(H); dH[b.roots] = rshift(np.outer(dy, w['w']), F)
        d = self.d; inside = lambda raw: (raw >= -WORD - 1) & (raw <= WORD)
        for (kind, idx, c1, c2, pay, bt), c in zip(reversed(b.groups), reversed(cache)):
            if kind in (TN, TB): g['Et'][kind] += dH[idx].sum(0)
            elif kind == CONST: np.add.at(g['Ec'], pay, dH[idx])
            elif kind == VAR:
                dr = dH[idx] * inside(c)
                np.add.at(g['Ev'], pay, dr)
                if self.mode == 'binder':
                    g['P'] += imat(H[bt].T, dr); np.add.at(dH, bt, rshift(imat(dr, w['P'].T), F))
            else:
                X, pre, raw = c; dr = dH[idx] * inside(raw); gp = dr * (pre > 0)
                g['W%d' % kind] += imat(X.T, gp); g['b%d' % kind] += gp.sum(0)
                dX = rshift(imat(gp, w['W%d' % kind].T), F) + np.concatenate([rshift(dr, 1), rshift(dr, 1)], axis=1)
                np.add.at(dH, c1, dX[:, :d]); np.add.at(dH, c2, dX[:, d:])
        unit = 1 << (F + S - self.k - halve)
        for k in self.p:
            self.peak = max(self.peak, int(np.abs(g[k]).max()), int(np.abs(dH).max()))
            self.p[k] -= unit * np.sign(7 * self.m[k] + g[k])
            self.m[k] = rshift(127 * self.m[k] + g[k], 7)
        return float(np.mean((err / (1 << F)) ** 2))

def accuracy(model, batches):
    ok = n = 0
    for b in batches:
        out = model.forward(b)[0]; ok += int(((out > 0) == (b.y > 0)).sum()); n += len(b.y)
    return ok / n

def gradcheck():
    rng = random.Random(3); items = [sample(rng, 3) for _ in range(6)]
    b = Batch([flatten(t) for t, _ in items], [y for _, y in items])
    for mode in ('index', 'binder'):
        for res in (False, True):
            m = Encoder(6, mode, 1, res=res); _, g, _ = m.grads(b); worst = 0.0
            for k in m.p:
                flat = m.p[k].reshape(-1); gf = g[k].reshape(-1)
                for j in range(0, flat.size, max(1, flat.size // 5)):
                    old = flat[j]; flat[j] = old + 1e-5; lp = m.grads(b)[0]; flat[j] = old - 1e-5; lm = m.grads(b)[0]; flat[j] = old
                    num = (lp - lm) / 2e-5
                    if abs(num) + abs(gf[j]) > 1e-7: worst = max(worst, abs(num - gf[j]) / (abs(num) + abs(gf[j])))
            print('gradient check', mode, 'res' if res else 'plain', 'worst relative error %.1e' % worst)

def intcheck(batch):
    """The integer model against the float one on the same weights."""
    for mode in ('index', 'binder'):
        im = IntEncoder(16, mode, 5); fm = Encoder(16, mode, 5, res=True, clamp=WORD / (1 << F))
        fm.p = {k: im.fw(k) / (1 << F) for k in im.p}
        oi = im.forward(batch)[0] / (1 << F); of = fm.forward(batch)[0]
        print('integer forward against float on the same weights (%s): largest difference %.4f of %.2f' % (mode, np.abs(oi - of).max(), np.abs(of).max()))

def bag_features(t):
    f = np.zeros(7 + 32 + len(CONSTS))
    for k, _, _, pay, _, _ in flatten(t):
        f[k] += 1
        if k == VAR: f[7 + pay] += 1
        if k == CONST: f[39 + pay] += 1
    return f

def make(rng, n, depth, chain=(0, 0), bs=64):
    """n terms, half typechecking, generation depth uniform in [3, depth] and
    chain budget uniform in the range `chain`."""
    items = []; need = {0: n // 2, 1: n - n // 2}
    while need[0] + need[1] > 0:
        t, y = sample(rng, rng.randint(3, depth), rng.randint(*chain))
        if need[y] > 0: items.append((t, y)); need[y] -= 1
    rng.shuffle(items)
    graphs = [flatten(t) for t, _ in items]; labels = [y for _, y in items]
    batches = [Batch(graphs[i:i + bs], labels[i:i + bs]) for i in range(0, n - n % bs, bs)]
    return items, batches

DATA = {}
def run(cfg):
    name, kind, d, mode, seed, kw, epochs = cfg
    train, test, deep = DATA['train'], DATA['test'], DATA['deep']
    t0 = time.time(); order = list(range(len(train))); r = random.Random(seed); tot = 0.0
    m = IntEncoder(d, mode, seed, **kw) if kind == 'int' else Encoder(d, mode, seed, **kw)
    for ep in range(epochs):
        r.shuffle(order); tot = 0.0
        for i in order:
            if kind == 'int': tot += m.step(train[i], halvings(ep, epochs))
            elif m.opt == 'lion': tot += m.step(train[i], 0.5 ** halvings(ep, epochs))
            else: tot += m.step(train[i], 1 - 0.95 * ep / epochs)
    peak = (' peak 2^%.0f' % np.log2(max(m.peak, 1))) if kind == 'int' else ''
    return name, d, mode, seed, tot / len(order), accuracy(m, test), accuracy(m, deep), time.time() - t0, peak

if __name__ == '__main__':
    import multiprocessing as mp, os
    sys.setrecursionlimit(100000)
    gradcheck()
    rng = random.Random(20261123)
    DATA['items'], DATA['train'] = make(rng, 20032, 6, (0, 40))
    _, DATA['test'] = make(rng, 3008, 6, (0, 40))
    _, DATA['deep'] = make(rng, 3008, 6, (40, 80))
    intcheck(DATA['test'][0])
    print('train %d terms, tree levels up to %d (test %d, deeper set %d)' % (len(DATA['items']), max(b.depth for b in DATA['train']),
          max(b.depth for b in DATA['test']), max(b.depth for b in DATA['deep'])))
    which = sys.argv[1] if len(sys.argv) > 1 else 'float'
    seeds = (1, 2, 3, 4)
    cfgs = []
    if which == 'float':
        for d in (32, 64):
            for name, kw in (('plain adam', {}), ('res adam', {'res': True}), ('res clamp adam', {'res': True, 'clamp': 8.0}),
                             ('res clamp sgdm 1/128', {'res': True, 'clamp': 8.0, 'opt': 'sgdm', 'lr': 1 / 128}),
                             ('res clamp sgdm 1/512', {'res': True, 'clamp': 8.0, 'opt': 'sgdm', 'lr': 1 / 512})):
                cfgs += [(name, 'float', d, 'binder', s, kw, 12) for s in seeds]
        cfgs += [('res clamp adam', 'float', 64, 'index', s, {'res': True, 'clamp': 8.0}, 12) for s in seeds]
    elif which == 'opt':
        base = {'res': True, 'clamp': 8.0}
        for name, kw in (('sgdm 1/256', {'opt': 'sgdm', 'lr': 1 / 256}), ('sgdm 1/1024', {'opt': 'sgdm', 'lr': 1 / 1024}),
                         ('sgdm 1/4096', {'opt': 'sgdm', 'lr': 1 / 4096}),
                         ('sgdm 1/1024 clip', {'opt': 'sgdm', 'lr': 1 / 1024, 'clipg': 0.05}),
                         ('lion 2^-10', {'opt': 'lion', 'lr': 2.0 ** -10}), ('lion 2^-11', {'opt': 'lion', 'lr': 2.0 ** -11}),
                         ('lion 2^-12', {'opt': 'lion', 'lr': 2.0 ** -12})):
            cfgs += [(name, 'float', 64, 'binder', s, dict(base, **kw), 12) for s in seeds]
    else:
        base = {'res': True, 'clamp': 8.0}
        cfgs += [('float adam', 'float', 64, 'binder', s, base, 24) for s in seeds]
        for k in (11, 12):
            cfgs += [('float sign 2^-%d' % k, 'float', 64, 'binder', s, dict(base, opt='lion', lr=2.0 ** -k), 24) for s in seeds]
            cfgs += [('int16 sign 2^-%d' % k, 'int', 64, 'binder', s, {'lr_shift': k}, 24) for s in seeds]
        cfgs += [('int16 sign 2^-11', 'int', 32, 'binder', s, {'lr_shift': 11}, 24) for s in seeds]
        cfgs += [('int16 sign 2^-11', 'int', 64, 'index', s, {'lr_shift': 11}, 24) for s in seeds]
    with mp.get_context('fork').Pool(min(len(cfgs), 28)) as pool:
        res = pool.map(run, cfgs, chunksize=1)
    by = {}
    for name, d, mode, seed, loss, a, ad, t, peak in res:
        by.setdefault((name, d, mode), []).append((a, ad, loss, t, peak))
    print('%-24s %3s %-7s %-32s %-8s %-8s %s' % ('variant', 'd', 'vars', 'accuracy by seed', 'mean', 'deeper', 'final loss by seed'))
    for (name, d, mode), rs in by.items():
        print('%-24s %3d %-7s %-32s %6.1f%% %6.1f%%  (%.0fs%s)' % (name, d, mode, ' '.join('%.1f' % (100 * a) for a, *_ in rs),
              100 * np.mean([a for a, *_ in rs]), 100 * np.mean([x[1] for x in rs]), max(x[3] for x in rs), rs[0][4]) + '  ' + ' '.join('%.2f' % x[2] for x in rs))
