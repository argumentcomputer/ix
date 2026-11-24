"""Sign-update training recipes for the STLC typecheck encoder, in exact
integers (`SignInt`) and as a floating-point twin of the same rule
(`SignFloat`). Model, data and forward format come from `stlc_toy`.

A recipe is a dict; every key has a default in `DEFAULT`:
  k          base step 2^-k
  kg         per-group extra shift: {'emb', 'cell', 'P', 'out'} -> int
  c1         sign of ((2^c1 - 1) m + g)          (7m + g is c1 = 3)
  c2         m <- ((2^c2 - 1) m + g) / 2^c2       (c2 = 7 is 127/128)
  sched      'step' (halve at 50/70/85/95%), 'lin' (linear to zero),
             'lin10' (linear to 1/16), or 'cos' (half cosine), all as a
             constant per-step table q_t in [0, 256]; the step is
             (2^(24-k) q_t) >> 8 in stored-weight units
  warm       warm-up steps: q_t ramps linearly from 0 over this many steps
  wd         decoupled weight decay p -= (p q_t) >> (wd + 8); 0 disables
  avg        Polyak average a <- a + (p - a) >> avg, evaluated instead of p;
             0 disables
  norm       0: pure sign. R > 0: step = unit * clip(n / 2^(c1 + bitlen(A)),
             -2, 2) with R fractional bits, A <- A + (|g| - A) >> c3
  c3         time constant of A
  dz         dead zone: do not move when |n| < (A << c1) >> dz; 0 disables
  loss       'mse' or 'sqhinge' (squared hinge at margin 1)
  bs         batch size (power of two)
  epochs
  init       multiplier on the initial weights
"""
import numpy as np, random, sys, time, os, json, pickle
import stlc_toy as T
from stlc_toy import (Encoder, IntEncoder, rshift, imat, F, S, WORD, TN, TB, CONST, VAR, Batch, make)

DEFAULT = dict(k=12, kg={}, c1=3, c2=7, sched='step', warm=0, wd=0, avg=0, norm=0, c3=7, dz=0,
               loss='mse', bs=64, epochs=24, init=1.0, opt='lion', mu=4, tensorA=0, box=0, psr=0)
GROUP = lambda name: ('emb' if name[0] == 'E' else 'P' if name == 'P' else 'out' if name in ('w', 'b0') else 'cell')


def schedule(cfg, steps):
    """Integer table q_t in [0, 256] for t in [0, steps)."""
    t = np.arange(steps); f = t / steps; s = cfg['sched']
    if s == 'step':
        q = 256 >> sum((f >= x).astype(np.int64) for x in (0.5, 0.7, 0.85, 0.95))
    elif s == 'lin':
        q = (256 * (steps - t)) // steps
    elif s == 'lin10':
        q = 16 + (240 * (steps - t)) // steps
    elif s == 'cos':
        q = np.rint(128 * (1 + np.cos(np.pi * f))).astype(np.int64)
    elif s == 'const':
        q = np.full(steps, 256)
    else:
        raise ValueError(s)
    q = np.asarray(q, dtype=np.int64)
    if cfg['warm']:
        q = np.minimum(q, (256 * (t + 1)) // cfg['warm'])
    return q


def bitlen(a):
    """Bit length of non-negative int64 entries (exact: values below 2^53)."""
    a = np.asarray(a)
    return np.where(a > 0, np.frexp(a.astype(np.float64))[1], 0).astype(np.int64)


class SignInt(IntEncoder):
    def __init__(self, d, mode, seed, cfg):
        ref = Encoder(d, mode, seed, res=True, clamp=WORD / (1 << F))
        self.d = d; self.mode = mode; self.cfg = cfg
        self.p = {k: np.round(v * cfg['init'] * (1 << (F + S))).astype(np.int64) for k, v in ref.p.items()}
        self.m = {k: np.zeros_like(v) for k, v in self.p.items()}
        self.A = {k: np.zeros_like(v) for k, v in self.p.items()}
        self.avgp = {k: v.copy() for k, v in self.p.items()} if cfg['avg'] else None
        self.peak = 0

    def grads(self, b):
        out, H, cache, w = self.forward(b)
        y = (b.y * (1 << F)).astype(np.int64); err = out - y
        if self.cfg['loss'] == 'sqhinge':
            err = np.where(y * out < (1 << (2 * F)), err, 0)
        lb = int(np.log2(len(b.y))); assert 1 << lb == len(b.y)
        g = {k: np.zeros_like(v) for k, v in self.p.items()}
        dy = err << (S + 1 - lb)
        g['w'] = imat(H[b.roots].T, dy[:, None])[:, 0]; g['b0'][0] = dy.sum()
        dH = np.zeros_like(H); dH[b.roots] = rshift(np.outer(dy, w['w']), F)
        d = self.d; inside = lambda raw: (raw >= -WORD - 1) & (raw <= WORD); pk = 0
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
        self.peak = max(self.peak, int(np.abs(dH).max()))
        return g, float(np.mean((err / (1 << F)) ** 2))

    def shr(self, x, k):
        """x / 2^k with round-to-nearest, or NITI-style pseudo-stochastic rounding
        when cfg['psr']: the discarded bits r split as hi (upper k - k//2 bits)
        and lo (lower k//2 bits); round up iff lo / 2^(k//2) < hi / 2^(k - k//2)."""
        if k == 0:
            return x
        if not self.cfg['psr'] or k < 2:
            return rshift(x, k)
        r = x & ((1 << k) - 1); kl = k // 2; kh = k - kl
        hi = r >> kl; lo = r & ((1 << kl) - 1)
        return (x >> k) + ((lo << kh) < (hi << kl))

    def step(self, b, q):
        c = self.cfg; g, loss = self.grads(b)
        for k in self.p:
            unit = ((1 << (F + S - c['k'] - c['kg'].get(GROUP(k), 0))) * q) >> 8
            gk = g[k]; m = self.m[k]
            if c['opt'] == 'sadam':
                # m <- m + (g - m) >> c2; A <- A + (|g| - A) >> c3; step = unit * clip(m / 2^bitlen(A), +-2)
                m = self.m[k] = m + self.shr(gk - m, c['c2'])
                ag = np.abs(gk)
                if c['tensorA']:
                    ag = np.full_like(ag, self.shr(np.int64(ag.sum()), int(np.log2(ag.size))))
                self.A[k] = self.A[k] + self.shr(ag - self.A[k], c['c3'])
                R = 4; u = np.clip(rshift_var(m << R, bitlen(self.A[k])), -(2 << R), 2 << R)
                delta = rshift(unit * u, R)
                if c['wd']: delta = delta + self.shr(self.p[k] * q, c['wd'] + 8)
                self.p[k] -= delta
                if c['box']: self.p[k] = np.clip(self.p[k], -c['box'] << (F + S), c['box'] << (F + S))
                self.peak = max(self.peak, int(np.abs(gk).max()), int(np.abs(m).max()) << R, int(np.abs(self.p[k]).max()) * 256)
                continue
            n = ((1 << c['c1']) - 1) * m + gk
            if c['norm'] or c['dz']:
                self.A[k] = self.A[k] + ((np.abs(gk) - self.A[k]) >> c['c3'])
            if c['opt'] == 'niti':
                # per-tensor b = bitlen(max |n|); u = round(n >> (b - mu)) in [-2^mu, 2^mu]; step = unit * u / 2^mu
                mu = c['mu']; sh = int(bitlen(np.abs(n).max())) - mu
                u = rshift(n, sh) if sh > 0 else n << -sh
                delta = rshift(unit * u, mu)
            elif c['norm']:
                R = c['norm']; sh = c['c1'] + bitlen(self.A[k])
                u = np.clip(rshift_var(n << R, sh), -(2 << R), 2 << R)
                delta = rshift(unit * u, R)
            else:
                delta = unit * np.sign(n)
            if c['dz']:
                delta = np.where(np.abs(n) < ((self.A[k] << c['c1']) >> c['dz']), 0, delta)
            if c['wd']:
                delta = delta + self.shr(self.p[k] * q, c['wd'] + 8)
            self.p[k] -= delta
            if c['box']: self.p[k] = np.clip(self.p[k], -c['box'] << (F + S), c['box'] << (F + S))
            self.m[k] = self.shr(((1 << c['c2']) - 1) * m + gk, c['c2'])
            if self.avgp is not None:
                self.avgp[k] += (self.p[k] - self.avgp[k]) >> c['avg']
            self.peak = max(self.peak, int(np.abs(gk).max()), int(np.abs(n).max()) << (c['norm'] or 0),
                            int(np.abs(self.p[k]).max()) * 256)
        return loss

    def eval_weights(self):
        if self.avgp is not None:
            self.p, self.avgp = self.avgp, self.p


def rshift_var(x, k):
    """x / 2^k rounded to nearest, k a per-entry non-negative shift."""
    k = np.broadcast_to(k, x.shape)
    half = np.where(k > 0, np.left_shift(np.int64(1), np.maximum(k - 1, 0)), 0)
    return (x + half) >> k


class SignFloat(Encoder):
    """The same rule in float64 on the `res` + clamp float model."""
    def __init__(self, d, mode, seed, cfg):
        super().__init__(d, mode, seed, res=True, clamp=WORD / (1 << F))
        self.cfg = cfg
        for k in self.p: self.p[k] = self.p[k] * cfg['init']
        self.A = {k: np.zeros_like(v) for k, v in self.p.items()}
        self.avgp = {k: v.copy() for k, v in self.p.items()} if cfg['avg'] else None

    def grads(self, b):
        p = self.p; out, H, cache = self.forward(b)
        err = out - b.y
        if self.cfg['loss'] == 'sqhinge': err = np.where(b.y * out < 1, err, 0.0)
        loss = float(np.mean(err ** 2))
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
                dX = gp @ p['W%d' % kind].T + np.concatenate([0.5 * dr, 0.5 * dr], axis=1)
                np.add.at(dH, c1, dX[:, :d]); np.add.at(dH, c2, dX[:, d:])
        return g, loss

    def step(self, b, q):
        c = self.cfg; g, loss = self.grads(b)
        for k in self.p:
            unit = 2.0 ** (-c['k'] - c['kg'].get(GROUP(k), 0)) * q / 256
            gk = g[k]; m = self.m[k]
            if c['opt'] == 'sadam':
                m = self.m[k] = m + (gk - m) / 2 ** c['c2']
                ag = np.abs(gk)
                if c['tensorA']: ag = np.full_like(ag, ag.sum() / 2 ** int(np.log2(ag.size)))
                self.A[k] = self.A[k] + (ag - self.A[k]) / 2 ** c['c3']
                A = self.A[k]; e = np.where(A > 0, np.frexp(A)[1], -60)
                delta = unit * np.clip(m / 2.0 ** e, -2, 2)
                if c['wd']: delta = delta + self.p[k] * q / 256 * 2.0 ** -c['wd']
                self.p[k] -= delta
                if c['box']: self.p[k] = np.clip(self.p[k], -c['box'], c['box'])
                continue
            n = (2 ** c['c1'] - 1) * m + gk
            if c['norm'] or c['dz']:
                self.A[k] = self.A[k] + (np.abs(gk) - self.A[k]) / 2 ** c['c3']
            if c['opt'] == 'niti':
                mx = np.abs(n).max(); e = np.frexp(mx)[1] if mx > 0 else 0
                delta = unit * np.round(n / 2.0 ** (e - c['mu'])) / 2 ** c['mu']
            elif c['norm']:
                A = self.A[k]; e = np.where(A > 0, np.frexp(A)[1], -60)    # 2^e > A >= 2^(e-1)
                delta = unit * np.clip(n / 2.0 ** (c['c1'] + e), -2, 2)
            else:
                delta = unit * np.sign(n)
            if c['dz']:
                delta = np.where(np.abs(n) < self.A[k] * 2.0 ** (c['c1'] - c['dz']), 0, delta)
            if c['wd']:
                delta = delta + self.p[k] * q / 256 * 2.0 ** -c['wd']
            self.p[k] -= delta
            if c['box']: self.p[k] = np.clip(self.p[k], -c['box'], c['box'])
            self.m[k] = ((2 ** c['c2'] - 1) * m + gk) / 2 ** c['c2']
            if self.avgp is not None:
                self.avgp[k] += (self.p[k] - self.avgp[k]) / 2 ** c['avg']
        return loss

    eval_weights = SignInt.eval_weights


DATA = {}
CACHE = os.environ.get('STLC_CACHE', os.path.join(os.environ.get('TMPDIR', '/tmp'), 'stlc_data.pkl'))

def load_data():
    if os.path.exists(CACHE):
        with open(CACHE, 'rb') as f: DATA.update(pickle.load(f)); return
    sys.setrecursionlimit(100000)
    rng = random.Random(20261123)
    DATA['items'], DATA['train'] = make(rng, 20032, 6, (0, 40))
    _, DATA['test'] = make(rng, 3008, 6, (0, 40))
    _, DATA['deep'] = make(rng, 3008, 6, (40, 80))
    with open(CACHE, 'wb') as f: pickle.dump(dict(DATA), f)

def run(job):
    name, kind, d, seed, cfg = job
    c = dict(DEFAULT); c.update(cfg)
    train = DATA['train%d' % c['bs']] if c['bs'] != 64 else DATA['train']
    t0 = time.time(); order = list(range(len(train))); r = random.Random(seed)
    if kind == 'adam':
        m = Encoder(d, 'binder', seed, res=True, clamp=8.0)
    else:
        m = SignInt(d, 'binder', seed, c) if kind == 'int' else SignFloat(d, 'binder', seed, c)
    q = schedule(c, c['epochs'] * len(train)); t = 0; curve = []
    for ep in range(c['epochs']):
        r.shuffle(order); tot = 0.0
        for i in order:
            if kind == 'adam': tot += m.step(train[i], 1 - 0.95 * ep / c['epochs'])
            else: tot += m.step(train[i], int(q[t]))
            t += 1
        curve.append(round(tot / len(order), 4))
    if kind != 'adam': m.eval_weights()
    acc, deep = T.accuracy(m, DATA['test']), T.accuracy(m, DATA['deep'])
    peak = float(np.log2(max(m.peak, 1))) if kind == 'int' else None
    return dict(name=name, kind=kind, d=d, seed=seed, cfg=cfg, acc=acc, deep=deep, peak=peak,
                loss=curve, secs=time.time() - t0)

def build_bs(bs):
    """Batches of `bs` terms over the same training terms in the same order."""
    from stlc_toy import flatten
    items = DATA['items']; graphs = [flatten(t) for t, _ in items]; labels = [y for _, y in items]
    n = len(items)
    DATA['train%d' % bs] = [Batch(graphs[i:i + bs], labels[i:i + bs]) for i in range(0, n - n % bs, bs)]

def sweep(jobs, out, procs=10):
    import multiprocessing as mp
    for c in {j[4].get('bs', 64) for j in jobs}:
        if c != 64 and 'train%d' % c not in DATA: build_bs(c)
    with mp.get_context('fork').Pool(min(len(jobs), procs)) as pool, open(out, 'a') as f:
        for res in pool.imap_unordered(run, jobs):
            f.write(json.dumps(res) + '\n'); f.flush()
            print('%-28s %-5s d%-3d s%d acc %.2f deep %.2f peak %s %.0fs' % (res['name'], res['kind'], res['d'], res['seed'],
                  100 * res['acc'], 100 * res['deep'], res['peak'] and '2^%.1f' % res['peak'], res['secs']), flush=True)

def summary(path):
    by = {}
    for line in open(path):
        r = json.loads(line); by.setdefault((r['name'], r['kind'], r['d']), []).append(r)
    print('%-30s %-5s %3s %-48s %6s %6s %6s %s' % ('recipe', 'arith', 'd', 'per-seed', 'mean', 'worst', 'deeper', 'peak'))
    for (name, kind, d), rs in by.items():
        rs.sort(key=lambda r: r['seed']); a = [100 * r['acc'] for r in rs]
        pk = max((r['peak'] for r in rs if r['peak'] is not None), default=None)
        print('%-30s %-5s %3d %-48s %6.2f %6.1f %6.2f %s' % (name, kind, d, ' '.join('%.1f' % x for x in a), np.mean(a), min(a),
              100 * np.mean([r['deep'] for r in rs]), '' if pk is None else '2^%.1f' % pk))

if __name__ == '__main__':
    load_data()
    if sys.argv[1] == 'summary':
        summary(sys.argv[2]); sys.exit()
    spec = json.loads(sys.argv[1])      # {"out": path, "recipes": {name: cfg}, "kinds": [...], "d": [...], "seeds": [...]}
    jobs = [(name, kind, d, s, cfg) for name, cfg in spec['recipes'].items() for kind in spec.get('kinds', ['int'])
            for d in spec.get('d', [64]) for s in spec.get('seeds', [1, 2, 3, 4])]
    sweep(jobs, spec['out'], spec.get('procs', 10))
