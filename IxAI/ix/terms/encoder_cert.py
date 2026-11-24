"""The term encoder of `encoder_gpu` with losses, updates and arithmetic that
can be stated as exact integer operations (add, multiply, compare, shift,
clamp), and a floating-point twin in which each integer feature can be
switched on separately.

    encoder_cert.py --loss pair --k 64 --opt sign --kexp 12 --arith wagpltu ...

Losses (all on raw dot products of clamped head outputs, scaled by 2^-sigma):
  pair   squared hinge  relu(margin - s(q, +) + s(q, -))^2  over the k highest
         scoring negatives of each query, every positive of a query weighted
         2^-round(log2 #positives)
  point  relu(1 - s(q, +))^2 weighted as above, plus lam * relu(1 + s(q, -))^2
         over the negatives, weighted 2^-round(log2 #negatives)
Updates:
  adam   torch Adam with the learning-rate schedule of `encoder_gpu`
  sign   p -= u_t sign(7 m + g) + p q_t 2^-22,  m <- (63 m + g) / 64,
         u_t = 2^-kexp q_t / 256, q_t = 256 halved at 50/70/85/95% of the steps
Arithmetic flags (`--arith`, any subset; all of them is the integer model):
  w  forward weights rounded to 2^-12 and clamped to the 16-bit word
  a  every dot product and shift in the forward pass rounded once to 2^-12,
     values clamped to [-8, 8 - 2^-12]
  p  mean pooling divides by 2^ceil(log2 n) instead of n
  t  max pooling sends its gradient to the first maximal node only
  l  scores rounded to 2^-12
  g  every backward product and shift rounded to 2^-G (`--G`)
  u  stored weights on 2^-24, momentum on the weight-gradient grid, update
     and decay rounded to those grids
  x  audit, every step: assert that every operand of a matrix product, sum,
     scatter-add and rounding lies on the grid its exact value lives on, that
     a bound on every partial sum (including the running accumulation of
     weight gradients) stays below 2^52 in units of that grid, and that
     forward values and head outputs fit 16-bit words; implies float64.
     `--audit_epochs` restricts it to the listed epochs.

In float64 with all flags every tensor holds an integer multiple of a fixed
power of two below 2^52 times that power, so the computation is integer
arithmetic on the scaled values.
"""
import argparse, json, math, os, sys, time
import numpy as np, torch
import torch.nn.functional as Fn
from cert_loss import Fixed, inv_sqrt_norm, norm_back, isoft, GD
from encoder_gpu_snapshot import (retrieval_loss, load_meta, Graph, SORT, VAR, REF, REC, PRJ, STR, NAT, APP, LAM, ALL, LET, DEV, log)

F = 12                      # fractional bits of forward values and forward weights
WS = 24                     # fractional bits of stored weights
LIM = 2.0 ** 52


_P2 = {}
def p2(e, like):
    """2^e for an integer tensor e in [-64, 64), by table lookup: the CUDA
    power and ldexp kernels are not exact."""
    if like not in _P2:
        _P2[like] = torch.tensor([2.0 ** i for i in range(-64, 64)], device=DEV, dtype=like)
    return _P2[like][e.long() + 64]


def flog2(n):
    """floor(log2 n) for an integer-valued tensor n >= 1, from the exact
    binary exponent (float log2 on CUDA is off by one at some powers of two)."""
    return torch.frexp(n.to(torch.float64)).exponent.long() - 1


def clog2(n):
    """ceil(log2 n) for an integer-valued tensor n >= 1."""
    n = n.to(torch.float64)
    return torch.where(n > 1, flog2((n - 1).clamp(min=1)) + 1, torch.zeros(n.shape, device=n.device, dtype=torch.long))


def check_log2(top=1 << 22):
    n = torch.arange(1, top, device=DEV)
    fl = flog2(n).cpu().numpy(); cl = clog2(n).cpu().numpy()
    ref_f = np.array([int(i).bit_length() - 1 for i in range(1, top)]); ref_c = np.array([int(i - 1).bit_length() for i in range(1, top)])
    assert (fl == ref_f).all() and (cl == ref_c).all(), 'bit-length helpers disagree with int.bit_length'


def pow2norm(x, ar):
    """x 2^-e per row with e = floor(log2(sum_j x_j^2) / 2), so that the row's
    Euclidean norm lies in [1, 2): a shift by a per-row exponent found from the
    bit length of an exact integer. Returns the scaled rows and 2^-e."""
    ssq = (x * x).sum(1)
    ex = torch.frexp(ssq).exponent
    e = torch.div(ex - 1, 2, rounding_mode='floor')
    f = p2(-e, x.dtype)[:, None]
    return ar.ra(x * f), f


def rnd(x, k):
    """Round to the grid 2^-k, to nearest with ties up."""
    return torch.floor(x * 2.0 ** k + 0.5) * 2.0 ** -k


class Arith:
    def __init__(self, flags, G):
        self.fl = set(flags); self.G = G; self.audit = 'x' in self.fl
        self.peak = 0.0           # largest bound on a partial sum, in integer units
        self.peak_at = ''; self.off = []; self.bounds = []; self.words = []; self.last = 0.0
        self.qpeak = {}; self.nchecks = 0; self.nsteps = 0
        self.st = {'vals': 0, 'clamped': 0, 'hvals': 0, 'hclamped': 0, 'dH': 0.0, 'gw': 0.0, 'm': 0.0, 'p': 0.0,
                   'grad_nz_float': 0, 'grad_nz': 0}
        self.hi = 8.0 - 2.0 ** -F if 'a' in self.fl else 8.0

    def ra(self, x): return rnd(x, F) if 'a' in self.fl else x
    def rg(self, x): return rnd(x, self.G) if 'g' in self.fl else x
    def wf(self, p): return rnd(p, F).clamp(-8.0, 8.0 - 2.0 ** -F) if 'w' in self.fl else p
    def clampv(self, x): return x.clamp(-8.0, self.hi)
    def inside(self, raw): return (raw >= -8.0) & (raw <= self.hi)

    def on_grid(self, x, g, what):
        """Record whether x lies on the grid 2^-g and its size in units of 2^-g;
        `flush` asserts on the records once per step."""
        if x.numel() == 0: return
        y = x * 2.0 ** g
        self.off.append(((y != torch.floor(y)).sum(), what))
        self.bounds.append((y.abs().max(), what))

    def mm(self, A, B, ga=None, gb=None, what=''):
        """A @ B. Under audit, both operands must lie on the grids 2^-ga, 2^-gb,
        and the bound min(max_i sum_k |A_ik| max|B|, max|A| max_j sum_k |B_kj|)
        on every partial sum, in units of 2^-(ga+gb), is recorded."""
        if not self.audit or ga is None or A.numel() == 0 or B.numel() == 0:
            return A @ B
        self.on_grid(A, ga, what + ' left'); self.on_grid(B, gb, what + ' right')
        aA = A.abs(); aB = B.abs()
        b = torch.minimum(aA.sum(-1).max() * aB.max(), aA.max() * aB.sum(0).max()) * 2.0 ** (ga + gb)
        self.bounds.append((b, what)); self.last = b
        return A @ B

    def word(self, x, g, bits, what):
        """Record that x on 2^-g fits a signed word of `bits` bits."""
        if self.audit and x.numel():
            self.on_grid(x, g, what)
            self.words.append((torch.maximum(x.max() * 2.0 ** g / (2.0 ** (bits - 1) - 1), -x.min() * 2.0 ** g / 2.0 ** (bits - 1)), what))

    def iadd(self, dst, idx, src, g=None, what=''):
        """dst.index_add_; under audit the bound max|dst| + (largest multiplicity
        of an index) max|src| on every partial sum is recorded."""
        if self.audit and g is not None and src.numel():
            self.on_grid(src, g, what)
            b = ((dst.abs().max() if dst.numel() else 0.0) + torch.bincount(idx).max() * src.abs().max()) * 2.0 ** g
            self.bounds.append((b, what))
        dst.index_add_(0, idx, src)
        return dst

    def colsum(self, x, g=None, what=''):
        if self.audit and g is not None and x.numel():
            self.on_grid(x, g, what); b = x.abs().sum(0).max() * 2.0 ** g
            self.bounds.append((b, what)); self.last = b
        return x.sum(0)

    def flush(self):
        if not self.audit or not self.bounds: return
        off = torch.stack([o for o, _ in self.off]).cpu().numpy() if self.off else np.zeros(0)
        bs = torch.stack([b.to(torch.float64) for b, _ in self.bounds]).cpu().numpy()
        bad = [w for (_, w), o in zip(self.off, off) if o]
        assert not bad, 'off grid: %s' % sorted(set(bad))
        i = int(bs.argmax())
        assert bs[i] < LIM, 'partial sum bound 2^%.2f at %s' % (math.log2(bs[i]), self.bounds[i][1])
        if bs[i] > self.peak: self.peak = float(bs[i]); self.peak_at = self.bounds[i][1]
        for (_, w), b in zip(self.bounds, bs):
            key = w.split(' ')[0] if not w.startswith('loss') else w
            if b > self.qpeak.get(key, 0.0): self.qpeak[key] = float(b)
        if self.words:
            ws = torch.stack([b.to(torch.float64) for b, _ in self.words]).cpu().numpy()
            j = int(ws.argmax())
            assert ws[j] <= 1.0, 'word overflow at %s (%.3f of range)' % (self.words[j][1], ws[j])
        self.nchecks += len(self.bounds) + len(self.off) + len(self.words); self.nsteps += 1
        self.off = []; self.bounds = []; self.words = []


class Encoder:
    """`encoder_gpu.Encoder` with every arithmetic step routed through `Arith`."""
    def __init__(self, d, slots, seed, dtype, pool, nary, ar):
        g = torch.Generator().manual_seed(seed); s = 1.0 / math.sqrt(d)
        def rn(*shape): return (torch.randn(*shape, generator=g, dtype=torch.float64) * s).to(DEV, dtype)
        def zs(*shape): return torch.zeros(*shape, device=DEV, dtype=dtype)
        self.d = d; self.dtype = dtype; self.pool = pool; self.ar = ar
        self.width = d * {'none': 1, 'mean': 2, 'meanmax': 3}[pool]
        self.slot = slots
        self.p = {'Esort': rn(20, d), 'Econst': rn(int(slots.max()) + 1, d), 'Evar': rn(64, d), 'Elit': rn(40, d),
                  'P': rn(d, d), 'Wp': rn(d, d), 'bp': zs(d), 'W10': rn(3 * d, d), 'b10': zs(d)}
        self.nary = nary
        for k in ((LAM, ALL) if nary else (APP, LAM, ALL)):
            self.p['W%d' % k] = rn(2 * d, d); self.p['b%d' % k] = zs(d)
        if nary:
            self.p['Wh'] = rn(d, d); self.p['Wa'] = rn(7, d, d); self.p['ba'] = zs(d)

    def leaf(self, tag, x):
        if tag == SORT: return 'Esort', x.clamp(max=19)
        if tag in (REF, REC): return 'Econst', self.slot[x.clamp(max=self.slot.numel() - 1)]
        if tag == NAT: return 'Elit', 1 + x.clamp(max=37)
        return 'Elit', torch.zeros_like(x)

    @torch.no_grad()
    def forward(self, G, batch, keep=True):
        ids, order, tags, counts, rootpos, seg, npos, lens = batch; ar = self.ar
        w = {k: ar.wf(v) for k, v in self.p.items()}
        fa = F if ar.audit else None
        for k, v in w.items(): ar.word(v, F, 16, 'fwd weight ' + k)
        H = torch.zeros(ids.numel(), self.d, device=DEV, dtype=self.dtype); cache = []; s = 0
        pos = lambda gid: torch.searchsorted(ids, gid)
        nvals = 0; nclamp = 0
        for tag, n in zip(tags, counts):
            idx = order[s:s + n]; s += n; gid = ids[idx]
            raw = None
            if tag in (SORT, REF, REC, STR, NAT):
                name, row = self.leaf(tag, G.x[gid]); H[idx] = w[name][row]; rec = (tag, idx, name, row)
            elif tag == VAR:
                vi = G.x[gid].clamp(max=63); ty = G.y[gid]; has = ty < G.n
                raw = w['Evar'][vi]
                tp = pos(ty[has]); raw[has] += ar.ra(ar.mm(H[tp], w['P'], fa, fa, 'fwd P'))
                rec = (tag, idx, vi, has, tp, ar.inside(raw))
            elif tag == APP and self.nary:
                head = pos(G.x[gid]); na = G.z[gid]; hh = H[head]
                node = torch.repeat_interleave(torch.arange(n, device=DEV), na)
                off = torch.arange(node.numel(), device=DEV) - (torch.cumsum(na, 0) - na)[node]
                apos = pos(G.args[G.y[gid][node] + off]); back = na[node] - 1 - off
                slot = torch.where(back < 3, back, torch.where(off < 3, 3 + off, torch.full_like(off, 6)))
                Ha = H[apos]; lin = hh @ w['Wh']
                sels = []
                for sl in range(7):
                    sel = torch.nonzero(slot == sl).flatten(); sels.append(sel)
                    if sel.numel(): lin.index_add_(0, node[sel], Ha[sel] @ w['Wa'][sl])
                if ar.audit:
                    ar.on_grid(hh, F, 'fwd app head'); ar.on_grid(Ha, F, 'fwd app args')
                    l1 = hh.abs().sum(1) + torch.zeros(n, device=DEV, dtype=self.dtype).index_add_(0, node, Ha.abs().sum(1))
                    wmax = torch.maximum(w['Wh'].abs().max(), w['Wa'].abs().max())
                    ar.bounds.append((l1.max() * wmax * 2.0 ** (2 * F), 'fwd app lin'))
                    ar.on_grid(lin, 2 * F, 'fwd app lin')
                    ar.bounds.append((torch.zeros_like(hh).index_add_(0, node, Ha.abs()).max() * 2.0 ** F, 'fwd app argsum'))
                naf = na.to(torch.float64)
                sf = torch.div(flog2(naf + 1), 2, rounding_mode='floor'); cf = 1 + clog2(naf)
                f = p2(-sf, self.dtype)[:, None]; c = p2(-cf, self.dtype)[:, None]
                asum = torch.zeros_like(hh).index_add_(0, node, Ha)
                if 'a' in ar.fl:
                    pre = rnd(lin * f, F) + w['ba']
                    raw = pre.clamp(min=0) + rnd(0.5 * hh, F) + rnd(asum * c, F)
                else:
                    pre = lin * f + w['ba']
                    raw = pre.clamp(min=0) + 0.5 * hh + asum * c
                rec = (tag, idx, head, hh, node, apos, sels, Ha, f, c, pre > 0, ar.inside(raw))
            elif tag in (APP, LAM, ALL):
                a = pos(G.x[gid]); b = pos(G.y[gid]); ha = H[a]; hb = H[b]
                X = torch.cat([ha, hb], 1); pre = ar.ra(ar.mm(X, w['W%d' % tag], fa, fa, 'fwd bin')) + w['b%d' % tag]
                raw = pre.clamp(min=0) + ar.ra(0.5 * (ha + hb))
                rec = (tag, idx, a, b, X, pre > 0, ar.inside(raw))
            elif tag == LET:
                a = pos(G.x[gid]); b = pos(G.y[gid]); c = pos(G.z[gid])
                X = torch.cat([H[a], H[b], H[c]], 1); pre = ar.ra(ar.mm(X, w['W10'], fa, fa, 'fwd let')) + w['b10']
                raw = pre.clamp(min=0) + ar.ra(0.5 * (H[b] + H[c]))
                rec = (tag, idx, a, b, c, X, pre > 0, ar.inside(raw))
            else:
                c = pos(G.z[gid]); hc = H[c]; pre = ar.ra(ar.mm(hc, w['Wp'], fa, fa, 'fwd proj')) + w['bp']
                raw = pre.clamp(min=0) + hc
                rec = (tag, idx, c, hc, pre > 0, ar.inside(raw))
            if raw is not None:
                if ar.audit: ar.on_grid(raw, F, 'fwd raw')
                H[idx] = ar.clampv(raw); nvals += raw.numel(); nclamp = nclamp + (~rec[-1]).sum()
            if keep: cache.append(rec)
        ar.st['vals'] += nvals; ar.st['clamped'] += int(nclamp)
        ar.word(H, F, 16, 'fwd values')
        out = [H[rootpos]]; pc = None
        if self.pool != 'none':
            Hn = H[npos]; n = lens.numel()
            ssum = torch.zeros(n, self.d, device=DEV, dtype=self.dtype).index_add_(0, seg, Hn)
            if ar.audit:
                ar.on_grid(ssum, F, 'fwd pool sum')
                ar.bounds.append((torch.zeros_like(ssum).index_add_(0, seg, Hn.abs()).max() * 2.0 ** F, 'fwd pool sum'))
            if 'p' in ar.fl:
                lsh = clog2(lens)
                scale = p2(-lsh, self.dtype)[:, None]
                mean = ar.ra(ssum * scale)
            else:
                scale = 1.0 / lens.to(self.dtype)[:, None]; mean = ssum * scale
            out.append(mean)
            if self.pool == 'meanmax':
                mx = torch.full((n, self.d), -1e30, device=DEV, dtype=self.dtype).scatter_reduce_(
                    0, seg[:, None].expand(-1, self.d), Hn, 'amax', include_self=True)
                out.append(mx); at = Hn == mx[seg]
                if 't' in ar.fl:
                    ix = torch.arange(Hn.shape[0], device=DEV)[:, None].expand(-1, self.d)
                    key = torch.where(at, ix, torch.full_like(ix, 1 << 40))
                    first = torch.full((n, self.d), 1 << 40, device=DEV, dtype=torch.long).scatter_reduce_(
                        0, seg[:, None].expand(-1, self.d), key, 'amin', include_self=True)
                    pc = ((ix == first[seg]).to(self.dtype), None)
                else:
                    pc = (at, torch.zeros(n, self.d, device=DEV, dtype=self.dtype).index_add_(0, seg, at.to(self.dtype)))
            pc = (scale,) + (pc if pc else ())
        return torch.cat(out, 1), (H, cache, rootpos, seg, npos, lens, pc, w)

    @torch.no_grad()
    def backward(self, state, droots):
        """Gradients of every parameter from the gradient in the pooled root vectors."""
        H, cache, rootpos, seg, npos, lens, pc, w = state; d = self.d; ar = self.ar; G_ = ar.G
        gq = G_ if ar.audit else None; gw = (F + G_) if ar.audit else None
        g = {k: torch.zeros_like(v) for k, v in self.p.items()}
        cb = {}
        def acc(k, val):
            if ar.audit: cb[k] = cb.get(k, 0.0) + ar.last
            return val
        dH = torch.zeros_like(H); ar.iadd(dH, rootpos, droots[:, :d], gq, 'root')
        if self.pool != 'none':
            scale = pc[0]
            ar.iadd(dH, npos, ar.rg(droots[:, d:2 * d] * scale)[seg], gq, 'mean pool')
            if self.pool == 'meanmax':
                at, ties = pc[1], pc[2]
                dm = droots[:, 2 * d:] if ties is None else droots[:, 2 * d:] / ties
                ar.iadd(dH, npos, dm[seg] * at, gq, 'max pool')
        mm = ar.mm
        for rec in reversed(cache):
            tag, idx = rec[0], rec[1]; dh = dH[idx]
            if tag in (SORT, REF, REC, STR, NAT):
                ar.iadd(g[rec[2]], rec[3], dh, gq, 'table')
            elif tag == VAR:
                _, _, vi, has, tp, inside = rec; dr = dh * inside
                ar.iadd(g['Evar'], vi, dr, gq, 'Evar')
                drh = dr[has]; g['P'] += acc('P', mm(H[tp].T, drh, F, gq, 'gP'))
                ar.iadd(dH, tp, ar.rg(mm(drh, w['P'].T, gq, F, 'dP')), gq, 'var type')
            elif tag == APP and self.nary:
                _, _, head, hh, node, apos, sels, Ha, f, c, act, inside = rec; dr = dh * inside; gp = dr * act
                g['ba'] += acc('ba', ar.colsum(gp, gw, 'gba')); gl = ar.rg(gp * f)
                g['Wh'] += acc('Wh', mm(hh.T, gl, F, gq, 'gWh'))
                ar.iadd(dH, head, ar.rg(mm(gl, w['Wh'].T, gq, F, 'dWh')) + ar.rg(0.5 * dr), gq, 'head')
                dA = ar.rg(dr * c)[node]; gn = gl[node]
                for sl in range(7):
                    sel = sels[sl]
                    if sel.numel():
                        g['Wa'][sl] += acc('Wa%d' % sl, mm(Ha[sel].T, gn[sel], F, gq, 'gWa'))
                        dA[sel] += ar.rg(mm(gn[sel], w['Wa'][sl].T, gq, F, 'dWa'))
                ar.iadd(dH, apos, dA, gq, 'args')
            elif tag in (APP, LAM, ALL):
                _, _, a, b, X, act, inside = rec; dr = dh * inside; gp = dr * act
                g['W%d' % tag] += acc('W%d' % tag, mm(X.T, gp, F, gq, 'gW')); g['b%d' % tag] += acc('b%d' % tag, ar.colsum(gp, gw, 'gb'))
                dX = ar.rg(mm(gp, w['W%d' % tag].T, gq, F, 'dW')); hr = ar.rg(0.5 * dr)
                ar.iadd(dH, a, dX[:, :d] + hr, gq, 'bin a'); ar.iadd(dH, b, dX[:, d:] + hr, gq, 'bin b')
            elif tag == LET:
                _, _, a, b, c, X, act, inside = rec; dr = dh * inside; gp = dr * act
                g['W10'] += acc('W10', mm(X.T, gp, F, gq, 'gW10')); g['b10'] += acc('b10', ar.colsum(gp, gw, 'gb10'))
                dX = ar.rg(mm(gp, w['W10'].T, gq, F, 'dW10')); hr = ar.rg(0.5 * dr)
                ar.iadd(dH, a, dX[:, :d], gq, 'let'); ar.iadd(dH, b, dX[:, d:2 * d] + hr, gq, 'let')
                ar.iadd(dH, c, dX[:, 2 * d:] + hr, gq, 'let')
            else:
                _, _, c, hc, act, inside = rec; dr = dh * inside; gp = dr * act
                g['Wp'] += acc('Wp', mm(hc.T, gp, F, gq, 'gWp')); g['bp'] += acc('bp', ar.colsum(gp, gw, 'gbp'))
                ar.iadd(dH, c, ar.rg(mm(gp, w['Wp'].T, gq, F, 'dWp')) + dr, gq, 'proj')
        if ar.audit:
            ar.st['dH'] = max(ar.st['dH'], float(dH.abs().max()) * 2.0 ** G_)
            for k, v in g.items(): ar.on_grid(v, F + G_, 'gradient ' + k)
            for k, b in cb.items(): ar.bounds.append((b if torch.is_tensor(b) else torch.tensor(b, device=DEV), 'running gradient ' + k))
        return g


# ------------------------------------------------------------------ heads and losses
def pow2w(cnt, cap=10):
    """round(log2 cnt) for cnt >= 1: e = floor(log2 cnt), plus one when cnt^2 >= 2^(2e+1)."""
    c = cnt.clamp(min=1).to(torch.float64); e = flog2(c)
    return (e + (c * c >= p2(2 * e + 1, torch.float64)).long()).clamp(max=cap)


def scores_loss(args, ar, q, p, pq, pc, sq, sc, nq):
    """Scores, loss and the gradient of the loss in the scores."""
    S = (q @ p.T) * 2.0 ** -args.sigma
    if 'l' in ar.fl: S = rnd(S, F)
    nc = S.shape[1]; dt = S.dtype
    npos = torch.bincount(pq, minlength=nq)
    lw = pow2w(npos)[pq]; wpos = p2(-lw, dt)          # per positive pair
    cst = 2.0 ** -(nq.bit_length() - 1)
    dS = torch.zeros_like(S); loss = 0.0
    if args.loss in ('pair', 'both'):
        neg = S.clone(); neg[pq, pc] = -1e30; neg[sq, sc] = -1e30
        kk = min(args.k, nc); top, ti = neg.topk(kk, dim=1)
        kc = 2.0 ** -(kk.bit_length() - 1)
        sp = S[pq, pc]
        e = (args.margin - sp[:, None] + top[pq]).clamp(min=0)         # [P, kk]
        we = (wpos * cst * kc)[:, None] * e
        if ar.audit:
            ar.on_grid(S, F, 'scores'); ar.on_grid(e, F, 'hinge'); ar.on_grid(we, grad_grid(args), 'weighted hinge')
        loss += float((we * e).sum())
        dS.index_put_((pq, pc), -2 * we.sum(1), accumulate=True)
        rows = pq[:, None].expand(-1, kk)
        dS.index_put_((rows.reshape(-1), ti[pq].reshape(-1)), (2 * we).reshape(-1), accumulate=True)
    if args.loss == 'softmax2':
        # multi-positive softmax in base 2 whose per-pair denominator Z is replaced
        # by the power of two 2^ceil(log2 Z); the gradient needs no log, no division
        neg = S.clone(); neg[pq, pc] = -1e30; neg[sq, sc] = -1e30
        mx = torch.maximum(neg.max(1).values, torch.zeros_like(neg[:, 0]).index_reduce_(0, pq, S[pq, pc], 'amax', include_self=False))
        E = torch.exp2(neg - mx[:, None]); N = E.sum(1)
        Ep = torch.exp2(S[pq, pc] - mx[pq]); Z = Ep + N[pq]
        b = p2(-torch.ceil(torch.log2(Z)).long(), dt) if args.p2den else 1.0 / Z
        w = wpos * cst
        loss = float((w * (torch.log2(Z) - torch.log2(Ep))).sum())
        dS.index_put_((pq, pc), w * (Ep - Z) * b, accumulate=True)
        coef = torch.zeros(nq, device=S.device, dtype=dt).index_add_(0, pq, w * b)
        dS += coef[:, None] * E
        return S, loss, dS
    if args.loss in ('point', 'both'):
        a = 1.0 if args.loss == 'point' else args.anchor
        sp = S[pq, pc]; e = (1 - sp).clamp(min=0)
        we = wpos * (cst * a) * e; loss += float((we * e).sum())
        dS.index_put_((pq, pc), -2 * we, accumulate=True)
        mask = torch.ones_like(S, dtype=torch.bool); mask[pq, pc] = False; mask[sq, sc] = False
        nn_ = mask.sum(1)
        wn = p2(-pow2w(nn_, 16), dt)[:, None] * (args.lam * cst * a)
        en = (1 + S).clamp(min=0) * mask
        loss += float((wn * en * en).sum()); dS += 2 * wn * en
    return S, loss, dS


def grad_grid(args):
    """Grid exponent of dS: margin and scores on 2^-F times the power-of-two
    weights of `scores_loss` (lam a multiple of 1/8)."""
    pair = F + 10 + 9 + round(math.log2(args.k)); point = F + 16 + 9 + 3
    return {'pair': pair, 'point': point}.get(args.loss, max(pair, point) + 3)


# ------------------------------------------------------------------ main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--d', type=int, default=128); ap.add_argument('--out', type=int, default=128)
    ap.add_argument('--epochs', type=int, default=12); ap.add_argument('--queries', type=int, default=512)
    ap.add_argument('--random', type=int, default=1024); ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--pool', default='meanmax'); ap.add_argument('--graph', default='graph_nary')
    ap.add_argument('--loss', default='pair', choices=['pair', 'point', 'both', 'softmax', 'softmax2', 'isoft'])
    ap.add_argument('--iround', type=int, default=1, help='isoft: apply the fixed-point roundings')
    ap.add_argument('--audit_epochs', default='', help='comma-separated epochs (1-based) run with the audit; empty = flag x decides')
    ap.add_argument('--p2den', type=int, default=1, help='softmax2: power-of-two denominators')
    ap.add_argument('--norm', default='none', choices=['none', 'pow2', 'l2'],
                    help='pow2: scale head outputs to Euclidean norm in [1, 2) by a power of two; l2: exact (float only)')
    ap.add_argument('--scale', type=float, default=30.0, help='softmax temperature on cosines')
    ap.add_argument('--anchor', type=float, default=1.0, help='weight of the pointwise term in --loss both')
    ap.add_argument('--k', type=int, default=64); ap.add_argument('--margin', type=float, default=1.0)
    ap.add_argument('--lam', type=float, default=1.0); ap.add_argument('--sigma', type=int, default=4)
    ap.add_argument('--opt', default='adam', choices=['adam', 'sign'])
    ap.add_argument('--lr', type=float, default=1e-3)
    ap.add_argument('--kexp', type=int, default=13); ap.add_argument('--kemb', type=int, default=0, help='extra shift for tables')
    ap.add_argument('--wd', type=int, default=14, help='decay p q_t 2^-(wd+8); 0 = none')
    ap.add_argument('--rows', default='lazy', choices=['lazy', 'dense'])
    ap.add_argument('--arith', default='', help='subset of wapltgux')
    ap.add_argument('--G', type=int, default=32, help='fractional bits of backward values')
    ap.add_argument('--f64', action='store_true'); ap.add_argument('--check', action='store_true')
    ap.add_argument('--eval_every', type=int, default=1)
    ap.add_argument('--name', default=''); ap.add_argument('--results', default='/opt/dlami/nvme/ix-ai/terms/runs/cert/results.jsonl')
    ap.add_argument('--save', default='', help='write final parameters, momentum and options here')
    args = ap.parse_args()
    check_log2()
    ar = Arith(args.arith, args.G)
    dt = torch.float64 if (args.f64 or args.check or set(args.arith) & set('ux')) else torch.float32
    torch.manual_seed(args.seed); rng = np.random.default_rng(args.seed)
    M = load_meta(); Gr = Graph(args.graph)
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
    log('config', json.dumps(vars(args)))
    seen_rows = np.nonzero(~held[lib_mod])[0]
    cnt = np.zeros(len(Gr.roots), dtype=np.int64)
    for c in np.unique(lib_cid[seen_rows]):
        ns = Gr.nodes[Gr.ptr[c]:Gr.ptr[c + 1]]
        m = (Gr.tag_np[ns] == REF) | (Gr.tag_np[ns] == REC)
        cs = Gr.x_np[ns][m]; cnt[cs[cs < len(cnt)]] += 1
    slots = np.zeros(len(Gr.roots) + 1, dtype=np.int64); keep = np.nonzero(cnt >= 3)[0]; slots[keep] = 1 + np.arange(len(keep))
    enc = Encoder(args.d, torch.from_numpy(slots).to(DEV), args.seed, dt, args.pool, Gr.nary, ar)
    g = torch.Generator().manual_seed(args.seed + 100)
    heads = {'Aq': (torch.randn(enc.width, args.out, generator=g, dtype=torch.float64) / math.sqrt(args.d)).to(DEV, dt),
             'Ap': (torch.randn(enc.width, args.out, generator=g, dtype=torch.float64) / math.sqrt(args.d)).to(DEV, dt)}
    P = dict(enc.p); P.update(heads)
    if 'u' in ar.fl:
        for k in P: P[k].copy_(rnd(P[k], WS))
    enc.p = {k: P[k] for k in enc.p}
    TABLES = ('Esort', 'Econst', 'Evar', 'Elit')
    log('parameters', sum(v.numel() for v in P.values()), 'dtype', dt)

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

    def head(R, name, w):
        raw = ar.ra(ar.mm(R, w[name], F if ar.audit else None, F, 'fwd head ' + name)); ins = ar.inside(raw)
        ar.word(ar.clampv(raw), F, 16, 'head ' + name)
        ar.st['hvals'] += raw.numel(); ar.st['hclamped'] += int((~ins).sum())
        return ar.clampv(raw), ins

    @torch.no_grad()
    def loss_and_grads(items):
        t = lambda a: torch.from_numpy(a).to(DEV)
        allc, qi, ci, pq, pc, sq, sc = step_batch(items)
        R, state = enc.forward(Gr, Gr.batch(allc))
        w = state[-1]; w['Aq'] = ar.wf(P['Aq']); w['Ap'] = ar.wf(P['Ap'])
        qi, ci, pq, pc, sq, sc = map(t, (qi, ci, pq, pc, sq, sc))
        Rq, Rp = R[qi], R[ci]
        q, iq = head(Rq, 'Aq', w); p, ip = head(Rp, 'Ap', w)
        ar.st['qn'] = q.norm(dim=1).mean(); ar.st['pn'] = p.norm(dim=1).mean()
        fq = fp = 1.0
        if args.norm == 'pow2':
            q, fq = pow2norm(q, ar); p, fp = pow2norm(p, ar)
        elif args.norm == 'l2':
            with torch.enable_grad():
                q0 = q.clone().requires_grad_(); p0 = p.clone().requires_grad_()
                qn_, pn_ = Fn.normalize(q0, dim=1), Fn.normalize(p0, dim=1)
            q, p = qn_.detach(), pn_.detach()
        gs = grad_grid(args) if ar.audit else None; gq = args.G if ar.audit else None
        if args.loss == 'isoft':
            fx = Fixed(bool(args.iround), ar)
            qd, pd_ = q.double(), p.double()
            qh, invq = inv_sqrt_norm(qd, fx); ph, invp = inv_sqrt_norm(pd_, fx)
            S, loss, dS = isoft(qh, ph, pq, pc, sq, sc, len(items), fx)
            dqh = fx.r(fx.mm(dS, ph, GD, 14, 'dqh'), args.G, GD + 14, 'dqh')
            dph = fx.r(fx.mm(dS.T, qh, GD, 14, 'dph'), args.G, GD + 14, 'dph')
            dq = norm_back(qh, invq, dqh, fx, args.G).to(q.dtype); dp = norm_back(ph, invp, dph, fx, args.G).to(q.dtype)
        elif args.loss == 'softmax':
            with torch.enable_grad():
                qq = q.clone().requires_grad_(); pp = p.clone().requires_grad_()
                if args.norm == 'pow2':
                    L = retrieval_loss(qq, pp, pq, pc, sq, sc, args.scale / 2)
                else:
                    L = retrieval_loss(Fn.normalize(qq, dim=1), Fn.normalize(pp, dim=1), pq, pc, sq, sc, args.scale)
                L.backward()
            loss = float(L); dq = ar.rg(qq.grad * fq); dp = ar.rg(pp.grad * fp)
        else:
            S, loss, dS = scores_loss(args, ar, q, p, pq, pc, sq, sc, len(items))
            sg = 2.0 ** -args.sigma
            dq = ar.rg(ar.mm(dS, p, gs, F, 'dq') * sg * fq)
            dp = ar.rg(ar.mm(dS.T, q, gs, F, 'dp') * sg * fp)
        if args.norm == 'l2':
            dq, dp = torch.autograd.grad((qn_, pn_), (q0, p0), (dq, dp))
        dq = dq * iq; dp = dp * ip
        grads = {'Aq': ar.mm(Rq.T, dq, F, gq, 'gAq'), 'Ap': ar.mm(Rp.T, dp, F, gq, 'gAp')}
        dR = torch.zeros_like(R)
        ar.iadd(dR, qi, ar.rg(ar.mm(dq, w['Aq'].T, gq, F, 'dRq')), gq, 'dRq')
        ar.iadd(dR, ci, ar.rg(ar.mm(dp, w['Ap'].T, gq, F, 'dRp')), gq, 'dRp')
        grads.update(enc.backward(state, dR))
        return loss, grads, state[0].shape[0], len(allc)

    if args.check:
        items = train[:6]
        saved_rng = rng.bit_generator.state
        def value():
            rng.bit_generator.state = saved_rng
            return loss_and_grads(items)
        loss, grads, _, _ = value(); worst = 0.0
        for k, v in P.items():
            gflat = grads[k].reshape(-1); flat = v.reshape(-1); err = 0.0
            for j in torch.topk(gflat.abs(), min(4, gflat.numel())).indices.tolist():
                if abs(float(gflat[j])) < 1e-9: continue
                old = float(flat[j])
                flat[j] = old + 1e-6; lp = value()[0]; flat[j] = old - 1e-6; lm = value()[0]; flat[j] = old
                num = (lp - lm) / 2e-6; err = max(err, abs(num - float(gflat[j])) / (abs(num) + abs(float(gflat[j]))))
            log('  %-7s largest gradient %.2e  relative error %.1e' % (k, float(gflat.abs().max()), err)); worst = max(worst, err)
        log('gradient check: worst relative error %.2e' % worst)
        return

    # ---------------------------------------------------------- optimiser
    steps_per_ep = (min(len(train), args.limit or len(train)) - args.queries) // args.queries + 1
    T = steps_per_ep * args.epochs
    if args.opt == 'adam':
        for v in P.values(): v.requires_grad_(False)
        tens = [torch.nn.Parameter(v) for v in P.values()]
        P = dict(zip(P.keys(), tens)); enc.p = {k: P[k] for k in enc.p}
        opt = torch.optim.Adam(tens, lr=args.lr)
    Mom = {k: torch.zeros_like(v) for k, v in P.items()}
    gridm = F + args.G
    moved = {'rows_touched': 0.0, 'n': 0}

    @torch.no_grad()
    def sign_update(grads, t):
        frac = t / T; q = 256 >> sum(frac >= x for x in (0.5, 0.7, 0.85, 0.95)); mx = []
        for k, v in P.items():
            gk = grads[k]; m = Mom[k]
            unit = 2.0 ** -(args.kexp + (args.kemb if k in TABLES else 0)) * q / 256
            n = 7 * m + gk
            delta = unit * torch.sign(n)
            if args.wd:
                dec = v * (q * 2.0 ** -(args.wd + 8))
                if 'u' in ar.fl: dec = rnd(dec, WS)
                delta = delta + dec
            mnew = (63 * m + gk) / 64
            if 'u' in ar.fl: mnew = rnd(mnew, gridm)
            if k in TABLES and args.rows == 'lazy':
                touched = (gk != 0).any(1, keepdim=True)
                delta = delta * touched; mnew = torch.where(touched, mnew, m)
                if k == 'Econst': moved['rows_touched'] += touched.float().mean(); moved['n'] += 1
            v -= delta; Mom[k] = mnew
            if ar.audit:
                ar.on_grid(v, WS, 'weight ' + k); ar.on_grid(mnew, gridm, 'momentum ' + k)
                mx.append(torch.stack([n.abs().max() * 2.0 ** gridm, gk.abs().max() * 2.0 ** gridm, v.abs().max() * 2.0 ** WS]))
                ar.bounds.append((((63 * m).abs().max() + gk.abs().max()) * 2.0 ** gridm, 'momentum ' + k))
                ar.bounds.append((((7 * m).abs().max() + gk.abs().max()) * 2.0 ** gridm, 'sign arg ' + k))
                ar.word(v, WS, 26, 'stored weight ' + k)
                ar.bounds.append((v.abs().max() * q * 2.0 ** WS, 'decay ' + k))
        if mx:
            a = torch.stack(mx).max(0).values.tolist()
            ar.st['m'] = max(ar.st['m'], a[0]); ar.st['gw'] = max(ar.st['gw'], a[1]); ar.st['p'] = max(ar.st['p'], a[2])

    # ---------------------------------------------------------- evaluation
    lib_u = np.unique(lib_cid); col_of_row = np.searchsorted(lib_u, lib_cid)
    lm_t = torch.from_numpy(lib_mod).to(DEV); ld_t = torch.from_numpy(lib_decl).to(DEV); lc_t = torch.from_numpy(lib_cid).to(DEV)
    reach_t = torch.from_numpy(reach).to(DEV)
    use = np.zeros(NL, dtype=np.int64)
    for i in np.nonzero(item_split == 0)[0]:
        for c in gold[gptr[i]:gptr[i + 1]]: use[first[int(c)]] += 1

    @torch.no_grad()
    def embed(cids, name):
        out = []; wn = ar.wf(P[name].detach())
        for s in range(0, len(cids), 4096):
            roots, _ = enc.forward(Gr, Gr.batch(cids[s:s + 4096]), keep=False)
            e = ar.clampv(ar.ra(roots @ wn))
            if args.loss == 'isoft': e = inv_sqrt_norm(e.double(), Fixed(bool(args.iround), ar))[0]
            if args.norm == 'pow2': e = pow2norm(e, ar)[0]
            if args.norm == 'l2': e = Fn.normalize(e, dim=1)
            out.append(Fn.normalize(e, dim=1) if args.loss == 'softmax' else e)
        return torch.cat(out)

    @torch.no_grad()
    def evaluate(items, Pm, name):
        Q = embed(lib_cid[item_row[items]], 'Aq')
        Prow = Pm[torch.from_numpy(col_of_row).to(DEV)]
        hits = np.zeros(3); gold_n = 0; rr = 0.0; ks = (1, 5, 10)
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
                grow = [x for c in gs for x in rows_of[int(c)]]
                best = S[k, torch.tensor(grow, device=DEV)].max()
                if best > -1e29: rr += 1.0 / (int((S[k] > best).sum()) + 1)
        res = dict(r1=100 * hits[0] / gold_n, r5=100 * hits[1] / gold_n, r10=100 * hits[2] / gold_n, mrr=rr / len(items))
        log('%-10s R@1 %4.1f  R@5 %4.1f  R@10 %4.1f  MRR %.3f' % (name, res['r1'], res['r5'], res['r10'], res['mrr']))
        return res

    best = (-1, None); hist = []; t = 0
    aud = {int(x) for x in args.audit_epochs.split(',') if x}
    for ep in range(args.epochs):
        if aud: ar.audit = (ep + 1) in aud
        order = rng.permutation(train)
        if args.limit: order = order[:args.limit]
        if args.opt == 'adam':
            for gq_ in opt.param_groups: gq_['lr'] = args.lr * (1 - 0.9 * ep / args.epochs)
        tl = 0.0; nb = 0; t0 = time.time(); nn_ = 0
        for s in range(0, len(order) - args.queries + 1, args.queries):
            l, grads, nodes, stm = loss_and_grads(order[s:s + args.queries]); tl += l; nb += 1; nn_ += nodes
            if args.opt == 'adam':
                for k, v in P.items(): v.grad = grads[k].to(v.dtype)
                opt.step()
            else:
                sign_update(grads, t)
            ar.flush()
            t += 1
            if t in (1, 10): log('step %d  loss %.4f  %.2fs/step' % (t, l, (time.time() - t0) / nb))
            if not math.isfinite(l): log('loss is not finite'); break
        st = ar.st
        extra = ''
        if ar.audit:
            extra = '  peak sum 2^%.1f  dH 2^%.1f  grad 2^%.1f  7m+g 2^%.1f  |p| 2^%.1f (%s)' % (tuple(
                math.log2(max(x, 1)) for x in (ar.peak, st['dH'], st['gw'], st['m'], st['p'])) + (ar.peak_at,))
        log('epoch %d  loss %.5f  %.2fs/step  %.0f nodes/step  clamped %.4f%%  head clamped %.4f%%  Econst rows touched %.3f  |q| %.2f |p| %.2f%s' % (
            ep + 1, tl / nb, (time.time() - t0) / nb, nn_ / nb, 100 * st['clamped'] / max(st['vals'], 1),
            100 * st['hclamped'] / max(st['hvals'], 1), float(moved['rows_touched']) / max(moved['n'], 1), float(st.get('qn', 0)), float(st.get('pn', 0)), extra))
        if (ep + 1) % args.eval_every and ep + 1 != args.epochs: continue
        Pm = embed(lib_u, 'Ap')
        v = evaluate(val, Pm, 'validation'); tres = evaluate(test, Pm, 'test'); ar.flush()
        hist.append(dict(ep=ep + 1, val=v, test=tres, loss=tl / nb))
        if v['r10'] > best[0]: best = (v['r10'], (ep + 1, v, tres))
    ep, v, tres = best[1]
    log('selected epoch %d by validation R@10 %.1f (MRR %.3f): test R@1 %.1f R@5 %.1f R@10 %.1f MRR %.3f' % (
        ep, v['r10'], v['mrr'], tres['r1'], tres['r5'], tres['r10'], tres['mrr']))
    st = {k: float(v) for k, v in ar.st.items()}; st.update(peak=ar.peak, peak_at=ar.peak_at, audited_steps=ar.nsteps,
                                                         checks=ar.nchecks, peaks={k: math.log2(max(v, 1)) for k, v in ar.qpeak.items()})
    log('audited steps %d, checks %d, none fired' % (ar.nsteps, ar.nchecks))
    for k in sorted(ar.qpeak, key=lambda k: -ar.qpeak[k])[:40]: log('  peak bound %-28s 2^%.1f' % (k, math.log2(max(ar.qpeak[k], 1))))
    if args.save:
        integer = 'u' in ar.fl
        torch.save({'args': vars(args), 'integer': integer, 'grids': {'weights': WS, 'momentum': gridm},
                    'params': {k: (torch.round(v.detach() * 2.0 ** WS).to(torch.int64) if integer else v.detach()).cpu() for k, v in P.items()},
                    'momentum': {k: (torch.round(v * 2.0 ** gridm).to(torch.int64) if integer else v).cpu() for k, v in Mom.items()},
                    'slots': enc.slot.cpu(), 'steps': t}, args.save)
        log('saved', args.save)
    with open(args.results, 'a') as f:
        f.write(json.dumps(dict(name=args.name, args=vars(args), epoch=ep, val=v, test=tres, hist=hist, stats=st,
                                rows_touched=float(moved['rows_touched']) / max(moved['n'], 1))) + '\n')


if __name__ == '__main__':
    main()
