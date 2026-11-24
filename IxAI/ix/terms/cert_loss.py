"""A multi-positive softmax retrieval loss whose forward scores and gradient
use only add, multiply, compare, shift and clamp, over embeddings normalised
to unit length by a Newton inverse square root.

All quantities are fixed point; `rnd(x, k)` rounds x to the grid 2^-k with
ties up, which in integer units is `(X + 2^(j-1)) >> j`. With `exact=False`
every rounding is skipped (the unrounded twin of the same algorithm). Under
an audit every rounding first checks that its operand lies on the grid the
exact product lives on and is below 2^52 there. Grids, for head outputs q on
2^-12 with |q_j| <= 8:

  ssq   = sum_j q_j^2                                   2^-24, < 2^13
  e     = floor((bitlen(ssq) - 1) / 2) in grid terms, x = ssq 2^-2e in [1, 4)
  x     rounded to 2^-24
  y0    = A - B x,  A = 1.1, B = 0.15 on 2^-16           2^-24
  y    <- y (3 - x y^2) / 2, three times                 2^-24 after each product
  inv   = rnd(y 2^-e, 24)                                ~ 1 / |q|
  qh    = rnd(q inv, 14)                                 unit rows, |qh_j| <= 1
  s     = qh . ph                                        2^-28, |s| <~ 1
  t     = rnd(C s, 16), C = 43 (= 30 log2 e)             base-2 logits
  u     = min(t - max over the query's negatives, 24)   negatives <= 0
  2^u   = (1 + f (a1 + a2 f)) shifted by floor(u), f = u - floor(u),
          a1 = 43267 / 2^16, a2 = 22269 / 2^16            2^-24
  Z     = 2^u(+) + sum over negatives 2^u                2^-24, in [1, 2^25 + 2^11)
  1/Z   : Z = m 2^b with m in [1/2, 1); r0 = 48/17 - 32/17 m, r <- r (2 - m r)
          three times; 1/Z = r 2^-b                       2^-24
  w     = 1/#positives (same reciprocal) / 2^9
  dt(+) = w (2^u(+) / Z - 1),  dt(n) = sum_+ w 2^u(n) / Z, rounded to 2^-GD
  dS    = C dt
and back through the normalisation dq = inv (dqh - qh (qh . dqh)).

Bound on dS^T qh: every query's row of dt has absolute sum at most
2 / 2^9 (the positive terms sum to at most sum_+ w = 2^-9, and the negative
terms to sum_+ w N / Z <= 2^-9), so a column of dS summed over 512 queries is
below 512 * 43 * 2^-8 = 86 < 2^6.43, and with |qh| <= 1 every partial sum of
dS^T qh is below 2^(6.43 + GD + 14) = 2^50.4 in units of 2^-(GD + 14).
"""
import torch

A_ISQ, B_ISQ = 72090 / 65536, 9830 / 65536          # 1.1, 0.15 on 2^-16
A1, A2 = 43267 / 65536, 22269 / 65536                # 2^f ~ 1 + f (A1 + A2 f), exact at f = 0, 1
C_LOGIT = 43
R48, R32 = round(48 / 17 * 2 ** 24) / 2 ** 24, round(32 / 17 * 2 ** 24) / 2 ** 24
GD = 30                                              # grid of the score gradient
UMAX = 24                                            # logits more than 24 above the largest negative are capped
EMAX = 6                                             # largest e of a head row: ssq < 2^13


class Fixed:
    def __init__(self, exact, audit=None):
        self.exact = exact; self.audit = audit       # audit: an `Arith` that records checks

    def r(self, x, k, gin=None, what=''):
        """x rounded to 2^-k; under audit x must lie on 2^-gin below 2^52 there."""
        if not self.exact: return x
        if self.audit is not None and self.audit.audit and gin is not None:
            self.audit.on_grid(x, gin, 'loss pre-round ' + what)
        return torch.floor(x * 2.0 ** k + 0.5) * 2.0 ** -k

    def chk(self, x, k, what):
        if self.exact and self.audit is not None and self.audit.audit:
            self.audit.on_grid(x, k, 'loss ' + what)
        return x

    def mm(self, A, B, ga, gb, what):
        if self.exact and self.audit is not None:
            return self.audit.mm(A, B, ga if self.audit.audit else None, gb, what)
        return A @ B

    def rowdot(self, A, B, ga, gb, what):
        """Row-wise dot products with a partial-sum bound under audit."""
        if self.exact and self.audit is not None and self.audit.audit:
            self.audit.on_grid(A, ga, what + ' left'); self.audit.on_grid(B, gb, what + ' right')
            self.audit.bounds.append(((A.abs() * B.abs()).sum(1).max() * 2.0 ** (ga + gb), what))
        return (A * B).sum(1)


def exp2_scale(x, dt):
    from encoder_cert import p2
    return p2(x, dt)


def frexp_exp(z):
    return torch.frexp(z).exponent.long()


def inv_sqrt_norm(q, fx):
    """Unit rows and the inverse norms of the rows of q (grid 2^-12)."""
    dt = q.dtype
    fx.chk(q, 12, 'head output')
    ssq = fx.rowdot(q, q, 12, 12, 'ssq')
    e = torch.div(frexp_exp(ssq) - 1, 2, rounding_mode='floor')
    if fx.exact: assert int(e.max()) <= EMAX
    x = fx.r(ssq * exp2_scale(-2 * e, dt), 24, 24 + 2 * EMAX, 'x')
    zero = ssq == 0; x = torch.where(zero, torch.ones_like(x), x)
    y = fx.r(A_ISQ - B_ISQ * x, 24, 40, 'y0')
    for _ in range(3):
        y2 = fx.r(y * y, 24, 48, 'y2'); xy = fx.r(x * y2, 24, 48, 'xy')
        y = fx.r((y * (3 - xy)) * 0.5, 24, 49, 'newton isqrt')
    inv = torch.where(zero, torch.zeros_like(y), fx.r(y * exp2_scale(-e, dt), 24, 24 + EMAX, 'inv'))
    qh = fx.r(q * inv[:, None], 14, 36, 'q inv')
    return qh, inv


def norm_back(qh, inv, dqh, fx, G):
    dot = fx.r(fx.rowdot(qh, dqh, 14, G, 'norm dot'), G, 14 + G, 'norm dot')
    t = fx.r(qh * dot[:, None], G, 14 + G, 'norm proj')
    return fx.r((dqh - t) * inv[:, None], G, G + 24, 'norm back')


def recip(z, fx, bmax):
    """1/z = r 2^-b for 0 < z < 2^bmax on 2^-24, by three Newton steps on the mantissa."""
    dt = z.dtype
    b = frexp_exp(z)
    if fx.exact: assert int(b.max()) <= bmax
    m = fx.r(z * exp2_scale(-b, dt), 24, 24 + bmax, 'mantissa')
    r = fx.r(R48 - R32 * m, 24, 48, 'r0')
    for _ in range(3):
        mr = fx.r(m * r, 24, 48, 'mr'); r = fx.r(r * (2 - mr), 24, 48, 'newton recip')
    return r, b


def exp2_x(u, fx):
    """2^u for -60 <= u <= UMAX on 2^-16 (a shift of the polynomial by floor(u))."""
    fx.chk(u, 16, 'u')
    fl = torch.floor(u); f = u - fl
    P = 1 + fx.r(f * fx.r(A1 + fx.r(A2 * f, 24, 32, 'a2 f'), 24, 24, 'a1'), 24, 40, 'poly')
    fx.chk(P, 24, 'poly')
    return fx.r(P * exp2_scale(fl.long().clamp(min=-60), u.dtype), 24, None, 'shift')


def isoft(qh, ph, pq, pc, sq, sc, nq, fx):
    """Loss (for logging, natural log) and the gradient C dt in the scores."""
    dt = qh.dtype
    S = fx.mm(qh, ph.T, 14, 14, 'scores')
    t = fx.r(C_LOGIT * S, 16, 28, 't')
    excl = torch.zeros_like(t, dtype=torch.bool); excl[sq, sc] = True
    isneg = ~excl; isneg[pq, pc] = False
    M = t.masked_fill(~isneg, -1e9).max(1).values    # largest negative: N >= 1, Z >= 1
    u = (t - M[:, None]).clamp(min=-60, max=UMAX)
    E = exp2_x(u, fx).masked_fill(excl, 0)
    N = fx.chk((E * isneg).sum(1), 24, 'N')          # nonnegative terms: partial sums <= N
    Ep = E[pq, pc]; Z = Ep + N[pq]
    r, b = recip(Z, fx, UMAX + 2)
    npos = torch.bincount(pq, minlength=nq).to(dt)
    rn, bn = recip(npos[pq], fx, 12)
    assert nq & (nq - 1) == 0
    nqs = 2.0 ** -(nq.bit_length() - 1)
    w = fx.r(rn * exp2_scale(-bn, dt), 24, 36, 'w') * nqs     # 1 / #positives / nq, on 2^-33
    pr = fx.r(fx.r(Ep * exp2_scale(-b, dt), 24, 24 + UMAX + 2, 'Ep 2^-b') * r, 24, 48, 'p(+)')
    dS = torch.zeros_like(t)
    dS.index_put_((pq, pc), fx.r(w * (pr - 1), GD, 57, 'dt(+)'), accumulate=True)
    coef = torch.zeros(nq, device=t.device, dtype=dt).index_add_(
        0, pq, fx.r(w * fx.r(r * exp2_scale(-b, dt), 24, 24 + UMAX + 2, '1/Z'), GD, 57, 'w/Z'))
    fx.chk(coef, GD, 'coef')
    dS += fx.r(coef[:, None] * (E * isneg), GD, GD + 24, 'dt(n)')
    fx.chk(dS, GD, 'dt')
    loss = float((w * (torch.log(Z.clamp(min=1e-30)) - torch.log(Ep.clamp(min=1e-30)))).sum())
    return S, loss, C_LOGIT * dS
