"""Least-squares estimators shared by the Aiur and Zisk cost models.

Two regimes show up across the benchmarks:
  * profiled features -> cost   (predict FFT / cycles from cheap counters)
  * cost -> runtime/RAM         (predict time / throughput / RAM from cost)

Costs span several orders of magnitude, so fits minimise *relative* error
(WLS with 1/y^2 weights) and we also expose a log-log power-law fit.
"""
import math


def nlogn(x: float) -> float:
    """`x * log2(x)` feature — the natural form for Aiur FFT (= sum w*h*log2 h)."""
    return x * math.log2(x + 2.0)


def _solve(A, b):
    n = len(A)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for i in range(n):
        piv = max(range(i, n), key=lambda r: abs(M[r][i]))
        M[i], M[piv] = M[piv], M[i]
        d = M[i][i]
        if abs(d) < 1e-300:
            raise ValueError("singular normal matrix")
        M[i] = [v / d for v in M[i]]
        for r in range(n):
            if r != i:
                f = M[r][i]
                M[r] = [a - f * c for a, c in zip(M[r], M[i])]
    return [M[i][n] for i in range(n)]


def wls(feature_cols, y, relative=True, intercept=True):
    """Weighted least squares. `feature_cols` is a list of equal-length columns.

    Returns dict(coef, r2 (weighted), mape (%), pred). With `relative`, weights
    are 1/y^2 so the fit targets relative error (right for multi-decade costs).
    """
    n = len(y)
    p = len(feature_cols) + (1 if intercept else 0)
    rows = [[col[i] for col in feature_cols] + ([1.0] if intercept else []) for i in range(n)]
    w = [1.0 / (v * v) if (relative and v) else 1.0 for v in y]
    A = [[sum(w[i] * rows[i][j] * rows[i][k] for i in range(n)) for k in range(p)] for j in range(p)]
    c = [sum(w[i] * rows[i][j] * y[i] for i in range(n)) for j in range(p)]
    coef = _solve(A, c)
    pred = [sum(coef[j] * rows[i][j] for j in range(p)) for i in range(n)]
    ybar = sum(w[i] * y[i] for i in range(n)) / sum(w)
    sst = sum(w[i] * (y[i] - ybar) ** 2 for i in range(n))
    ssr = sum(w[i] * (y[i] - pred[i]) ** 2 for i in range(n))
    mape = sum(abs(pred[i] - y[i]) / y[i] for i in range(n) if y[i]) / n * 100
    return dict(coef=coef, r2=(1 - ssr / sst if sst else 0.0), mape=mape, pred=pred)


def loglog(x, y):
    """Power-law fit y = a * x^b by OLS in log space. Returns (a, b, r2_log)."""
    lx = [math.log(v) for v in x]
    ly = [math.log(v) for v in y]
    n = len(x)
    sx, sy = sum(lx), sum(ly)
    sxx = sum(v * v for v in lx)
    sxy = sum(a * b for a, b in zip(lx, ly))
    b = (n * sxy - sx * sy) / (n * sxx - sx * sx)
    a = (sy - b * sx) / n
    yb = sy / n
    sst = sum((v - yb) ** 2 for v in ly)
    ssr = sum((ly[i] - (a + b * lx[i])) ** 2 for i in range(n))
    return math.exp(a), b, (1 - ssr / sst if sst else 0.0)
