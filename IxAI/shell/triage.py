#!/usr/bin/env python3
"""Untrusted reimplementation of the formula-triage decision model (IxAICore/Triage.lean).

It regenerates the dataset from the seed, computes every label with the same decision procedures,
and trains with the same arithmetic. If the specification is deterministic, its final weights
equal those of compiled Lean and those IxVM computes inside an Ix proof, bit for bit.

Usage: triage.py SIZE [--reverse-reductions]
Prints the trained parameters, one line per tensor, in the order of `ixai weights SIZE`.
--reverse-reductions sums every dot product and batch gradient in the opposite order.
"""

import sys

M64 = (1 << 64) - 1
REVERSE = False

CONFIGS = {
    "tiny": dict(seed=42, hidden=4, lr=2, epochs=1, batch=8, train=16, test=16),
    "small": dict(seed=42, hidden=8, lr=2, epochs=2, batch=16, train=64, test=32),
    "full": dict(seed=42, hidden=16, lr=2, epochs=30, batch=20, train=400, test=200),
}


def ordered(xs):
    return list(reversed(xs)) if REVERSE else list(xs)


class Rng:
    def __init__(self, seed):
        self.state = 11400714819323198485 if seed & M64 == 0 else seed & M64

    def next(self):
        x = self.state
        x ^= x >> 12
        x = (x ^ (x << 25)) & M64
        x ^= x >> 27
        self.state = x
        return (x * 2685821657736338717) & M64

    def below(self, n):
        return self.next() % n


# Formulas: ("atom", n) | ("top",) | ("imp", a, b) | ("and", a, b)

def gen(d, r):
    if d == 0:
        k = r.below(4)
        return ("top",) if k == 3 else ("atom", k)
    k = r.below(5)
    a = gen(d - 1, r)
    b = gen(d - 1, r)
    return a if k < 2 else ("and", a, b) if k == 4 else ("imp", a, b)


def ev(f, v):
    t = f[0]
    if t == "atom":
        return v(f[1])
    if t == "top":
        return True
    if t == "imp":
        return (not ev(f[1], v)) or ev(f[2], v)
    return ev(f[1], v) and ev(f[2], v)


def models(f):
    return sum(1 for bits in range(8) if ev(f, lambda n: (bits >> n) % 2 == 1))


def size(f):
    return f[0] in ("imp", "and") and size(f[1]) + size(f[2]) + 1 or 1


def depth(f):
    return max(depth(f[1]), depth(f[2])) + 1 if f[0] in ("imp", "and") else 0


def atom_count(k, f):
    if f[0] == "atom":
        return 1 if f[1] == k else 0
    if f[0] in ("imp", "and"):
        return atom_count(k, f[1]) + atom_count(k, f[2])
    return 0


def imp_count(f):
    if f[0] == "imp":
        return imp_count(f[1]) + imp_count(f[2]) + 1
    if f[0] == "and":
        return imp_count(f[1]) + imp_count(f[2])
    return 0


def head(f):
    return head(f[2]) if f[0] == "imp" else f


def head_assumed(f):
    return f[0] == "imp" and (f[1] == head(f[2]) or head_assumed(f[2]))


def features(f):
    return [atom_count(0, f), atom_count(1, f), atom_count(2, f), imp_count(f), size(f), depth(f),
            1 if head_assumed(f) else 0, 1 if head(f) == ("top",) else 0]


def targets(f):
    m = models(f)
    valid = 1 if m == 8 else 0
    h = head(f)
    hd = h[1] if h[0] == "atom" and h[1] < 3 else 3 if h == ("top",) else 4
    cov = 0 if m == 0 else 1 if m < 4 else 2 if m < 8 else 3
    onehot = lambda k, n: [256 if i == k else 0 for i in range(n)]
    return onehot(valid, 2) + onehot(hd, 5) + onehot(cov, 4)


def dot(a, b):
    return sum(ordered([x * y for x, y in zip(a, b)])) >> 8


def mul(a, b):
    return (a * b) >> 8


def shuffle(n, r):
    a = list(range(n))
    for k in range(n - 1, 0, -1):
        j = r.below(k + 1)
        a[k], a[j] = a[j], a[k]
    return a


def schedule(c):
    r = Rng(c["seed"] + 7)
    out = []
    for _ in range(c["epochs"]):
        perm = shuffle(c["train"], r)
        out += [perm[i:i + c["batch"]] for i in range(0, len(perm), c["batch"])]
    return out


def init(c, n_in, n_out):
    h = c["hidden"]
    r = Rng(c["seed"] + 3)
    ws = [r.below(33) - 16 for _ in range(h * n_in + h + n_out * h + n_out)]
    w1 = [ws[j * n_in:(j + 1) * n_in] for j in range(h)]
    b1 = ws[h * n_in:h * n_in + h]
    base = h * n_in + h
    w2 = [ws[base + k * h:base + (k + 1) * h] for k in range(n_out)]
    b2 = ws[base + n_out * h:base + n_out * h + n_out]
    return w1, b1, w2, b2


def delta(m, x, t):
    w1, b1, w2, b2 = m
    z = [dot(row, x) + b for row, b in zip(w1, b1)]
    h = [v if v > 0 else 0 for v in z]
    o = [dot(row, h) + b for row, b in zip(w2, b2)]
    dout = [oi - ti for oi, ti in zip(o, t)]
    dz = [dot([row[j] for row in w2], dout) if z[j] > 0 else 0 for j in range(len(z))]
    return x, h, dz, dout


def step(lr, m, batch):
    if not batch:
        return m
    w1, b1, w2, b2 = m
    ds = ordered([delta(m, x, t) for x, t in batch])
    col = lambda i, j: [d[i][j] for d in ds]
    upd = lambda w, g: w - mul(lr, g)
    return (
        [[upd(w, dot(col(2, j), col(0, i))) for i, w in enumerate(row)] for j, row in enumerate(w1)],
        [upd(b, sum(ordered(col(2, j)))) for j, b in enumerate(b1)],
        [[upd(w, dot(col(3, k), col(1, j))) for j, w in enumerate(row)] for k, row in enumerate(w2)],
        [upd(b, sum(ordered(col(3, k)))) for k, b in enumerate(b2)],
    )


def main():
    global REVERSE
    REVERSE = "--reverse-reductions" in sys.argv
    c = CONFIGS[sys.argv[1]]
    r = Rng(c["seed"])
    data = [gen(3, r) for _ in range(c["train"])]
    examples = [([v * 256 for v in features(f)], targets(f)) for f in data]
    m = init(c, 8, 11)
    for idx in schedule(c):
        m = step(c["lr"], m, [examples[i] for i in idx])
    w1, b1, w2, b2 = m
    print("w1 " + " ".join(str(v) for row in w1 for v in row))
    print("b1 " + " ".join(map(str, b1)))
    print("w2 " + " ".join(str(v) for row in w2 for v in row))
    print("b2 " + " ".join(map(str, b2)))


if __name__ == "__main__":
    main()
