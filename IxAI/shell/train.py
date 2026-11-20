#!/usr/bin/env python3
"""Untrusted trainer for the MLP specified in IxAI/Model.lean.

Nothing this script outputs is trusted. `ixai check` recomputes every step against the Lean
specification and rejects any trajectory that differs by a single bit. The script only has to be
fast and correct; it does not have to be believed.

Usage: train.py DATA_FILE OUT_FILE [--reverse-reductions] [--tamper STEP]

The numeric format (fx, bf16 or f32) is read from the data file's `format` line.
--reverse-reductions accumulates every sum (within dot products and across a batch) in the
opposite order. The specification accumulates exactly and rounds once, so nothing may change.
--tamper STEP perturbs one weight after the given step, to show that the checker notices.
"""

import sys

MASK = (1 << 64) - 1
REVERSE = False


def ordered(xs):
    return list(reversed(xs)) if REVERSE else list(xs)


class Rng:
    def __init__(self, seed):
        self.state = 0x9E3779B97F4A7C15 if seed == 0 else seed & MASK

    def next(self):
        x = self.state
        x ^= x >> 12
        x ^= (x << 25) & MASK
        x ^= x >> 27
        self.state = x
        return (x * 0x2545F4914F6CDD1D) & MASK

    def below(self, n):
        return self.next() % n


class Fx:
    """Fixed point with 8 fractional bits; values are raw integers."""

    zero = 0

    @staticmethod
    def of_int(n):
        return n << 8

    @staticmethod
    def of_scaled(n):
        return n

    @staticmethod
    def add(a, b):
        return a + b

    @staticmethod
    def sub(a, b):
        return a - b

    @staticmethod
    def mul(a, b):
        return (a * b) >> 8

    @staticmethod
    def dot(xs, ys):
        return sum(ordered([a * b for a, b in zip(xs, ys)])) >> 8

    @staticmethod
    def pos(a):
        return a > 0

    @staticmethod
    def wire(a):
        return a


def round_shift_right_even(n, s):
    if s <= 0:
        return n << -s
    q, rem, half = n >> s, n & ((1 << s) - 1), 1 << (s - 1)
    return q + 1 if rem > half or (rem == half and q & 1) else q


class Ieee:
    """IEEE binary format; values are bit patterns. Mirrors FloatLib's exact-dyadic specification:
    decode exactly, compute exactly, round once to nearest with ties to even."""

    def __init__(self, ew, fw):
        self.ew, self.fw = ew, fw
        self.bias = (1 << (ew - 1)) - 1
        self.emax_field = (1 << ew) - 1
        self.zero = 0

    def fields(self, neg, e, f):
        return (int(neg) << (self.ew + self.fw)) | (e << self.fw) | f

    def decode(self, b):
        neg = bool(b >> (self.ew + self.fw))
        e = (b >> self.fw) & self.emax_field
        f = b & ((1 << self.fw) - 1)
        if e == self.emax_field:
            raise ArithmeticError("non-finite value")
        if e == 0:
            return neg, f, 1 - self.bias - self.fw
        return neg, (1 << self.fw) + f, e - self.bias - self.fw

    def round(self, neg, sig, exp):
        fw = self.fw
        if sig == 0:
            return self.fields(neg, 0, 0)
        leading = sig.bit_length() - 1
        total = leading + exp
        if total < 1 - self.bias:
            frac = round_shift_right_even(sig, -(exp + self.bias - 1 + fw))
            if frac == 0:
                return self.fields(neg, 0, 0)
            if frac == 1 << fw:
                return self.fields(neg, 1, 0)
            return self.fields(neg, 0, frac)
        mant = round_shift_right_even(sig, leading - fw)
        if mant == 1 << (fw + 1):
            mant, total = 1 << fw, total + 1
        if total > self.bias:
            return self.fields(neg, self.emax_field, 0)
        return self.fields(neg, total + self.bias, mant - (1 << fw))

    @staticmethod
    def dadd(x, y):
        (nx, sx, ex), (ny, sy, ey) = x, y
        if sx == 0 and sy == 0:
            return nx and ny, 0, 0
        if sx == 0:
            return y
        if sy == 0:
            return x
        e = min(ex, ey)
        s = (-1 if nx else 1) * (sx << (ex - e)) + (-1 if ny else 1) * (sy << (ey - e))
        if s == 0:
            return nx and ny, 0, 0
        return s < 0, abs(s), e

    def of_int(self, n):
        return self.round(n < 0, abs(n), 0)

    def of_scaled(self, n):
        return self.round(n < 0, abs(n), -8)

    def add(self, a, b):
        return self.round(*self.dadd(self.decode(a), self.decode(b)))

    def sub(self, a, b):
        return self.add(a, b ^ (1 << (self.ew + self.fw)))

    def mul(self, a, b):
        (na, sa, ea), (nb, sb, eb) = self.decode(a), self.decode(b)
        if sa == 0 or sb == 0:
            return self.fields(na != nb, 0, 0)
        return self.round(na != nb, sa * sb, ea + eb)

    def dot(self, xs, ys):
        acc = (False, 0, 0)
        prods = []
        for a, b in zip(xs, ys):
            (na, sa, ea), (nb, sb, eb) = self.decode(a), self.decode(b)
            prods.append((na != nb, sa * sb, ea + eb))
        for p in ordered(prods):
            acc = self.dadd(acc, p)
        return self.round(*acc)

    def pos(self, a):
        neg, sig, _ = self.decode(a)
        return not neg and sig != 0

    @staticmethod
    def wire(a):
        return a


FORMATS = {"fx": lambda: Fx, "bf16": lambda: Ieee(8, 7), "f32": lambda: Ieee(8, 23)}


def init(cfg, n_features, num):
    r = Rng(cfg["seed"] ^ 0x494E4954)
    h = cfg["hidden"]
    p = [num.of_scaled(r.below(33) - 16) for _ in range(h * n_features + 2 * h + 1)]
    w1 = [p[j * n_features:(j + 1) * n_features] for j in range(h)]
    rest = p[h * n_features:]
    return {"w1": w1, "b1": rest[:h], "w2": rest[h:2 * h], "b2": rest[2 * h]}


def shuffle(n, r):
    a = list(range(n))
    for i in range(n - 1, 0, -1):
        j = r.below(i + 1)
        a[i], a[j] = a[j], a[i]
    return a


def schedule(cfg, n):
    r = Rng(cfg["seed"] ^ 0x53434844)
    bs = cfg["batch"]
    out = []
    for _ in range(cfg["epochs"]):
        perm = shuffle(n, r)
        for b in range((n + bs - 1) // bs):
            out.append(perm[b * bs:(b + 1) * bs])
    return out


def delta(num, m, x, t):
    z = [num.add(num.dot(row, x), b) for row, b in zip(m["w1"], m["b1"])]
    h = [v if num.pos(v) else num.zero for v in z]
    dy = num.sub(num.add(num.dot(m["w2"], h), m["b2"]), t)
    dz = [num.mul(dy, w) if num.pos(zj) else num.zero for w, zj in zip(m["w2"], z)]
    return x, h, dz, dy


def step(num, lr, m, batch):
    if not batch:
        return m
    ds = ordered([delta(num, m, x, t) for x, t in batch])
    one = num.of_int(1)
    dys = [d[3] for d in ds]

    def col(i, j):
        return [d[i][j] for d in ds]

    def upd(w, g):
        return num.sub(w, num.mul(lr, g))

    return {
        "w1": [[upd(w, num.dot(col(2, j), col(0, k))) for k, w in enumerate(row)]
               for j, row in enumerate(m["w1"])],
        "b1": [upd(b, num.dot(col(2, j), [one] * len(ds))) for j, b in enumerate(m["b1"])],
        "w2": [upd(w, num.dot(dys, col(1, j))) for j, w in enumerate(m["w2"])],
        "b2": upd(m["b2"], num.dot(dys, [one] * len(ds))),
    }


def params(m):
    return [p for row in m["w1"] for p in row] + m["b1"] + m["w2"] + [m["b2"]]


def main():
    global REVERSE
    args = sys.argv[1:]
    REVERSE = "--reverse-reductions" in args
    tamper = int(args[args.index("--tamper") + 1]) if "--tamper" in args else None
    data_path, out_path = [a for a in args if not a.startswith("--") and not a.isdigit()][:2]

    header, raw_items, fmt = [], [], "fx"
    for line in open(data_path):
        w = line.split()
        if not w:
            continue
        if w[0] in ("config", "data", "format"):
            header.append(line.rstrip("\n"))
            if w[0] == "config":
                cfg = dict(zip(["seed", "hidden", "lr", "epochs", "batch", "bound"],
                               map(int, w[1:])))
            if w[0] == "format":
                fmt = w[1]
        elif w[0] == "item":
            raw_items.append((int(w[1]), [int(v) for v in w[2:]]))

    num = FORMATS[fmt]()
    items = [([num.of_int(f) for f in feats], num.of_int(1 if label else -1))
             for label, feats in raw_items]
    lr = num.of_scaled(cfg["lr"])
    m = init(cfg, len(items[0][0]), num)
    out = list(header)
    for i, idx in enumerate(schedule(cfg, len(items))):
        m = step(num, lr, m, [items[k] for k in idx])
        if tamper == i:
            m["w2"][0] ^= 1
        out.append("step " + " ".join(map(str, idx)))
        out.append("w " + " ".join(str(num.wire(p)) for p in params(m)))
    with open(out_path, "w") as f:
        f.write("\n".join(out) + "\n")
    print(f"wrote {(len(out) - len(header)) // 2} steps ({fmt})")


if __name__ == "__main__":
    main()
