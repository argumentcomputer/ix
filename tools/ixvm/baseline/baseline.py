#!/usr/bin/env python3
"""IxVM cost baseline: extract per-case, per-circuit and per-function costs from
`ixvm-proof test --stats-out` sidecars, and diff two baselines.

  baseline.py extract OUTDIR LOG [LOG ...] > BASE.json
      OUTDIR is searched recursively for `*.stats.json` sidecars (and their
      `*.stats.json.functions.json` companions, written when the host runs with
      IXVM_FUNCTION_STATS=1). Each LOG is scanned for the harness's
      `FFT <label>: <cost> (expected ...)` lines, which are authoritative for a
      case's total; the per-circuit costs are recomputed here with the formula of
      `Ix/Aiur/Statistics.lean` (`fftCost`), and their sum is checked against the
      logged total.
  baseline.py diff OLD.json NEW.json [--top N]
      Every label's total in both, the labels in one only, sums by suite, and for
      the N labels that moved most, the circuits (and functions) that moved most.
  baseline.py show BASE.json LABEL [--top N]
      One case's largest circuits and functions.

Costs are FFT-work units (`roundedFftCost`). No third-party modules.
"""
import json
import math
import os
import re
import sys

FFT_LINE = re.compile(r"^FFT (.*): (\d+) \(expected [^)]*\)\s*$")


def transform(x):
    return 0.0 if x == 0 else x * math.log2(max(x, 2))


def circuit_cost(c, log_blowup, ext):
    h = c["rows"]
    w = c["stage1_width"] + c["stage2_width"]
    q = c["quotient_degree"]
    b = 2 ** log_blowup
    return (b + 1) * w * transform(h) + ext * transform(q * h) + q * ext * transform(b * h)


def extract(outdir, logs):
    totals = {}
    for log in logs:
        with open(log, errors="replace") as f:
            for line in f:
                m = FFT_LINE.match(line.rstrip("\n"))
                if m:
                    totals[m.group(1)] = int(m.group(2))
    names, index, cases = [], {}, {}
    for root, _, files in os.walk(outdir):
        for fn in sorted(files):
            if not fn.endswith(".stats.json"):
                continue
            path = os.path.join(root, fn)
            with open(path) as f:
                data = json.load(f)
            fpath = path + ".functions.json"
            fdata = {}
            if os.path.exists(fpath):
                with open(fpath) as f:
                    fdata = json.load(f)
            for label, m in data.items():
                ext = m.get("extension_degree", 3)
                lb = m["log_blowup"]
                circuits, total, rows = {}, 0.0, 0
                for c in m["circuits"]:
                    cost = circuit_cost(c, lb, ext)
                    total += cost
                    if c["rows"] == 0:
                        continue
                    i = index.get(c["name"])
                    if i is None:
                        i = index[c["name"]] = len(names)
                        names.append(c["name"])
                    circuits[str(i)] = [c["rows"], c["cache_hits"], round(cost)]
                    rows += c["rows"]
                case = {"fft": totals.get(label), "fft_model": round(total), "rows": rows,
                        "circuits": circuits, "file": os.path.relpath(path, outdir)}
                if label in fdata:
                    case["functions"] = {e["name"]: [e["rows"], e["cache_hits"]] for e in fdata[label]}
                if label in cases:
                    raise SystemExit(f"label twice: {label}")
                cases[label] = case
    for label, total in totals.items():
        if label not in cases:
            cases[label] = {"fft": total, "fft_model": None, "rows": None, "circuits": {}, "file": None}
    bad = [l for l, c in cases.items()
           if c["fft"] is not None and c["fft_model"] is not None and abs(c["fft"] - c["fft_model"]) > 1]
    for l in bad:
        print(f"warning: {l}: logged {cases[l]['fft']} but sidecar gives {cases[l]['fft_model']}",
              file=sys.stderr)
    json.dump({"circuits": names, "cases": cases}, sys.stdout, sort_keys=True)
    print(f"extracted {len(cases)} cases, {len(totals)} logged totals, {len(names)} circuits, "
          f"{len(bad)} disagreements", file=sys.stderr)


def total(c):
    return c["fft"] if c["fft"] is not None else c["fft_model"]


def suite(label):
    for p in ("eval ", "check ", "binding ", "shard ", "s4 decl ", "s4 decl-ind ", "s4 decl-rec ",
              "s4 check ", "s4 std ", "s4 model "):
        if label.startswith(p):
            return p.strip()
    return "other"


def by_name(base, case):
    return {base["circuits"][int(i)]: v for i, v in case["circuits"].items()}


def short(name, n=90):
    return name if len(name) <= n else name[: n - 3] + "..."


def diff(old_path, new_path, top):
    with open(old_path) as f:
        old = json.load(f)
    with open(new_path) as f:
        new = json.load(f)
    oc, nc = old["cases"], new["cases"]
    common = sorted(set(oc) & set(nc))
    only_old = sorted(set(oc) - set(nc))
    only_new = sorted(set(nc) - set(oc))
    moved = [(l, total(oc[l]), total(nc[l])) for l in common if total(oc[l]) != total(nc[l])]
    print(f"cases: {len(common)} in both, {len(moved)} moved, {len(only_old)} only in old, "
          f"{len(only_new)} only in new")
    sums = {}
    for l in common:
        s = sums.setdefault(suite(l), [0, 0, 0])
        s[0] += total(oc[l]) or 0
        s[1] += total(nc[l]) or 0
        s[2] += 1
    print("\nsums by suite (old -> new, ratio):")
    for k, (a, b, n) in sorted(sums.items()):
        r = b / a if a else float("nan")
        print(f"  {k:10s} {n:4d} cases  {a:.4e} -> {b:.4e}  x{r:.4f}")
    if moved:
        print("\nmoved cases (largest absolute change first):")
        for l, a, b in sorted(moved, key=lambda t: -abs((t[2] or 0) - (t[1] or 0))):
            r = b / a if a else float("nan")
            print(f"  {a:>16} -> {b:>16}  x{r:.4f}  {l}")
    for l in only_old:
        print(f"  only in old: {l} ({total(oc[l])})")
    for l in only_new:
        print(f"  only in new: {l} ({total(nc[l])})")
    for l, a, b in sorted(moved, key=lambda t: -abs((t[2] or 0) - (t[1] or 0)))[:top]:
        print(f"\n== {l}: {a} -> {b}")
        co, cn = by_name(old, oc[l]), by_name(new, nc[l])
        rows = []
        for name in set(co) | set(cn):
            ro, ho, ko = co.get(name, [0, 0, 0])
            rn, hn, kn = cn.get(name, [0, 0, 0])
            if (ro, ko) != (rn, kn):
                rows.append((kn - ko, rn - ro, ro, rn, name))
        for dk, dr, ro, rn, name in sorted(rows, key=lambda t: -abs(t[0]))[:top]:
            print(f"   cost {dk:+14d}  rows {ro:>11} -> {rn:>11}  {short(name)}")
        fo, fn = oc[l].get("functions"), nc[l].get("functions")
        if fo and fn:
            frows = []
            for name in set(fo) | set(fn):
                a1 = fo.get(name, [0, 0])[0]
                b1 = fn.get(name, [0, 0])[0]
                if a1 != b1:
                    frows.append((b1 - a1, a1, b1, name))
            for d, a1, b1, name in sorted(frows, key=lambda t: -abs(t[0]))[:top]:
                print(f"   fn rows {d:+12d}  {a1:>11} -> {b1:>11}  {short(name)}")


def show(base_path, label, top):
    with open(base_path) as f:
        base = json.load(f)
    c = base["cases"][label]
    print(f"{label}: fft {total(c)}, rows {c['rows']}")
    for name, (r, h, k) in sorted(by_name(base, c).items(), key=lambda t: -t[1][2])[:top]:
        print(f"  {k:>16}  rows {r:>11}  hits {h:>11}  {short(name)}")
    if c.get("functions"):
        print("  functions by rows:")
        for name, (r, h) in sorted(c["functions"].items(), key=lambda t: -t[1][0])[:top]:
            print(f"  rows {r:>11}  hits {h:>11}  {short(name)}")


def main(argv):
    if len(argv) >= 3 and argv[1] == "extract":
        extract(argv[2], argv[3:])
    elif len(argv) >= 4 and argv[1] == "diff":
        top = int(argv[5]) if len(argv) >= 6 and argv[4] == "--top" else 15
        diff(argv[2], argv[3], top)
    elif len(argv) >= 4 and argv[1] == "show":
        top = int(argv[5]) if len(argv) >= 6 and argv[4] == "--top" else 25
        show(argv[2], argv[3], top)
    else:
        print(__doc__, file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
