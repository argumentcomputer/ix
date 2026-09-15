#!/usr/bin/env python3
"""Tabulate one lanes run's record sizes for the shard-count calibration.

    python3 summarize.py RUNDIR [--csv records.csv]

Reads RUNDIR/lanes.err (the `[lanes]` lines), RUNDIR/meta.txt and
RUNDIR/gpu.csv, and prints the per-unit record table, the calibration
summary the scheduler printed, the timeline, and the measured peaks.
"""
import argparse
import csv
import re
import statistics
from pathlib import Path

EXEC = re.compile(
    r"^\[lanes\] worker (\d+): (claim (\d+)|join (\d+)|root) executed in ([\d.]+)s, "
    r"record (\d+) B \(([\d.]+) GiB(?:, (\d+)% of its ([\d.]+) GiB cap)?\)")
PROVEN = re.compile(r"^\[lanes\] worker (\d+): (claim (\d+) proven|join (\d+) published|root proven) at \+(\d+)s")
OVER = re.compile(r"^\[lanes\] worker (\d+): (claim (\d+)|join (\d+)|root) reached (\d+) B, over its (\d+) B share")
GIB = 1 << 30


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("rundir", type=Path)
    ap.add_argument("--csv", type=Path)
    args = ap.parse_args()
    err = (args.rundir / "lanes.err").read_text().splitlines()
    rows, proven, over, other = [], {}, [], []
    for line in err:
        if (m := EXEC.match(line)):
            kind = "root" if m.group(2) == "root" else m.group(2).split()[0]
            ident = m.group(3) or m.group(4) or "root"
            rows.append(dict(kind=kind, id=ident, worker=int(m.group(1)),
                             exec_s=float(m.group(5)), bytes=int(m.group(6)),
                             pct_of_cap=int(m.group(8)) if m.group(8) else None,
                             cap_gib=float(m.group(9)) if m.group(9) else None))
        elif (m := PROVEN.match(line)):
            kind = "claim" if m.group(3) else "join" if m.group(4) else "root"
            ident = m.group(3) or m.group(4) or "root"
            proven[(kind, ident)] = int(m.group(5))
        elif (m := OVER.match(line)):
            over.append(line)
        elif line.startswith("[lanes] calibration") or line.startswith("[lanes] record budget") \
                or line.startswith("[lanes] root ") or " claims (" in line:
            other.append(line)
    for r in rows:
        r["proven_at_s"] = proven.get((r["kind"], r["id"]))
    if args.csv:
        with args.csv.open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0].keys()) if rows else ["kind"])
            w.writeheader(); w.writerows(rows)
    for kind in ("claim", "join", "root"):
        units = [r for r in rows if r["kind"] == kind]
        if not units:
            continue
        b = sorted(r["bytes"] / GIB for r in units)
        t = [r["exec_s"] for r in units]
        largest = max(units, key=lambda r: r["bytes"])
        print(f"{kind}s: {len(units)} measured; record GiB mean {statistics.fmean(b):.1f} "
              f"p50 {b[len(b)//2]:.1f} p90 {b[int(len(b)*0.9)-1 if len(b)>1 else 0]:.1f} "
              f"max {b[-1]:.1f} ({kind} {largest['id']}, worker {largest['worker']}); "
              f"exec s mean {statistics.fmean(t):.0f} max {max(t):.0f}")
    print(f"over-share reruns: {len(over)}")
    for line in over:
        print("  " + line)
    for line in other:
        print(line)
    print()
    print("largest 10 claim records:")
    for r in sorted((r for r in rows if r["kind"] == "claim"), key=lambda r: -r["bytes"])[:10]:
        print(f"  claim {r['id']:>4}  {r['bytes']/GIB:6.1f} GiB  {r['pct_of_cap'] or 0:3d}% of cap  exec {r['exec_s']:6.0f}s  worker {r['worker']}")
    meta = args.rundir / "meta.txt"
    if meta.exists():
        print()
        for line in meta.read_text().splitlines():
            if line.split(" ")[0] in ("started", "ended", "exit", "flags", "ix", "ixes"):
                print(line)
    gpu = args.rundir / "gpu.csv"
    if gpu.exists():
        peak = {}
        for line in gpu.read_text().splitlines():
            parts = [p.strip() for p in line.split(",")]
            if len(parts) < 4:
                continue
            try:
                idx, mem = int(parts[1]), int(parts[2].split()[0])
            except ValueError:
                continue
            peak[idx] = max(peak.get(idx, 0), mem)
        print("peak device memory MiB: " + ", ".join(f"gpu{i} {m}" for i, m in sorted(peak.items())))
    time_v = [l.strip() for l in err if "Maximum resident set size" in l or "Elapsed (wall clock)" in l]
    for line in time_v:
        print(line)


if __name__ == "__main__":
    main()
