#!/usr/bin/env python3
"""Summarize a kernel census (`kernel-census` JSONL output).

Usage: census-report.py <census.jsonl> [top]

Prints outcome counts, check time, decline reasons, and the root causes
ranked by how many records they block. A blocked row names the root record
whose failure it inherits (the census follows first causes transitively), so
ranking roots by blocked rows ranks the fixes by reach."""
import json
import sys
from collections import Counter, defaultdict

path = sys.argv[1]
top = int(sys.argv[2]) if len(sys.argv) > 2 else 30
rows = [json.loads(line) for line in open(path)]
by_address = {r["address"]: r for r in rows}

outcomes = Counter(r["outcome"] for r in rows)
print(f"records {len(rows)}: " + ", ".join(f"{k} {v}" for k, v in outcomes.most_common()))
# A recursor checked with its family repeats the pair's time on its own row.
timed = [r for r in rows if r.get("kind") != "recursor"]
accept_micros = sum(r["micros"] for r in timed if r["outcome"] == "accept")
all_micros = sum(r["micros"] for r in timed)
read_micros = sum(r.get("readMicros", 0) for r in rows)
print(f"check time: accepts {accept_micros / 1e6:.1f} s, all {all_micros / 1e6:.1f} s; "
      f"reading {read_micros / 1e6:.1f} s")

def name(r):
    return (r.get("names") or [r["address"][:16]])[0]

def group(reason):
    """Decline reasons with an instance-specific suffix, grouped."""
    for prefix in ("census: expanded term size exceeds",):
        if reason.startswith(prefix):
            return prefix
    return reason

reasons = Counter(group(r["reason"]) for r in rows if r["outcome"] in ("decline", "reject"))
print("\ndecline and reject reasons:")
for reason, count in reasons.most_common(top):
    print(f"  {count:6d}  {reason}")

blocked = Counter(r["reason"] for r in rows if r["outcome"] == "blocked")
reach = defaultdict(int)
for root, count in blocked.items():
    reach[root] += count
print(f"\nroots by blocked records (top {top}):")
for root, count in sorted(reach.items(), key=lambda kv: -kv[1])[:top]:
    r = by_address.get(root)
    if r is None:
        print(f"  {count:6d}  {root[:16]}  (not in this census)")
    else:
        print(f"  {count:6d}  {name(r)[:60]:60s}  {r['outcome']}: {group(r['reason'])[:70]}")

by_reason = defaultdict(int)
for root, count in reach.items():
    r = by_address.get(root)
    by_reason[group(r["reason"]) if r else "(outside)"] += count + 1
print("\nreach by root decline reason (roots plus the records they block):")
for reason, count in sorted(by_reason.items(), key=lambda kv: -kv[1])[:top]:
    print(f"  {count:6d}  {reason[:100]}")

slow = sorted((r for r in timed if r["outcome"] == "accept"), key=lambda r: -r["micros"])[:10]
print("\nslowest accepts:")
for r in slow:
    print(f"  {r['micros'] / 1e3:9.1f} ms  {name(r)[:80]}")
