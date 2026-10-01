#!/usr/bin/env python3
"""Summarize a `kernel-check-ixe` JSONL run.

Reports outcome counts by declaration kind, first-cause decline/reject reasons,
and root blockers ranked by how many records they transitively block. A blocked
row's reason is the address of its root blocker, as the environment check writes it.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("jsonl", type=Path)
    parser.add_argument("--top", type=int, default=25)
    parser.add_argument("--json", type=Path, help="write the summary as JSON")
    args = parser.parse_args()

    rows = [json.loads(line) for line in args.jsonl.read_text().splitlines() if line.strip()]
    by_address = {row["address"]: row for row in rows}
    outcomes = Counter(row["outcome"] for row in rows)
    by_kind: dict[str, Counter] = defaultdict(Counter)
    for row in rows:
        by_kind[row["kind"]][row["outcome"]] += 1
    reasons = Counter(row["reason"].split(" (")[0] for row in rows
                      if row["outcome"] in ("decline", "reject"))
    blockers = Counter(row["reason"] for row in rows if row["outcome"] == "blocked")
    micros = sum(row["micros"] for row in rows)
    read_micros = sum(row.get("readMicros", 0) for row in rows)
    accepted = sorted(row["micros"] for row in rows if row["outcome"] == "accept")

    def quantile(q: float) -> float:
        return accepted[min(len(accepted) - 1, int(q * len(accepted)))] / 1e3 if accepted else 0.0

    slowest = sorted((row for row in rows if row["outcome"] != "blocked"),
                     key=lambda row: -row["micros"])[:10]

    total = len(rows)
    print(f"# Environment check of {args.jsonl.name}: {total} declaration rows\n")
    print("| Outcome | Records | Share |\n| --- | ---: | ---: |")
    for outcome, count in outcomes.most_common():
        print(f"| {outcome} | {count} | {100 * count / total:.1f}% |")
    print(f"\nSum of row timings: checking {micros / 1e6:.1f} s; "
          f"reading {read_micros / 1e6:.1f} s. "
          "Family/recursor rows repeat admission timings; these are not wall times.")
    if accepted:
        top = sum(row["micros"] for row in slowest)
        print(f"Accepted row time: median {quantile(0.5):.2f} ms, p90 {quantile(0.9):.2f} ms, "
              f"p99 {quantile(0.99):.1f} ms; the 10 slowest rows account for "
              f"{100 * top / max(micros, 1):.0f}% of summed checking time\n")
    else:
        print()
    print("| Kind | accept | decline | reject | blocked |\n| --- | ---: | ---: | ---: | ---: |")
    for kind, counts in sorted(by_kind.items(), key=lambda kv: -sum(kv[1].values())):
        print(f"| {kind} | {counts['accept']} | {counts['decline']} | {counts['reject']} | {counts['blocked']} |")
    print(f"\n## First-cause reasons (top {args.top})\n")
    print("| Records | Reason |\n| ---: | --- |")
    for reason, count in reasons.most_common(args.top):
        print(f"| {count} | {reason} |")
    print(f"\n## Root blockers by records blocked (top {args.top})\n")
    print("| Blocked | Root | Kind | Outcome | Reason |\n| ---: | --- | --- | --- | --- |")
    top_blockers = []
    for address, count in blockers.most_common(args.top):
        root = by_address.get(address, {})
        name = ", ".join(root.get("names", [])[:2]) or address[:16]
        print(f"| {count} | {name} | {root.get('kind', '?')} | {root.get('outcome', '?')} | "
              f"{root.get('reason', '?')} |")
        top_blockers.append({"address": address, "blocked": count, **root})
    print("\n## Slowest row timings\n")
    print("| Seconds | Outcome | Kind | Name |\n| ---: | --- | --- | --- |")
    for row in slowest:
        name = ", ".join(row.get("names", [])[:1]) or row["address"][:16]
        print(f"| {row['micros'] / 1e6:.2f} | {row['outcome']} | {row['kind']} | {name} |")
    if args.json:
        args.json.write_text(json.dumps({
            "input": str(args.jsonl), "records": total, "outcomes": dict(outcomes),
            "byKind": {k: dict(v) for k, v in by_kind.items()},
            "reasons": reasons.most_common(), "rootBlockers": top_blockers,
            "checkingSeconds": micros / 1e6, "readingSeconds": read_micros / 1e6,
            "timingScope": "sum of row timings; paired admissions counted twice; not wall time",
            "acceptedMillis": {"median": quantile(0.5), "p90": quantile(0.9), "p99": quantile(0.99)},
            "slowest": [{"seconds": row["micros"] / 1e6, "names": row.get("names", [])[:1],
                         "outcome": row["outcome"]} for row in slowest]}, indent=1) + "\n")


if __name__ == "__main__":
    main()
