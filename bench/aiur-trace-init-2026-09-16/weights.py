#!/usr/bin/env python3
"""Per-circuit host witness time and rows from an AIUR_PROFILE span file of an
Init proof, joined with the static seed inventory of the IxVM program.

usage: weights.py spans.jsonl report-ixvm.json [top]
"""
import json
import sys
from collections import defaultdict


def union(intervals):
    total, cur = 0, None
    for a, b in sorted(intervals):
        if cur is None:
            cur = [a, b]
        elif a <= cur[1]:
            cur[1] = max(cur[1], b)
        else:
            total += cur[1] - cur[0]
            cur = [a, b]
    if cur:
        total += cur[1] - cur[0]
    return total / 1e9


def main():
    spans, report = sys.argv[1], sys.argv[2]
    top = int(sys.argv[3]) if len(sys.argv) > 3 else 30
    program = json.load(open(report))["programs"][0]
    functions = {f["index"]: f for f in program["functions"]}
    circuits = {c["index"]: c for c in program["circuits"]}
    meta, enter, cpu, seeds, rows = {}, {}, defaultdict(list), defaultdict(list), defaultdict(int)
    for line in open(spans):
        e = json.loads(line)
        i = e["id"]
        if e["event"] == "new" and e["name"] in ("aiur/cpu_circuit", "aiur/codegen_seeds"):
            f = e["fields"]
            meta[i] = (e["name"], int(f["circuit"]), int(f.get("rows", 0)), str(f.get("kind", "")))
        elif e["event"] == "enter" and i in meta:
            enter[i] = e["ts_ns"]
        elif e["event"] == "exit" and i in enter:
            name, c, r, kind = meta[i]
            (cpu if name == "aiur/cpu_circuit" else seeds)[(c, kind)].append((enter.pop(i), e["ts_ns"]))
            rows[(c, kind)] += r
    print("| Circuit | Kind | Rows, M | Host witness s | Seed prep s | Row bytes | Canonical | Typed | Typed / row |")
    print("| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
    keys = sorted(set(cpu) | set(seeds), key=lambda k: -(union(cpu.get(k, [])) + union(seeds.get(k, []))))
    for c, kind in keys[:top]:
        circuit = circuits.get(c)
        if circuit is None or "function" not in kind and kind != "":
            name = f"{kind.strip(chr(34))} {c}"
            row_bytes = canonical = typed = ""
            ratio = ""
        else:
            members = [functions[m["function"]] for m in circuit["members"]]
            name = circuit["name"] + (f" ({len(members)} members)" if len(members) > 1 else "")
            row_bytes = circuit["layout"]["main_width"] * 8
            canonical = sum(f["canonical_seed_bytes"] for f in members) // len(members)
            typed = sum(f["typed_seed_bytes"] for f in members) // len(members)
            ratio = f"{typed / row_bytes:.2f}"
        print(f"| {c} `{name}` | {kind.strip(chr(34)) or 'generated'} | {rows[(c, kind)] / 1e6:.1f} | "
              f"{union(cpu.get((c, kind), [])):.1f} | {union(seeds.get((c, kind), [])):.1f} | {row_bytes} | {canonical} | {typed} | {ratio} |")


if __name__ == "__main__":
    main()
