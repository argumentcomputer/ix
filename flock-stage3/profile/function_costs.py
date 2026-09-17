#!/usr/bin/env python3
"""Join a completed reference trace to the compiler's function inventory.

Counts are exclusive logical transitions, not timing or projected proof savings.
The original observer output is checked against the pinned reference census.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

from summarize import summarize


GROUPS = {
    "array_tree_navigation": ["Ixby.Runtime.treeGet", "Ixby.Runtime.treeSet"],
    "byte_rope_helpers": ["Ixby.Runtime.byteAppend", "Ixby.Runtime.byteHeight",
                          "Ixby.Runtime.byteNode", "Ixby.Runtime.byteBalance"],
    "number_unboxing": ["Ixby.Runtime.natural"],
    "nibble_conversion_helpers": ["Ixby.Runtime.toWord", "Ixby.Runtime.fromWordLoop",
                                  "Ixby.Runtime.nibbleWord", "Ixby.Runtime.nibbleNat"],
}


def pin(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--inventory", required=True, type=Path)
    parser.add_argument("--reference", required=True, type=Path)
    parser.add_argument("--program", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--groups", type=Path,
                        help="JSON object mapping group names to function-name lists")
    args = parser.parse_args()
    raw_report = args.report.read_bytes()
    report = json.loads(gzip.decompress(raw_report) if args.report.suffix == ".gz" else raw_report)
    inventory = json.loads(args.inventory.read_text())
    reference = json.loads(args.reference.read_text())
    if not report["completed"]:
        raise ValueError("function costs require a complete reference run")
    census = summarize(report)
    for key, value in census.items():
        if value != reference[key]:
            raise ValueError(f"reference census mismatch: {key}")
    if pin(args.program) != reference["artifacts"]["program"]:
        raise ValueError("program does not match the pinned reference image")
    for key, value in pin(args.program).items():
        if inventory["artifact"][key] != value:
            raise ValueError(f"compiler inventory program mismatch: {key}")
    bases = report["function_block_bases"]
    counts = report["block_counts"]
    functions = inventory["function_inventory"]
    if len(bases) != len(functions) or len(functions) != inventory["functions"]:
        raise ValueError("function inventory length mismatch")
    if bases[0] != 0 or len(counts) != inventory["blocks"]:
        raise ValueError("function inventory block domain mismatch")
    total = report["reference_transitions"]
    if sum(report["control_counts_eval_ret_apply"]) != total:
        raise ValueError("control counts do not cover all reference transitions")
    rows = []
    blocks = []
    for i, function in enumerate(functions):
        start = bases[i]
        end = bases[i + 1] if i + 1 < len(bases) else len(counts)
        if function["index"] != i or end - start != function["blocks"]:
            raise ValueError(f"function block layout mismatch at {i}")
        count = sum(counts[start:end])
        rows.append({"index": i, "name": function["name"], "blocks": end - start,
                     "eval_transitions": count, "fraction_of_all_transitions": count / total})
        for offset, count in enumerate(counts[start:end]):
            blocks.append({"function": i, "name": function["name"], "block": offset,
                           "eval_transitions": count,
                           "instruction": report["instructions"][start + offset]})
    if sum(row["eval_transitions"] for row in rows) != census["control_counts_eval_ret_apply"][0]:
        raise ValueError("function counts do not cover all eval transitions")
    by_name = {row["name"]: row for row in rows}
    if len(by_name) != len(rows):
        raise ValueError("duplicate function names")
    groups = {}
    definitions = json.loads(args.groups.read_text()) if args.groups else GROUPS
    for name, members in definitions.items():
        count = sum(by_name[member]["eval_transitions"] for member in members)
        groups[name] = {"members": members, "eval_transitions": count,
                        "fraction_of_all_transitions": count / total}
    result = {
        "scope": "Exclusive function/block counts from the unchanged completed native reference run; no Flock proof or measured optimization speedup.",
        "reference_transitions": total,
        "eval_ret_apply_transitions": census["control_counts_eval_ret_apply"],
        "artifacts": {"program": pin(args.program), "observer_report": pin(args.report),
                      "compiler_inventory": pin(args.inventory), "reference_census": pin(args.reference)},
        "groups": groups,
        "functions": sorted(rows, key=lambda row: (-row["eval_transitions"], row["index"])),
        "top_blocks": sorted(blocks, key=lambda row: -row["eval_transitions"])[:40],
        "limits": [
            "Function names come from the compiler inventory joined by checked function indices and block counts.",
            "Function counts include their own call instructions; callee instructions are attributed to the callee.",
            "Return-control and apply-control transitions have no function attribution in this observer.",
            "Replacing a helper still requires checked semantics, compiler correspondence, and constrained execution; these counts are not removable-work estimates.",
        ],
    }
    if args.groups:
        result["artifacts"]["group_definitions"] = pin(args.groups)
    with args.output.open("x") as output:
        json.dump(result, output, indent=2)
        output.write("\n")


if __name__ == "__main__":
    main()
