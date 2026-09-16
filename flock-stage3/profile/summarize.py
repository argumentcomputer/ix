#!/usr/bin/env python3
"""Summarize a reference observer report without replaying any guest."""
import argparse
from collections import Counter
import json
from pathlib import Path
import re


def summarize(report):
    result = {key: value for key, value in report.items()
              if key not in {"instructions", "block_counts", "function_block_bases"}}
    counts = report["block_counts"]
    instructions = report["instructions"]
    if len(counts) != len(instructions):
        raise ValueError("block/instruction count mismatch")
    if sum(counts) != report["control_counts_eval_ret_apply"][0]:
        raise ValueError("block counts do not cover reference eval transitions")
    result["executed_blocks"] = sum(count > 0 for count in counts)
    result["total_blocks"] = len(counts)
    for field, prefix in [("instructions", "Instr"), ("operations", "Op"), ("primitives", "Primitive")]:
        census = Counter()
        for count, instruction in zip(counts, instructions):
            match = re.search(r"Ix\.Ixby\." + prefix + r"\.(\w+)", instruction)
            if match:
                census[match[1]] += count
        result[field] = dict(census.most_common())
    result["scope"] = "Native reference execution observation; no Flock proof. Value maxima cover inspected values, not a traversal of all reachable values."
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("summary", type=Path)
    args = parser.parse_args()
    result = summarize(json.loads(args.report.read_text()))
    with args.summary.open("x") as output:
        json.dump(result, output, indent=2)
        output.write("\n")


if __name__ == "__main__":
    main()
