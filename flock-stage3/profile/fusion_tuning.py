#!/usr/bin/env python3
"""Check fused capture counts and the matched genuine execution proof trees.

Rust checks circuit witnesses and proofs. This report checks completed logs,
source receipts, exact public boundaries, all batch counts and all tree joins.
Captured addresses are count-only inputs, never execution proof witnesses.
"""
import argparse
import ast
from collections import defaultdict
import json
from pathlib import Path
import re
import struct

from batch_tuning import CHIP_NAMES, passed, receipt, records, timing
from cslib_tuning import proof_run, words


CHIPS = CHIP_NAMES + ["FusedControl", "FusedNumeric", "CopyPair"] + [
    f"FusedCall{n}" for n in range(5)]
SPANS = [1] * 31 + [3, 4, 2, 2, 4, 6, 8, 10]
ACCESSES = [1, 3, 6, 4, 4, 3, 1, 1, 1, 5, 5, 1, 2, 3, 3, 3,
            7, 6, 3, 1, 3, 1, 1, 0, 5, 3, 2, 3, 2, 3, 1,
            7, 10, 4, 3, 7, 11, 15, 19]


def vector(text, length):
    result = ast.literal_eval(text)
    assert isinstance(result, list) and len(result) == length
    assert all(type(n) is int and n >= 0 for n in result)
    return result


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def expanded(counts):
    result = counts[:31]
    for n, parts in zip(counts[31:], [
            [(0, 1), (1, 1), (3, 1)], [(0, 1), (1, 2), (2, 1)],
            [(5, 2)], *[[(0, 1), (1, n), (4, 1), (5, n)] for n in range(5)]], strict=True):
        for chip, multiplicity in parts:
            result[chip] += n * multiplicity
    return result


def capture_receipts(native, directory):
    sources = {}
    for expected in native["captured_windows"]:
        path = directory / expected["file"]
        assert receipt(path) == {k: expected[k] for k in ("bytes", "sha256")}
        with path.open("rb") as stream:
            header = stream.read(96)
        assert header[:8] == b"IXQP0001"
        for at, key in ((8, "program_blake3"), (40, "input_blake3")):
            assert header[at:at + 32].hex() == expected[key] == native[key]
        start, fuel, length = struct.unpack("<QQQ", header[72:])
        assert [start, start + length] == expected["clock_range"]
        assert fuel == expected["fuel_range"][0]
        assert sum(expected["chip_counts"]) == length
        assert path.stem not in sources
        sources[path.stem] = expected
    return sources


def census(paths, sources):
    shapes, traces, samples, logs = {}, {}, {}, []
    for path in paths:
        logs.append({"name": path.name, "log": receipt(path),
                     "process": timing(path.with_suffix(".time"))})
        for line in passed(path).splitlines():
            if line.startswith("fusion_shape,"):
                s = line.split(",", 12)
                keys = ["circuit_rows", "access_slots", "cells", "parents",
                        "row_variables", "dense_variables", "dense_words",
                        "committed_words", "state_lanes", "memory_lanes"]
                shape = dict(zip(keys, map(int, s[2:12]), strict=True))
                original, fused = ast.literal_eval("[" + s[12] + "]")
                assert len(original) == 31 and len(fused) == 8
                shape["quotas"] = original + fused
                assert all(type(n) is int and n >= 0 for n in shape["quotas"])
                assert sum(shape["quotas"]) == shape["circuit_rows"]
                assert dot(shape["quotas"], ACCESSES) == shape["access_slots"]
                assert shape["committed_words"] == 1 << (shape["dense_variables"] - 7)
                assert shape["committed_words"] // 2 < shape["dense_words"] <= shape["committed_words"]
                assert shape["circuit_rows"] + 2 <= shape["state_lanes"]
                assert shape["access_slots"] + 2 * shape["cells"] <= shape["memory_lanes"]
                if s[1] in shapes:
                    assert shapes[s[1]] == shape
                shapes[s[1]] = shape
            elif line.startswith("fusion_trace,"):
                s = line.split(",", 9)
                name = s[1]
                assert name not in traces
                start, end, before, after, rows, old_events, new_events = map(int, s[2:9])
                counts = vector(s[9], len(CHIPS))
                source = sources[name]
                assert [start, end] == source["clock_range"]
                assert [before, after] == source["fuel_range"]
                assert sum(counts) == rows and dot(counts, SPANS) == end - start
                assert dot(counts, ACCESSES) == new_events
                assert expanded(counts) == source["chip_counts"]
                assert dot(source["chip_counts"], ACCESSES[:31]) == old_events
                traces[name] = {"clock_range": [start, end], "fuel_range": [before, after],
                                "original_rows": end - start, "fused_rows": rows,
                                "original_events": old_events, "fused_events": new_events,
                                "fused_chip_counts": counts,
                                "capture": {k: source[k] for k in ("bytes", "sha256")}}
            elif line.startswith("fusion_batch,"):
                s = line.split(",", 11)
                shape_name, name = s[1:3]
                index, start, end, before, after, rows, cells, parents = map(int, s[3:11])
                counts = vector(s[11], len(CHIPS))
                shape, trace = shapes[shape_name], traces[name]
                assert sum(counts) == rows > 0 and dot(counts, SPANS) == end - start
                assert all(n <= q for n, q in zip(counts, shape["quotas"], strict=True))
                assert 0 < cells <= shape["cells"] and 0 < parents <= shape["parents"]
                assert before <= after
                sample = samples.setdefault((shape_name, name), {
                    "leaves": 0, "circuit_rows": 0, "accesses": 0,
                    "counts": [0] * len(CHIPS), "next_clock": trace["clock_range"][0],
                    "next_fuel": trace["fuel_range"][0], "max_cells": 0, "max_parents": 0})
                assert index == sample["leaves"]
                assert start == sample["next_clock"] and before == sample["next_fuel"]
                sample["next_clock"], sample["next_fuel"] = end, after
                sample["leaves"] += 1
                sample["circuit_rows"] += rows
                sample["accesses"] += dot(counts, ACCESSES)
                sample["counts"] = [a + b for a, b in zip(sample["counts"], counts, strict=True)]
                sample["max_cells"] = max(sample["max_cells"], cells)
                sample["max_parents"] = max(sample["max_parents"], parents)
            elif line.startswith("fusion_sample,"):
                s = line.split(",", 4)
                shape_name, name = s[1:3]
                sample, trace = samples[shape_name, name], traces[name]
                assert "stops" not in sample
                assert sample["leaves"] == int(s[3])
                stops = vector(s[4], len(CHIPS) + 2)
                assert sum(stops) == sample["leaves"] - 1
                assert sample.pop("next_clock") == trace["clock_range"][1]
                assert sample.pop("next_fuel") == trace["fuel_range"][1]
                expected = (trace["fused_chip_counts"] if any(shapes[shape_name]["quotas"][31:])
                            else sources[name]["chip_counts"] + [0] * 8)
                assert sample.pop("counts") == expected
                sample["stops"] = {k: n for k, n in zip(CHIPS + ["Cells", "Parents"], stops, strict=True) if n}
    assert traces.keys() == sources.keys()
    assert len(samples) == len(shapes) * len(traces)
    for label, shape in shapes.items():
        selected = {name: samples[label, name] for name in sorted(traces)}
        assert all("stops" in sample for sample in selected.values())
        stop_counts = defaultdict(int)
        for sample in selected.values():
            for reason, n in sample["stops"].items():
                stop_counts[reason] += n
        shape["summary"] = {
            "windows": len(selected), "leaves_including_window_tails": sum(s["leaves"] for s in selected.values()),
            "fewer_leaves_than_baseline": sum(s["leaves"] < samples["cslib-2048", n]["leaves"] for n, s in selected.items()),
            "equal_leaves_to_baseline": sum(s["leaves"] == samples["cslib-2048", n]["leaves"] for n, s in selected.items()),
            "more_leaves_than_baseline": sum(s["leaves"] > samples["cslib-2048", n]["leaves"] for n, s in selected.items()),
            "stops": dict(stop_counts)}
        shape["samples"] = selected
    totals = {k: sum(t[k] for t in traces.values()) for k in (
        "original_rows", "fused_rows", "original_events", "fused_events")}
    totals["row_reduction_fraction"] = 1 - totals["fused_rows"] / totals["original_rows"]
    totals["event_reduction_fraction"] = 1 - totals["fused_events"] / totals["original_events"]
    return {"logs": logs, "totals": totals, "shapes": shapes, "windows": traces}


def measured_run(root, name, batch_class, shape):
    result = proof_run(root, name, batch_class)
    text = passed(root / f"{name}-proof.log")
    counts = {}
    for line in records(text, "proof_quota,"):
        _, index, values = line.split(",", 2)
        assert int(index) not in counts
        counts[int(index)] = vector(values, len(CHIPS))
    assert sorted(counts) == list(range(result["leaf_count"]))
    for leaf in result["leaves"]:
        q = counts[leaf["index"]]
        assert all(n <= cap for n, cap in zip(q, shape["quotas"], strict=True))
        assert dot(q, SPANS) == leaf["microsteps"]
        leaf.update(chip_counts=q, circuit_rows=sum(q), accesses=dot(q, ACCESSES))
    final, = records(text, "proof benchmark complete: ")
    fields = dict(re.findall(r"(\w+)=([^ ]+)", final))
    for key in ("microsteps", "circuit_rows", "logical_steps"):
        assert int(fields[key]) == sum(leaf[key] for leaf in result["leaves"])
    assert result["row_variables"] == shape["row_variables"]
    assert result["dense_variables"] == shape["dense_variables"]
    result["circuit_rows"] = sum(leaf["circuit_rows"] for leaf in result["leaves"])
    result["accesses"] = sum(leaf["accesses"] for leaf in result["leaves"])
    # Require every internal node of the binary tree, not just the root.
    seen = set()
    setups = result["join_setups"]
    for join in result["joins"]:
        first, count = join["first_leaf"], join["leaves"]
        assert (first, count) not in seen
        split = 1 << ((count - 1).bit_length() - 1)
        for at, n in ((first, split), (first + split, count - split)):
            assert n == 1 or (at, n) in seen
        setup, = [s for s in setups if s["leaves"] == count]
        assert setup["geometry"] == join["geometry"]
        join["setup_identity"] = setup["identity"]
        seen.add((first, count))
    assert (first, count) == (0, result["leaf_count"])
    chain_text = passed(root / f"{name}-chain.log")
    events = [json.loads(s) for s in chain_text.splitlines() if s.startswith("{")]
    receiver_setup, = [e for e in events if e["event"] == "chain_receiver_setup"]
    assert receiver_setup["geometry"] == result["joins"][-1]["geometry"]
    assert receiver_setup["identity"] == result["joins"][-1]["setup_identity"]
    result["fresh_receiver_setup"] = receiver_setup
    assert result["fresh_receiver"]["bytes"] == result["root_proof"]["bytes"]
    assert result["leaf_process"]["swaps"] == result["chain_process"]["swaps"] == 0
    result["total_process_wall_seconds"] = sum(result[k]["wall_seconds"] for k in ("leaf_process", "chain_process"))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--native-report", required=True, type=Path)
    parser.add_argument("--windows", required=True, type=Path)
    parser.add_argument("--census", action="append", required=True, type=Path)
    parser.add_argument("--run", action="append", required=True, help="prefix:class")
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    native = json.loads(args.native_report.read_text())
    comparison = census(args.census, capture_receipts(native, args.windows))
    runs = [measured_run(args.root, name, label, comparison["shapes"][label])
            for name, label in (s.split(":") for s in args.run)]
    assert len(runs) >= 2 and len({r["class"] for r in runs}) == len(runs)
    assert all(r["root_statement"] == runs[0]["root_statement"] for r in runs)
    statements = [words(args.root / f"{s.split(':')[0]}-chain" / f"range-0-{r['leaf_count']}.statement")
                  for s, r in zip(args.run, runs, strict=True)]
    assert all(s == statements[0] for s in statements)
    result = {"format": "IxBy/execution-fusion/v0", "native_profile": receipt(args.native_report),
              "chip_order": CHIPS, "clock_spans": SPANS, "accesses_per_row": ACCESSES,
              "fused_zero_cell": "Address zero is included in each fused batch's authenticated cell quota; its old and new values are constrained to zero without adding an execution access.",
              "census": comparison, "runs": runs,
              "speedups_vs_first": {r["class"]: {
                  "leaf_work": runs[0]["leaf_seconds"] / r["leaf_seconds"],
                  "cached_leaf_plus_every_join": runs[0]["cached_setup_total_seconds"] / r["cached_setup_total_seconds"],
                  "total_process_wall": runs[0]["total_process_wall_seconds"] / r["total_process_wall_seconds"]} for r in runs[1:]},
              "limits": [
                  "One matched 20,000-original-microstep / 4,598-logical-step execution range per class; no complete CSLib proof.",
                  "Leaf production and every recursive join were measured for both classes. The baseline uses the pinned v10 binaries; fused proofs and final checks use v14, whose later changes affect fused wiring only.",
                  "Cached totals include witness, proof and verification work; setup, source admission, complete-run closing and I/O are excluded.",
                  "Process wall times include actual setup and fresh reception. Large proof jobs ran sequentially; final fused checks and capture counting finished before fused proof production.",
                  "Captures contain chip/fuel/address counts, not values or proofs. They are 341 separate 100,000-microstep windows, each including a final partial leaf.",
                  f"The small fused class needs more leaves in {comparison['shapes']['cslib-fused']['summary']['more_leaves_than_baseline']} windows. The larger fused candidate is count-only and is not an approved proof class; neither count predicts whole-run proof time.",
                  "Source program, input, logical fuel and final public state/memory are unchanged. Original microstep clocks now differ from the number of circuit rows."]}
    args.out.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
