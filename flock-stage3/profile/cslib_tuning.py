#!/usr/bin/env python3
"""Assemble exact-range leaf/join measurements and captured-window censuses.

This validates receipts and public boundaries. Proof verification happens in
the recorded Rust producer and fresh receiver, not in this report builder.
"""
import argparse
import json
from pathlib import Path
import re
import struct

from batch_tuning import census, passed, receipt, records, timing


def words(path):
    raw = path.read_bytes()
    assert len(raw) == 57 * 16
    return [pair for pair in struct.iter_unpack("<QQ", raw)]


def merged_census(paths):
    combined = {"logs": [], "sources": {}, "shapes": []}
    by_name = {}
    for path in paths:
        part = census(path, expected_sources=None)
        combined["logs"].append({"name": path.name, **part["log"]})
        assert not (combined["sources"].keys() & part["sources"].keys())
        combined["sources"].update(part["sources"])
        for shape in part["shapes"]:
            if shape["name"] not in by_name:
                by_name[shape["name"]] = shape
                combined["shapes"].append(shape)
                continue
            current = by_name[shape["name"]]
            assert all(current[k] == v for k, v in shape.items()
                       if k not in ["samples", "census_seconds"])
            assert not (current["samples"].keys() & shape["samples"].keys())
            current["samples"].update(shape["samples"])
    for shape in combined["shapes"]:
        assert shape["samples"].keys() == combined["sources"].keys()
        samples = list(shape["samples"].values())
        complete = sum(s["complete_batches"] for s in samples)
        logical = sum(s["logical_steps"] for s in samples)
        shape["summary"] = {
            "windows": len(samples), "complete_leaves": complete,
            "fixed_window_leaves_including_tails": complete + len(samples),
            "complete_leaf_logical_steps": logical,
            "logical_steps_per_complete_leaf": logical / complete,
        }
    return combined


def proof_run(root, name, expected_class):
    path = root / f"{name}-proof.log"
    text = passed(path)
    identity, = records(text, "proof_setup_identity,")
    _, batch_class, registry, circuit, nu, dense = identity.split(",")
    assert batch_class == expected_class
    leaves, statements, setup_seconds = [], [], None
    summary, = records(text, "proof benchmark: ")
    fields = dict(re.findall(r"(\w+)=([^ ]+)", summary))
    assert int(fields["workers"]) == 1 and int(fields["threads"]) == 2
    setup_seconds = float(fields["setup_seconds"])
    for line in records(text, "proof_sample,"):
        s = line.split(",")
        if s[1] == "batch":
            continue
        index, worker, microsteps, logical = map(int, s[1:5])
        assert index == len(leaves) and worker == 0
        stem = root / f"{name}-proofs" / f"{index:010}"
        statement_path = stem.with_suffix(".statement")
        proof_path = stem.with_suffix(".flock")
        statement = words(statement_path)
        assert statement[30][0] - statement[3][0] == microsteps
        assert statement[36][1] - statement[9][1] == logical
        assert proof_path.stat().st_size == int(s[8])
        if statements:
            assert statements[-1][:3] == statement[:3]
            assert statements[-1][30:] == statement[3:30]
        statements.append(statement)
        leaves.append({"index": index, "microsteps": microsteps, "logical_steps": logical,
                       "witness_seconds": float(s[5]), "prove_seconds": float(s[6]),
                       "verify_seconds": float(s[7]), "proof": receipt(proof_path),
                       "statement": receipt(statement_path)})
    assert len(leaves) == int(fields["batches"]) >= 2
    first, last = statements[0], statements[-1]
    assert first[3][0] == 0 and last[30][0] == 20_000
    expected = first[:30] + last[30:]
    chain_path = root / f"{name}-chain.log"
    chain_text = passed(chain_path)
    events = [json.loads(line) for line in chain_text.splitlines() if line.startswith("{")]
    joins = [e for e in events if e["event"] == "chain_proof"]
    setups = [e for e in events if e["event"] == "chain_setup"]
    receivers = [e for e in events if e["event"] == "chain_receiver_accepted"]
    assert len(joins) == len(leaves) - 1 and len(receivers) == 1
    assert all(e["class"] == batch_class for e in events)
    assert "rejected all 114 public-word mutations, truncation and trailing data" in chain_text
    for event in joins:
        start, count = event["first_leaf"], event["leaves"]
        stem = root / f"{name}-chain" / f"range-{start}-{count}"
        statement = words(stem.with_suffix(".statement"))
        assert statement == statements[start][:30] + statements[start + count - 1][30:]
        assert stem.with_suffix(".flock").stat().st_size == event["bytes"]
        event["proof"] = receipt(stem.with_suffix(".flock"))
        event["statement"] = receipt(stem.with_suffix(".statement"))
    root_stem = root / f"{name}-chain" / f"range-0-{len(leaves)}"
    assert words(root_stem.with_suffix(".statement")) == expected
    leaf_seconds = sum(sum(e[k] for k in ["witness_seconds", "prove_seconds", "verify_seconds"])
                       for e in leaves)
    join_seconds = sum(e["seconds"] for e in joins)
    total = leaf_seconds + join_seconds
    fuel = last[36][1] - first[9][1]
    return {"class": batch_class, "registry_digest": registry, "circuit_digest": circuit,
            "row_variables": int(nu), "dense_variables": int(dense),
            "claim": "Conditional execution segment; source admission and complete execution are outside this benchmark.",
            "clock_range": [first[3][0], last[30][0]], "fuel_range": [first[9][1], last[36][1]],
            "root_statement": receipt(root_stem.with_suffix(".statement")),
            "root_proof": receipt(root_stem.with_suffix(".flock")),
            "leaf_count": len(leaves), "join_count": len(joins),
            "leaf_setup_seconds": setup_seconds, "native_seconds": float(fields["native_seconds"]),
            "leaf_seconds": leaf_seconds, "join_seconds": join_seconds,
            "cached_setup_total_seconds": total, "cached_setup_logical_steps_per_second": fuel / total,
            "leaf_log": receipt(path), "chain_log": receipt(chain_path),
            "leaf_process": timing(root / f"{name}-proof.time"),
            "chain_process": timing(root / f"{name}-chain.time"),
            "leaves": leaves, "joins": joins, "join_setups": setups, "fresh_receiver": receivers[0]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--native-report", required=True, type=Path)
    parser.add_argument("--census", required=True, type=Path, action="append")
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--run", action="append", required=True, help="prefix:class")
    args = parser.parse_args()
    runs = [proof_run(args.root, *spec.split(":")) for spec in args.run]
    assert len({r["root_statement"]["sha256"] for r in runs}) == 1
    comparison = merged_census(args.census)
    native = json.loads(args.native_report.read_text())
    for source in comparison["sources"].values():
        assert source["program_blake3"] == native["program_blake3"]
        assert source["input_blake3"] == native["input_blake3"]
    result = {"format": "IxBy/cslib-execution-tuning/v0",
              "native_profile": receipt(args.native_report),
              "census": comparison, "runs": runs,
              "speedups_vs_first": {r["class"]: runs[0]["cached_setup_total_seconds"] /
                                     r["cached_setup_total_seconds"] for r in runs[1:]},
              "limits": ["One bounded range and one timing run per class; no whole-workload proof forecast.",
                         "Cached totals include every leaf and join's proof/check work; setup, admission and complete-run closing are excluded.",
                         "Process records separately include actual setup and fresh-receiver costs."]}
    args.out.write_text(json.dumps(result, indent=2) + "\n")
