#!/usr/bin/env python3
"""Check same-proof recursive measurements and assemble their cost breakdown.

Rust verifies the proofs. This script validates the completed test logs,
artifact receipts, unchanged setups and exact execution boundaries. Leaf
timings are explicitly reused from the earlier, unchanged execution run.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import shlex

from batch_tuning import passed, receipt, timing
from cslib_tuning import words


def stages(events, scope):
    selected = [e for e in events if e["scope"] == scope]
    assert len({e["id"] for e in selected}) == 1, scope
    result = {e["stage"]: e["seconds"] for e in selected}
    assert len(result) == len(selected)
    return result


def constraints(events):
    result = {}
    for e in events:
        if e["scope"] not in ("child", "fold"):
            continue
        assert e["shape_only"] is True
        key = f'{e["scope"]}/{e["stage"]}'
        counts = result.setdefault(key, {k: 0 for k in e["counts"]})
        for field, n in e["counts"].items():
            counts[field] += n
    return result


def graph_total(events, geometry):
    graph = [e for e in events if e["scope"] == "node_graph"]
    assert len(graph) == 2 and {e["stage"] for e in graph} == {"children", "folds"}
    total = {k: sum(e["counts"][k] for e in graph) for k in graph[0]["counts"]}
    for field, geometry_field in (("variables", "variables"),
                                  ("arithmetic", "arithmetic_operations"),
                                  ("packing", "packing_rows"),
                                  ("compressions", "blake3_compressions")):
        assert total[field] == geometry[geometry_field]
    return total


def chain(root, name, leaves, source):
    log_path = root / f"{name}-chain.log"
    text = passed(log_path)
    assert text.count("test result: ok. 1 passed;") == 2
    assert "rejected all 114 public-word mutations, truncation and trailing data" in text
    pending, kernel, setups, joins = [], [], [], []
    receiver_setups, receivers = [], []
    main_pid = None
    for line in text.splitlines():
        if "[prove_union]" in line:
            kernel.append(line.strip())
        if not line.startswith("{"):
            continue
        event = json.loads(line)
        kind = event["event"]
        if kind == "recursion_profile":
            main_pid = main_pid or event["pid"]
            if event["pid"] == main_pid:
                assert event["seconds"] >= 0
                if event["counts"] is not None:
                    assert all(n >= 0 for n in event["counts"].values())
                pending.append(event)
            continue
        assert event["class"] == source["class"]
        if kind == "chain_setup":
            assert all(e["shape_only"] in (None, True) for e in pending)
            event["graph_counts"] = graph_total(pending, event["geometry"])
            event["constraint_phases"] = constraints(pending)
            event["compile_seconds"] = stages(pending, "node_compile")
            setups.append(event)
            pending = []
        elif kind == "chain_proof":
            first, count = event["first_leaf"], event["leaves"]
            assert 0 <= first < first + count <= len(leaves)
            stem = root / f"{name}-chain" / f"range-{first}-{count}"
            statement = stem.with_suffix(".statement")
            proof = stem.with_suffix(".flock")
            assert words(statement) == leaves[first][:30] + leaves[first + count - 1][30:]
            event["statement"] = receipt(statement)
            event["proof"] = receipt(proof)
            assert event["proof"]["bytes"] == event["bytes"]
            setup, = [e for e in setups if e["leaves"] == count]
            assert event["geometry"] == setup["geometry"]
            assert graph_total(pending, event["geometry"]) == setup["graph_counts"]
            event["setup_identity"] = setup["identity"]
            event["prove_seconds"] = stages(pending, "node_prove")
            event["verify_seconds"] = stages(pending, "node_verify")
            event["native_proof_seconds"] = stages(pending, "native_proof")
            event["fold_seconds"] = stages(pending, "fold")
            families = defaultdict(lambda: {"count": 0, "seconds": 0.0})
            for e in pending:
                if e["scope"] == "fold_family":
                    families[e["stage"]]["count"] += 1
                    families[e["stage"]]["seconds"] += e["seconds"]
            if families:
                assert sum(v["count"] for v in families.values()) == event["geometry"]["root_families"]
            event["fold_families"] = dict(families)
            event["flock_kernel_log"] = kernel
            accounted = sum(event["prove_seconds"].values()) + sum(event["verify_seconds"].values())
            assert 0 <= event["seconds"] - accounted < 1.0
            event["unaccounted_seconds"] = event["seconds"] - accounted
            joins.append(event)
            pending, kernel = [], []
        elif kind == "chain_receiver_setup":
            receiver_setups.append(event)
        elif kind == "chain_receiver_accepted":
            receivers.append(event)
        else:
            raise ValueError(f"unexpected event {kind}")
    assert not pending and not kernel
    assert len(joins) == len(leaves) - 1
    assert len(receiver_setups) == len(receivers) == 1
    seen = set()
    for e in joins:
        first, count = e["first_leaf"], e["leaves"]
        assert (first, count) not in seen
        seen.add((first, count))
        split = 1 << ((count - 1).bit_length() - 1)
        for child_first, child_count in ((first, split), (first + split, count - split)):
            assert child_count == 1 or (child_first, child_count) in seen
    final = joins[-1]
    assert (final["first_leaf"], final["leaves"]) == (0, len(leaves))
    receiver_setup, receiver = receiver_setups[0], receivers[0]
    assert receiver_setup["geometry"] == final["geometry"]
    assert receiver_setup["identity"] == final["setup_identity"]
    assert receiver["bytes"] == final["bytes"]
    assert final["statement"] == source["root_statement"]
    total = sum(e["seconds"] for e in joins)
    breakdown = {}
    for scope in ("prove_seconds", "verify_seconds", "native_proof_seconds", "fold_seconds"):
        keys = joins[0][scope].keys()
        assert all(e[scope].keys() == keys for e in joins)
        breakdown[scope] = {k: sum(e[scope][k] for e in joins) for k in keys}
    return {"name": name, "class": source["class"],
            "log": receipt(log_path), "process": timing(root / f"{name}-chain.time"),
            "join_seconds": total, "cached_leaf_plus_join_seconds": source["leaf_seconds"] + total,
            "root_statement": final["statement"], "root_proof": final["proof"],
            "breakdown": breakdown, "setups": setups, "joins": joins,
            "receiver_setup": receiver_setup, "receiver": receiver}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--leaf-report", required=True, type=Path)
    parser.add_argument("--leaf-dir", required=True, type=Path)
    parser.add_argument("--class", dest="batch_class", default="cslib-2048")
    parser.add_argument("--binary", required=True, type=Path)
    parser.add_argument("--run", action="append", required=True)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    previous = json.loads(args.leaf_report.read_text())
    source, = [r for r in previous["runs"] if r["class"] == args.batch_class]
    assert source["leaf_count"] == len(source["leaves"])
    leaves = []
    for i, leaf in enumerate(source["leaves"]):
        assert leaf["index"] == i
        stem = args.leaf_dir / f"{i:010}"
        assert receipt(stem.with_suffix(".statement")) == leaf["statement"]
        assert receipt(stem.with_suffix(".flock")) == leaf["proof"]
        statement = words(stem.with_suffix(".statement"))
        assert statement[30][0] - statement[3][0] == leaf["microsteps"]
        assert statement[36][1] - statement[9][1] == leaf["logical_steps"]
        if leaves:
            assert leaves[-1][:3] == statement[:3]
            assert leaves[-1][30:] == statement[3:30]
        leaves.append(statement)
    assert [leaves[0][3][0], leaves[-1][30][0]] == source["clock_range"]
    assert [leaves[0][9][1], leaves[-1][36][1]] == source["fuel_range"]
    leaf_seconds = sum(sum(e[k] for k in ("witness_seconds", "prove_seconds", "verify_seconds")) for e in source["leaves"])
    assert abs(leaf_seconds - source["leaf_seconds"]) < 1e-9
    assert len(args.run) >= 2 and len(set(args.run)) == len(args.run)
    runs = [chain(args.root, name, leaves, source) for name in args.run]
    assert all(shlex.split(r["process"]["command"])[0] == str(args.binary) for r in runs)
    for run in runs[1:]:
        assert run["root_proof"] == runs[0]["root_proof"]
        for a, b in zip(runs[0]["joins"], run["joins"], strict=True):
            for key in ("first_leaf", "leaves", "geometry", "setup_identity", "proof", "statement"):
                assert a[key] == b[key], key
        for a, b in zip(runs[0]["setups"], run["setups"], strict=True):
            assert a["constraint_phases"] == b["constraint_phases"]
    for run in runs:
        assert run["root_proof"] == source["root_proof"]
    microsteps = source["clock_range"][1] - source["clock_range"][0]
    logical_steps = source["fuel_range"][1] - source["fuel_range"][0]
    result = {"format": "IxBy/recursive-tuning/v0", "binary": receipt(args.binary),
              "leaf_measurement": {"report": receipt(args.leaf_report),
                                   **{k: source[k] for k in ("class", "clock_range", "fuel_range", "leaf_count", "leaf_seconds", "leaves", "leaf_process")}},
              "runs": runs,
              "speedups_vs_first": {r["name"]: {
                  "joins": runs[0]["join_seconds"] / r["join_seconds"],
                  "cached_leaf_plus_join": runs[0]["cached_leaf_plus_join_seconds"] / r["cached_leaf_plus_join_seconds"],
                  "tree_process_wall": runs[0]["process"]["wall_seconds"] / r["process"]["wall_seconds"]} for r in runs[1:]},
              "limits": [f"Conditional {microsteps:,}-microstep / {logical_steps:,}-logical-step execution segment; no complete CSLib proof-time forecast.",
                         "Leaf timings and the identical leaf proofs are reused from the prior pinned run; each tree measures every recursive join again.",
                         "Cached totals exclude setup, admission, complete-run closing and I/O. Tree process records include actual setup and fresh reception.",
                         "Nested timing scopes and Flock kernel logs overlap and must not be added to their parent scopes.",
                         "Fresh receivers clear the environment and use the optimized default in both runs. The reference switch selects the producer's folds and in-process root checks.",
                         "One matched run per evaluator; ordinary checks overlapped optimized setup compilation, and no large proof jobs overlapped."]}
    args.out.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
