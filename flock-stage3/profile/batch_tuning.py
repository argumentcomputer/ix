#!/usr/bin/env python3
"""Assemble the bounded batch experiment's census and verified-proof receipts.

This reads measurements; it does not verify Flock proofs. Each included test
log must report success, and each proof/statement receipt is checked against
the measured sizes, clocks, fuel charges, and per-chip counts.
"""

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import struct


RUNS = {
    "baseline-arithmetic": ("shared-linked-1024", "arithmetic"),
    "arithmetic-768": ("arithmetic-768", "arithmetic"),
    "arithmetic-3072": ("arithmetic-3072", "arithmetic"),
    "arithmetic-4096": ("arithmetic-4096", "arithmetic"),
    "baseline-arrays": ("shared-linked-1024", "arrays"),
    "arrays-768": ("arrays-768", "arrays"),
    "baseline-builders": ("shared-linked-1024", "bytes"),
    "builders-768": ("builders-768", "bytes"),
    "baseline-retained": ("shared-linked-1024", "retained"),
    "mixed-3072": ("mixed-3072", "retained"),
}
CHAINS = ["baseline-arithmetic", "arithmetic-768", "arithmetic-3072", "arithmetic-4096", "mixed-3072"]
CHIP_NAMES = [
    "Fetch", "Resolve", "Numeric", "Control", "Call", "Resume", "Construct",
    "Closure", "ApplyInstruction", "Project", "Case", "Apply", "StoreCopy",
    "StoreFinish", "ByteStart", "ByteRead", "ByteAppend", "ByteEq", "ByteFinish",
    "ByteEmit", "HashBlock", "HashCombine", "HashPush", "HashSkip",
    "CollectionStart", "ArrayStep", "ArrayAscend", "CollectionFinish",
    "BuilderNode", "BuilderCopy", "BuilderEmit",
]
SHAPE_KEYS = [
    "name", "microstep_slots", "access_slots", "cells", "parents", "row_variables",
    "state_lanes", "memory_lanes", "tree_lanes", "dense_variables", "dense_words",
    "committed_words", "switches", "census_seconds", "quotas",
]


def receipt(path: Path) -> dict:
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def passed(path: Path) -> str:
    text = path.read_text()
    if "test result: ok." not in text or "test result: FAILED." in text:
        raise ValueError(f"incomplete or failed test: {path}")
    return text


def records(text: str, prefix: str):
    for line in text.splitlines():
        at = line.find(prefix)
        if at >= 0:
            yield line[at:]


def census(path: Path, expected_sources: int | None = 4) -> dict:
    shapes = []
    sources = {}
    for line in passed(path).splitlines():
        if "quota_trace," in line:
            line = line[line.index("quota_trace,"):]
            match = re.fullmatch(r"quota_trace,([^,]+),(\d+),(\d+),([\d.]+),(\[.*\]),([0-9a-f]{64}),([0-9a-f]{64})", line)
            if not match:
                raise ValueError(f"invalid trace receipt: {line}")
            name, steps, fuel, seconds, counts, program, inputs = match.groups()
            sources[name] = {"microsteps": int(steps), "logical_end": int(fuel),
                             "native_seconds": float(seconds),
                             "chip_counts": ast.literal_eval(counts),
                             "program_blake3": program, "input_blake3": inputs}
        elif line.startswith("quota_source_range,"):
            _, name, start, end, first_fuel, last_fuel = line.split(",")
            sources[name]["clock_range"] = [int(start), int(end)]
            sources[name]["fuel_range"] = [int(first_fuel), int(last_fuel)]
        elif line.startswith("quota_shape,"):
            s = line.split(",", 15)
            values = [s[1]] + list(map(int, s[2:14])) + [float(s[14]), ast.literal_eval(s[15])]
            shape = dict(zip(SHAPE_KEYS, values, strict=True))
            assert len(shape["quotas"]) == len(CHIP_NAMES)
            assert sum(shape["quotas"]) == shape["microstep_slots"]
            shape["samples"] = {}
            shapes.append(shape)
        elif line.startswith("quota_sample,"):
            s = line.split(",", 8)
            stops = ast.literal_eval(s[8])
            assert len(stops) == len(CHIP_NAMES) + 2
            shape["samples"][s[1]] = {
                "complete_batches": int(s[2]), "microsteps": int(s[3]),
                "logical_steps": int(s[4]), "fetches": int(s[5]),
                "max_cells": int(s[6]), "max_parents": int(s[7]),
                "stops": {name: n for name, n in zip(
                    CHIP_NAMES + ["Cells", "Parents"], stops, strict=True) if n},
            }
    assert sources and shapes
    if expected_sources is not None:
        assert len(sources) == expected_sources
    return {"log": receipt(path), "sources": sources, "shapes": shapes}


def timing(path: Path) -> dict:
    text = path.read_text()
    exit_code = int(re.search(r"Exit status: (\d+)", text)[1])
    if exit_code:
        raise ValueError(f"failed process: {path}")
    elapsed = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)", text)[1]
    wall = 0.0
    for piece in elapsed.split(":"):
        wall = wall * 60 + float(piece)
    return {
        "command": re.search(r'Command being timed: "(.*)"', text)[1],
        "wall_seconds": wall,
        "user_seconds": float(re.search(r"User time \(seconds\): ([\d.]+)", text)[1]),
        "system_seconds": float(re.search(r"System time \(seconds\): ([\d.]+)", text)[1]),
        "max_rss_kib": int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", text)[1]),
        "swaps": int(re.search(r"Swaps: (\d+)", text)[1]),
        "exit_code": exit_code,
        "receipt": receipt(path),
    }


def leaf_receiver(root: Path, batch_class: str) -> dict:
    path = root / "receivers" / f"{batch_class}.log"
    text = passed(path)
    identity = next(records(text, "proof_setup_identity,")).split(",")
    assert identity[1] == batch_class and "leaf receiver accepted:" in text
    accepted = next(records(text, "leaf receiver accepted: "))
    return {"class": batch_class, "registry_digest": identity[2],
            "circuit_digest": identity[3], "row_variables": int(identity[4]),
            "dense_variables": int(identity[5]),
            "setup_seconds": float(re.search(r"setup_seconds=([\d.]+)", accepted)[1]),
            "verify_seconds": float(re.search(r"verify_seconds=([\d.]+)", accepted)[1]),
            "proof_bytes": int(re.search(r"bytes=(\d+)", accepted)[1]),
            "process": timing(path.with_suffix(".time")), "log": receipt(path)}


def table_costs(root: Path) -> dict:
    path = root / "table-costs.log"
    result = {}
    for line in records(passed(path), "execution_cost"):
        parts = line.split(",")
        entry = result.setdefault(parts[1], {"tables": []})
        if parts[0] == "execution_cost":
            entry["tables"].append({"table": parts[2], "rows": int(parts[3]), "dense_words": int(parts[4])})
        elif parts[0] == "execution_cost_total":
            entry.update({key: int(value) for key, value in (p.split("=") for p in parts[2:])})
            assert sum(t["dense_words"] for t in entry["tables"]) == entry["dense_words"]
    # Later revisions append named classes to the historical table census.
    assert len(result) >= 19
    return {"log": receipt(path), "classes": result,
            "note": "padded_words and boolean_words are the historical full-union layouts; the production dense commitment has 2^(dense_m-7) 128-bit words."}


def checks(root: Path) -> dict:
    tests = {}
    for name in ["stage3-paged-tests", "stage3-memory-tests", "stage3-sizing-tests", "stage4-tree-tests"]:
        path = root / f"{name}.log"
        text = passed(path)
        count = int(re.search(r"test result: ok\. (\d+) passed", text)[1])
        assert count > 0
        tests[name] = {"passed": count, "log": receipt(path)}
    lint = {}
    for name in ["stage3-clippy", "stage4-clippy"]:
        path = root / f"{name}.log"
        text = path.read_text()
        assert "Finished" in text and "error:" not in text
        lint[name] = {"arguments": "--locked --workspace --all-targets -- -D warnings", "log": receipt(path)}
    reference = {}
    for name, steps in [("arithmetic", 57), ("arrays", 15), ("bytes", 21)]:
        directory = root / "reference-fixtures" / name
        reference[name] = {"iterations": 3, "logical_steps": steps,
                           "expected_output_bytes": 78,
                           "artifacts": {p.name: receipt(p) for p in sorted(directory.iterdir()) if p.is_file()}}
    return {"ordinary_tests": tests, "clippy": lint,
            "reference_fixtures": {"executor": "lake env lean --run Tests/Ixby/Fixture.lean DIRECTORY",
                                   "result": "All three matched independently encoded canonical IXFO bytes.", "fixtures": reference}}


def words(path: Path) -> list[tuple[int, int]]:
    data = path.read_bytes()
    assert len(data) == 57 * 16
    return list(struct.iter_unpack("<QQ", data))


def leaf_run(root: Path, tag: str, extension: bool = False) -> dict:
    path = root / ("extensions" if extension else "runs") / tag
    text = passed(path.with_suffix(".log"))
    config_path = path.with_suffix(".proofs") / "config.txt"
    config = dict(line.split("=", 1) for line in config_path.read_text().splitlines())
    assert config["claim"] == "conditional execution segments"
    assert config["class"].lower() == RUNS[tag][0].replace("-", "")
    assert int(config["skip"]) == (3 if extension else 0)
    assert int(config["batches"]) == (1 if extension else 3)
    assert int(config["workers"]) == 1 and int(config["threads_per_worker"]) == 2
    samples = []
    quotas = {int(line.split(",", 2)[1]): ast.literal_eval(line.split(",", 2)[2])
              for line in records(text, "proof_quota,")}
    previous = None
    for line in records(text, "proof_sample,"):
        s = line.split(",")
        if s[1] == "batch":
            continue
        batch, worker, micro, logical = map(int, s[1:5])
        stem = path.with_suffix(".proofs") / f"{batch:010}"
        statement = words(stem.with_suffix(".statement"))
        assert statement[30][0] - statement[3][0] == micro
        assert statement[36][1] - statement[9][1] == logical
        # New binaries append fused families. These historical classes must
        # still contain only the original single-microstep rows.
        assert len(quotas[batch]) >= len(CHIP_NAMES)
        assert not any(quotas[batch][len(CHIP_NAMES):])
        assert sum(quotas[batch]) == micro
        if previous is not None:
            assert previous[:3] == statement[:3] and previous[30:] == statement[3:30]
        previous = statement
        proof = receipt(stem.with_suffix(".flock"))
        assert proof["bytes"] == int(s[8])
        samples.append({
            "batch": batch, "worker": worker, "microsteps": micro,
            "logical_steps": logical, "fetches": quotas[batch][0],
            "witness_seconds": float(s[5]), "prove_seconds": float(s[6]),
            "verify_seconds": float(s[7]), "chip_counts": quotas[batch],
            "proof": proof, "statement": receipt(stem.with_suffix(".statement")),
            "clock_range": [statement[3][0], statement[30][0]],
            "fuel_range": [statement[9][1], statement[36][1]],
        })
    assert [s["batch"] for s in samples] == ([3] if extension else [0, 1, 2])
    info = next(records(text, "proof benchmark: "))
    assert f'class={config["class"]} ' in info
    durations = {key: float(value) for key, value in
                 re.findall(r"(load_seconds|skip_seconds|native_seconds|setup_seconds)=([\d.]+)", info)}
    complete = next(records(text, "proof benchmark complete: "))
    steady = float(re.search(r"worker_wall_seconds=([\d.]+)", complete)[1])
    steps = sum(s["logical_steps"] for s in samples)
    return {
        "class": RUNS[tag][0], "workload": RUNS[tag][1],
        **durations, "worker_wall_seconds": steady,
        "logical_steps": steps, "logical_steps_per_second": steps / steady,
        "samples": samples, "process": timing(path.with_suffix(".time")),
        "configuration": config, "configuration_receipt": receipt(config_path),
        "log": receipt(path.with_suffix(".log")),
    }


def chain_run(root: Path, tag: str, leaves: dict, extension: dict) -> dict:
    path = root / "chains" / tag
    text = passed(path.with_suffix(".log"))
    assert "chain receiver rejected all 114 public-word mutations, truncation and trailing data" in text
    for attack in ["repeated", "reversed", "skipped"]:
        assert f"{attack} valid execution segments rejected" in text
    events = []
    for line in text.splitlines():
        at = line.find('{"')
        if at >= 0:
            event = json.loads(line[at:])
            if event.get("event", "").startswith("chain_"):
                events.append(event)
    assert all(e["class"] == leaves["class"] for e in events)
    assert sorted(e["leaves"] for e in events if e["event"] == "chain_setup") == [2, 4]
    assert sorted(e["leaves"] for e in events if e["event"] == "chain_proof") == [2, 2, 4]
    assert len([e for e in events if e["event"] == "chain_receiver_accepted"]) == 1
    root_setup = next(e for e in events if e["event"] == "chain_setup" and e["leaves"] == 4)
    receiver_setup = next(e for e in events if e["event"] == "chain_receiver_setup")
    assert root_setup["identity"] == receiver_setup["identity"]
    assert root_setup["geometry"] == receiver_setup["geometry"]
    assert len([e for e in events if e["event"] == "chain_leaf_setup"]) == 1
    receipts = {}
    for name, start, end in [("node-2", 0, 1), ("node-2-right", 2, 3), ("node-4", 0, 3)]:
        stem = path.with_suffix(".proofs") / name
        statement = words(stem.with_suffix(".statement"))
        first = words(root / "runs" / f"{tag}.proofs" / f"{start:010}.statement")
        last = words(root / "runs" / f"{tag}.proofs" / f"{end:010}.statement")
        assert statement == first[:30] + last[30:]
        receipts[name] = {"proof": receipt(stem.with_suffix(".flock")),
                          "statement": receipt(stem.with_suffix(".statement"))}
        event = next(e for e in events if e["event"] == "chain_proof"
                     and e["leaves"] == end - start + 1 and e.get("first_leaf", 0) == start)
        assert receipts[name]["proof"]["bytes"] == event["bytes"]
        assert event["geometry"]["children"] == ([2, 2] if name == "node-4" else [1, 1])
    accepted = next(e for e in events if e["event"] == "chain_receiver_accepted")
    assert accepted["bytes"] == receipts["node-4"]["proof"]["bytes"]
    samples = leaves["samples"] + extension["samples"]
    for a, b in zip(samples, samples[1:]):
        assert a["clock_range"][1] == b["clock_range"][0]
        assert a["fuel_range"][1] == b["fuel_range"][0]
    fourth = root / "runs" / f"{tag}.proofs" / "0000000003.flock"
    assert receipt(fourth) == extension["samples"][0]["proof"]
    proving = sum(e["seconds"] for e in events if e["event"] == "chain_proof")
    leaf_online = sum(s["witness_seconds"] + s["prove_seconds"] + s["verify_seconds"]
                      for s in samples)
    steps = sum(s["logical_steps"] for s in samples)
    return {
        "class": leaves["class"], "logical_steps": steps, "leaf_count": 4,
        "events": events, "nodes": receipts,
        "chain_prove_and_verify_seconds": proving,
        "leaf_and_chain_online_seconds": leaf_online + proving,
        "leaf_and_chain_logical_steps_per_second": steps / (leaf_online + proving),
        "excluded_from_online_rate": ["setup", "native replay", "negative checks", "fresh receiver", "source admission", "complete-run closure"],
        "negative_checks": {"nonadjacent_valid_child_pairs": 3, "expected_word_changes": 114,
                            "truncation": 1, "trailing_data": 1},
        "process": timing(path.with_suffix(".time")), "log": receipt(path.with_suffix(".log")),
    }


def full_counts(root: Path, leaves: dict, extensions: dict) -> dict:
    path = root / "full-counts.log"
    result = {}
    for line in passed(path).splitlines():
        if line.startswith("full_execution_batch,"):
            _, workload, batch_class, index, start, end, fuel_start, fuel_end = line.split(",")
            key = f"{workload}/{batch_class}"
            entry = result.setdefault(key, {"workload": workload, "class": batch_class, "batches": []})
            assert int(index) == len(entry["batches"])
            entry["batches"].append({"clock_range": [int(start), int(end)],
                                     "fuel_range": [int(fuel_start), int(fuel_end)]})
        elif line.startswith("full_execution_count,"):
            _, workload, batch_class, micro, count, logical, joins = line.split(",")
            entry = result[f"{workload}/{batch_class}"]
            entry.update({"microsteps": int(micro), "leaf_count": int(count),
                          "logical_steps": int(logical), "join_count": int(joins)})
            assert len(entry["batches"]) == int(count) and int(joins) == int(count) - 1
            assert entry["batches"][0]["clock_range"][0] == 0
            assert entry["batches"][-1]["clock_range"][1] == int(micro)
    assert len(result) == 8
    for tag, run in leaves.items():
        key = f'{run["workload"]}/{run["class"]}'
        if key not in result:
            continue
        samples = run["samples"] + extensions.get(tag, {}).get("samples", [])
        for sample in samples:
            counted = result[key]["batches"][sample["batch"]]
            assert counted["clock_range"] == sample["clock_range"]
            assert counted["fuel_range"] == sample["fuel_range"]
    return {"log": receipt(path), "runs": result,
            "validation": "Every measured independent-fixture leaf boundary matches the complete native census."}


def model(leaves: dict, extensions: dict, chains: dict, counts: dict) -> dict:
    rows = []
    for tag in CHAINS[:4]:
        leaf, chain = leaves[tag], chains[tag]
        samples = leaf["samples"] + extensions[tag]["samples"]
        leaf_seconds = sum(s["witness_seconds"] + s["prove_seconds"] + s["verify_seconds"]
                           for s in samples) / len(samples)
        joins = [e for e in chain["events"] if e["event"] == "chain_proof"]
        pair_seconds = sum(e["seconds"] for e in joins if e["leaves"] == 2) / 2
        recursive_seconds = next(e["seconds"] for e in joins if e["leaves"] == 4)
        complete = counts["runs"][f'arithmetic/{leaf["class"]}']
        n = complete["leaf_count"]
        # The CLI splits off the largest complete power-of-two prefix.
        # Its tree has floor(n/2) raw leaf pairs; the remaining joins
        # involve at least one recursive child.
        first_level = n // 2
        upper = n - 1 - first_level
        predictions = []
        for multiplier in [1, 2, 4]:
            seconds = n * leaf_seconds + first_level * pair_seconds + upper * recursive_seconds * multiplier
            predictions.append({"upper_join_cost_multiplier": multiplier,
                                "online_seconds": seconds,
                                "logical_steps_per_second": complete["logical_steps"] / seconds})
        aggregation_setup = sum(e["seconds"] for e in chain["events"] if e["event"] == "chain_setup")
        rows.append({"class": leaf["class"], "logical_steps": complete["logical_steps"],
                     "leaves": n, "raw_leaf_pair_joins": first_level, "other_joins": upper,
                     "mean_leaf_seconds": leaf_seconds, "mean_raw_leaf_join_seconds": pair_seconds,
                     "measured_recursive_join_seconds": recursive_seconds,
                     "leaf_setup_seconds": leaf["setup_seconds"],
                     "aggregation_setup_through_four_leaves_seconds": aggregation_setup,
                     "separate_leaf_and_aggregation_setup_subtotal_seconds": leaf["setup_seconds"] + aggregation_setup,
                     "predictions": predictions})
    return {"scope": "Estimates for the same complete arithmetic fixture, using exact native leaf counts and sampled proof timings; the complete fixture was not proved.",
            "assumptions": ["One sequential worker with two threads; all setups cached for online estimates.",
                            "Every leaf costs the mean of the four measured leaf proofs, including the partly occupied final leaf.",
                            "Joins above raw leaf pairs use the measured four-leaf recursive join as a proxy, multiplied by 1, 2, or 4 for sensitivity. Higher levels and mixed leaf/node joins were not measured.",
                            "Setup is reported separately. As in the CLI's separate leaf and aggregation phases, aggregation recompiles the raw leaf verifier. The setup subtotal covers those phases through four leaves; larger trees need additional setups.",
                            "Native execution, admission, final closing relation, disk I/O, and complete-run verification are excluded."],
            "runs": rows}


def selected_shapes(sweeps: list[dict], held: dict) -> dict:
    keys = [key for key in SHAPE_KEYS if key not in ["name", "census_seconds"]]
    candidates = [shape for sweep in sweeps for shape in sweep["shapes"]]
    unique = {tuple(json.dumps(shape[key], sort_keys=True) for key in keys)
              for shape in candidates}
    selected = {}
    for shape in held["shapes"]:
        matches = sorted({candidate["name"] for candidate in candidates
                          if all(shape[key] == candidate[key] for key in keys)})
        assert matches, f'no swept geometry matches {shape["name"]}'
        selected[shape["name"]] = matches
    return {"distinct_geometries": len(unique), "selected_candidate_names": selected}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    options = parser.parse_args()
    root = options.evidence
    leaves = {tag: leaf_run(root, tag) for tag in RUNS}
    extensions = {tag: leaf_run(root, tag, True) for tag in CHAINS}
    chains = {tag: chain_run(root, tag, leaves[tag], extensions[tag]) for tag in CHAINS}
    counts = full_counts(root, leaves, extensions)
    coarse, refined = census(root / "sweep3.log"), census(root / "refine.log")
    held = census(root / "holdout.log")
    for run in list(leaves.values()) + list(extensions.values()):
        for window in [coarse, refined, held]:
            source = window["sources"][run["workload"]]
            for name in ["program_blake3", "input_blake3"]:
                assert run["configuration"][name] == source[name]
    sources = {}
    for name in ["arithmetic", "arrays", "bytes", "retained"]:
        directory = root / ("retained" if name == "retained" else f"fixtures/{name}")
        sources[name] = {path.name: receipt(path) for path in sorted(directory.iterdir()) if path.is_file()}
    repository = Path(__file__).resolve().parents[2]
    source_paths = [
        ".cargo/config.toml",
        "flock-stage3/Cargo.lock",
        "flock-stage4/Cargo.lock",
        "flock-stage3/host/src/ixby/paged_exec/batch.rs",
        "flock-stage3/host/src/ixby/paged_exec/mod.rs",
        "flock-stage3/host/src/ixby/paged_exec/tuning.rs",
        "flock-stage3/host/src/ixby/paged_exec/quota_tests.rs",
        "flock-stage3/host/src/ixby/paged_exec/benchmark_tests.rs",
        "flock-stage3/host/src/ixby/memory_log/mod.rs",
        "flock-stage3/host/src/ixby/memory_log/witness.rs",
        "flock-stage3/host/src/sizing.rs",
        "flock-stage4/recursive/src/execution_tree/tests/large_execution.rs",
        "flock-stage4/recursive/src/bin/paged-execution/main.rs",
        "flock-stage4/fixtures/paged-execution-batch-sweep.py",
        "flock-stage3/profile/batch_tuning.py",
    ]
    record = {
        "format": "IxBy/execution-batch-tuning/v0", "runtime_semantics": 2, "date_utc": "2026-09-17",
        "scope": "Semantics-2 physical batch census, conditional execution leaves, four-leaf recursive trees, and explicitly modeled longer-run costs. No complete CSLib proof or new compiler export.",
        "source_base_commit": "6836a77c3f432c83c42428490e56811f4a69808d",
        "flock_revision": "b310f35f35f68095537150a1c8c0a43caca9a29e",
        "build": {"profile": "release", "locked_dependencies": True,
                  "rustc": "1.98.1 (48a229cea 2026-09-01)", "llvm": "22.1.8",
                  "target": "x86_64-unknown-linux-gnu", "rustflags": ["-Ctarget-cpu=native"]},
        "resources": {"cpu": "AMD Ryzen 9 7950X3D", "host_memory_kib": 130984484,
                      "threads_per_worker": 2, "leaf_workers": 1, "memory_max_bytes": 84 << 30,
                      "swap_max_bytes": 0, "cpu_affinity_pinned": False},
        "chip_order": CHIP_NAMES, "artifacts": sources,
        "source_files": {name: receipt(repository / name) for name in source_paths},
        "validation": checks(root),
        "census_1024_4096": coarse,
        "census_768_3072": refined,
        "holdout": held, "selection": selected_shapes([coarse, refined], held),
        "table_costs": table_costs(root),
        "leaves": leaves, "fourth_leaves": extensions, "chains": chains,
        "fresh_leaf_receivers": {name: leaf_receiver(root, name) for name in ["arrays-768", "builders-768"]},
        "complete_native_counts": counts, "longer_run_model": model(leaves, extensions, chains, counts),
        "producer_binaries": {name: receipt(root / name) for name in ["leaf-tests", "leaf-tests-final", "chain-tests"]},
        "binary_roles": {"leaf-tests": "All 35 execution leaf proofs.",
                         "leaf-tests-final": "Final census, ordinary tests, and fresh array/builder receivers.",
                         "chain-tests": "All recursive proofs and their fresh receivers."},
    }
    with options.output.open("x") as output:
        json.dump(record, output, indent=2)
        output.write("\n")


if __name__ == "__main__":
    main()
