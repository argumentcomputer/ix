#!/usr/bin/env python3
"""Check a streaming native profile against the independent compiler observer.

This checks measurements and exact block/fuel agreement, not Flock proofs.
The address-only window format deliberately cannot reconstruct proof advice.
"""
import argparse
import ast
import gzip
import json
from pathlib import Path
import struct

from batch_tuning import CHIP_NAMES, passed, receipt, records, timing


def numbers(text, length):
    values = ast.literal_eval(text)
    assert isinstance(values, list) and len(values) == length
    assert all(isinstance(n, int) and n >= 0 for n in values)
    return values


def window(path):
    """Read a bounded capture, validating its exact encoding and counters."""
    data = path.read_bytes()
    assert data[:8] == b"IXQP0001" and len(data) >= 96
    clock, fuel, length = struct.unpack_from("<QQQ", data, 72)
    assert 1 <= length <= 1_000_000 and clock + length < 1 << 59
    access_width = [1, 3, 6, 4, 4, 3, 1, 1, 1, 5, 5, 1, 2, 3, 3, 3, 7, 6,
                    3, 1, 3, 1, 1, 0, 5, 3, 2, 3, 2, 3, 1]
    at, charged = 96, 0
    counts = [0] * len(CHIP_NAMES)
    for _ in range(length):
        chip, step, count = struct.unpack_from("BBB", data, at)
        assert chip < len(counts) and step <= 1 and count == access_width[chip]
        at += 3
        for _ in range(count):
            address, = struct.unpack_from("<Q", data, at)
            assert address < 1 << 40
            at += 8
        counts[chip] += 1
        charged += step
    assert at == len(data)
    return {"file": path.name, **receipt(path),
            "program_blake3": data[8:40].hex(), "input_blake3": data[40:72].hex(),
            "clock_range": [clock, clock + length],
            "fuel_range": [fuel, fuel + charged], "chip_counts": counts}


def profile(args):
    text = passed(args.log)
    source, = records(text, "native_profile_source,")
    _, program, inputs, output, initial_cells, functions = source.split(",")
    functions = int(functions)
    complete, = records(text, "native_profile_complete,")
    fields = complete.split(",", 8)
    assert fields[1] == "true", "this report requires completed native execution"
    phase_text, chip_text = fields[8].split("],", 1)
    phases, chips = numbers(phase_text + "]", 5), numbers(chip_text, 31)
    clock, fuel, heap, byte_cells, overlay = map(int, fields[2:7])
    assert sum(chips) == clock and sum(phases) == fuel
    observer = json.loads(gzip.decompress(args.observer.read_bytes()))
    inventory = json.loads(args.inventory.read_text())["function_inventory"]
    assert observer["completed"] and len(inventory) == functions
    assert fuel == observer["reference_transitions"]
    assert [phases[0], phases[1], phases[3]] == observer["control_counts_eval_ret_apply"]
    assert phases[2] == phases[4] == 0
    blocks = {}
    for line in records(text, "native_profile_blocks,"):
        _, index, counts = line.split(",", 2)
        index = int(index)
        assert index not in blocks
        blocks[index] = numbers(counts, inventory[index]["blocks"])
    assert sorted(blocks) == list(range(functions))
    flattened = [n for i in range(functions) for n in blocks[i]]
    assert flattened == observer["block_counts"], "native/compiler block counts differ"
    assert sum(flattened) == chips[0] == phases[0]
    by_function = []
    for line in records(text, "native_profile_function,"):
        s = line.split(",", 8)
        index = int(s[1])
        assert index == len(by_function)
        entry = {"index": index,
                 "name": inventory[index]["name"] if index < functions else "Return/Apply",
                 "first_clock": None if s[2] == "none" else int(s[2]),
                 "reads": int(s[3]), "writes": int(s[4]), "zero_accesses": int(s[5]),
                 "heap_cells": int(s[6]), "byte_cells": int(s[7]),
                 "chip_counts": numbers(s[8], 31)}
        by_function.append(entry)
    assert len(by_function) == functions + 1
    assert [sum(f["chip_counts"][i] for f in by_function) for i in range(31)] == chips
    initial_heap = heap - sum(f["heap_cells"] for f in by_function)
    initial_bytes = byte_cells - sum(f["byte_cells"] for f in by_function)
    assert initial_heap >= 0 and initial_bytes >= 0
    captures = []
    for line in records(text, "native_profile_window,"):
        _, name, start, end, first, last = line.split(",")
        capture = window(args.windows / name)
        assert capture["clock_range"] == [int(start), int(end)]
        assert capture["fuel_range"] == [int(first), int(last)]
        assert capture["program_blake3"] == program and capture["input_blake3"] == inputs
        captures.append(capture)
    progress = []
    for line in records(text, "native_profile_progress,"):
        s = line.split(",", 7)
        progress.append({"clock": int(s[1]), "logical_steps": int(s[2]),
                         "heap_cells": int(s[3]), "byte_cells": int(s[4]),
                         "overlay_cells": int(s[5]), "seconds": float(s[6]),
                         "chip_counts": numbers(s[7], 31)})
    return {"format": "IxBy/cslib-native-physical-profile/v0",
            "scope": "Complete native execution, exact output checked by the producer and all block/fuel counts checked against the compiler observer. No execution proof.",
            "producer_binary": receipt(args.binary), "log": receipt(args.log),
            "process": timing(args.time),
            "artifacts": {name: receipt(args.fixture / name) for name in
                          ["program.ixby", "input.ixbi", "output.ixbo"]},
            "program_blake3": program, "input_blake3": inputs, "output_blake3": output,
            "observer": receipt(args.observer), "inventory": receipt(args.inventory),
            "compiler_block_counts_checked": len(flattened), "functions": functions,
            "microsteps": clock, "logical_steps": fuel,
            "initial_cells": int(initial_cells), "initial_heap_cells": initial_heap,
            "initial_byte_cells": initial_bytes, "heap_cells": heap,
            "byte_cells": byte_cells, "overlay_cells": overlay,
            "native_seconds": float(fields[7]),
            "phase_order": ["Eval", "Return", "Halted", "Apply", "Copy"],
            "logical_phase_counts": phases, "chip_order": CHIP_NAMES,
            "chip_counts": chips, "function_costs": by_function,
            "progress": progress, "captured_windows": captures}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ["log", "time", "binary", "fixture", "observer", "inventory", "windows", "out"]:
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    result = profile(args)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
