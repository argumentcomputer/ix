#!/usr/bin/env python3
"""Independent semantics-2 loops for physical batch measurements.

All loops return their original Bytes argument. Arithmetic updates a Nat;
arrays repeatedly update and read a persistent 64-element array; bytes builds
and freezes two chunks each iteration. These are synthetic workloads, not
new Compilatrix exports or measurements of complete CSLib execution.
"""

import argparse
import json
from pathlib import Path
import struct


def natural(value: int) -> bytes:
    result = bytearray()
    while value >= 128:
        result.append((value & 127) | 128)
        value >>= 7
    result.append(value)
    return bytes(result)


def header(magic: bytes) -> bytes:
    return magic + struct.pack("<II", 1, 2)


def local(index: int) -> bytes:
    return b"\0" + natural(index)


def nat(value: int) -> bytes:
    return b"\1\0" + natural(value)


def fixture(workload: str, iterations: int) -> tuple[dict[str, bytes], int]:
    payload = bytes((i * 13 + 7) % 256 for i in range(63))
    value = bytes([0, 6]) + natural(len(payload)) + payload
    if workload == "arithmetic":
        operations = [(0, [local(2 if i == 0 else 3 + i), nat(i + 1)])
                      for i in range(16)]
        state = bytes([0, 0, 0])
        next_state = local(19)
    elif workload == "arrays":
        operations = [(52, [local(2), nat(31), nat(7)]),
                      (51, [local(4), nat(31)])]
        state = bytes([4, 64]) + b"".join(bytes([0, 0]) + natural(i) for i in range(64))
        next_state = local(4)
    elif workload == "bytes":
        operations = [(54, []), (55, [local(4), local(0)]),
                      (55, [local(5), local(0)]), (56, [local(6)])]
        state = bytes([0, 0, 0])
        next_state = local(2)
    else:
        raise ValueError(workload)
    steps = (len(operations) + 2) * iterations + 3
    blocks = len(operations) + 3
    limits = [1, 0, blocks, len(operations) + 4, 3, 0, 128, 128, 0, 256]
    program = header(b"IXBF") + b"".join(map(natural, limits + [steps]))
    program += bytes([0, 0, 1, 3, 0]) + natural(blocks)
    program += bytes([3, 6]) + local(1) + bytes([1, 2])
    program += bytes([3, 1]) + local(0)
    for i, (opcode, args) in enumerate(operations):
        program += natural(4 + i) + bytes([0, 1, opcode])
        program += natural(len(args)) + b"".join(args) + natural(3 + i)
    program += natural(len(operations) + 4) + bytes([3, 3])
    program += local(0) + local(3) + next_state
    inputs = header(b"IXFI") + bytes([3]) + value + bytes([0, 0]) + natural(iterations) + state
    output = header(b"IXFO") + value
    profile = b"IXFP" + struct.pack("<III", 0, 1, 2)
    profile += b"".join(n.to_bytes(16, "little") for n in limits) + struct.pack("<Q", steps)
    return {"program.ixby": program, "input.ixbi": inputs,
            "output.ixbo": output, "profile.ixfp": profile}, steps


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--iterations", type=int, default=4096)
    options = parser.parse_args()
    if not 1 <= options.iterations <= 1_000_000:
        parser.error("iterations must be in 1..1,000,000")
    options.out.mkdir(parents=True, exist_ok=False)
    report = {}
    for workload in ("arithmetic", "arrays", "bytes"):
        artifacts, steps = fixture(workload, options.iterations)
        directory = options.out / workload
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        report[workload] = {"logical_steps": steps, "iterations": options.iterations,
                            "bytes": {name: len(data) for name, data in artifacts.items()}}
    print(json.dumps(report))


if __name__ == "__main__":
    main()
