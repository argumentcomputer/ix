#!/usr/bin/env python3
"""Write a canonical original-format fixture with repeated tail calls.

The function takes (Bytes, Nat), cases on the natural and tail-calls itself
with its predecessor. At zero it returns the original Bytes. The 40-iteration
input takes 83 logical steps, including the final return-to-halt transition,
and crosses several fixed execution batches.
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
    return magic + struct.pack("<II", 1, 1 if magic == b"IXBF" else 0)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--fuel", type=int, choices=(82, 83), default=83,
                        help="83 completes; 82 tests fuel exhaustion")
    options = parser.parse_args()

    limits = [1, 0, 3, 3, 2, 0, 8, 4096, 64, 64]
    program = header(b"IXBF") + b"".join(map(natural, limits + [options.fuel]))
    # Program entry 0, no constructors, one function: arity 2, entry 0,
    # three blocks. Each block starts with its exact local count.
    program += bytes([0, 0, 1, 2, 0, 3])
    program += bytes([2, 6, 0, 1, 1, 2])  # caseNat local1 -> blocks 1 / 2
    program += bytes([2, 1, 0, 0])  # return local0
    program += bytes([3, 3, 2, 0, 0, 0, 2])  # tailCallSelf [local0, local2]

    payload = bytes((i * 13 + 7) % 256 for i in range(34))
    value = bytes([0, 6]) + natural(len(payload)) + payload
    inputs = header(b"IXFI") + bytes([2]) + value + bytes([0, 0, 40])
    output = header(b"IXFO") + value
    options.out.mkdir(parents=True, exist_ok=False)
    artifacts = {"program.ixby": program, "input.ixbi": inputs, "output.ixbo": output}
    for name, data in artifacts.items():
        (options.out / name).write_bytes(data)
    print(json.dumps({"artifacts": {name: len(data) for name, data in artifacts.items()},
                      "expected_logical_steps": 83, "fuel": options.fuel,
                      "directory": str(options.out)}))


if __name__ == "__main__":
    main()
