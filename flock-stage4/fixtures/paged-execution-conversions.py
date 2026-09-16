#!/usr/bin/env python3
"""Write an independently encoded IXBF semantics-1 conversion fixture.

Nat input 2^65 + 37 goes through NatToWord32, Word32ToNat, NatAdd 5,
NatToWord32, and Word32ToBytes. The expected output is [42, 0, 0, 0].
The six instructions plus the final return-to-halt transition take seven
logical steps. --fuel 6 generates the otherwise identical failing fixture.
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
    parser.add_argument("--fuel", type=int, choices=(6, 7), default=7)
    options = parser.parse_args()

    limits = [1, 0, 6, 6, 2, 0, 8, 128, 0, 64]
    program = header(b"IXBF") + b"".join(map(natural, limits + [options.fuel]))
    program += bytes([0, 0, 1, 1, 0, 6])  # entry, ctors, funcs, arity, entry, blocks
    program += bytes([1, 0, 1, 45, 1, 0, 0, 1])  # local1 = natToWord32 local0
    program += bytes([2, 0, 1, 46, 1, 0, 1, 2])  # local2 = word32ToNat local1
    program += bytes([3, 0, 1, 0, 2, 0, 2, 1, 0, 5, 3])  # local3 = natAdd local2 5
    program += bytes([4, 0, 1, 45, 1, 0, 3, 4])  # local4 = natToWord32 local3
    program += bytes([5, 0, 1, 21, 1, 0, 4, 5])  # local5 = word32ToBytes local4
    program += bytes([6, 1, 0, 5])  # return local5

    inputs = header(b"IXFI") + bytes([1, 0, 0]) + natural((1 << 65) + 37)
    output = header(b"IXFO") + bytes([0, 6, 4, 42, 0, 0, 0])
    options.out.mkdir(parents=True, exist_ok=False)
    artifacts = {"program.ixby": program, "input.ixbi": inputs, "output.ixbo": output}
    for name, data in artifacts.items():
        (options.out / name).write_bytes(data)
    print(json.dumps({"artifacts": {name: len(data) for name, data in artifacts.items()},
                      "expected_logical_steps": 7, "fuel": options.fuel,
                      "program_hex": program.hex(), "input_hex": inputs.hex(),
                      "output_hex": output.hex(), "directory": str(options.out)}))


if __name__ == "__main__":
    main()
