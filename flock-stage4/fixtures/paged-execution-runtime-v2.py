#!/usr/bin/env python3
"""Write an independent IXBF semantics-2 array/builder/conversion fixture.

Exercises every new primitive, an input array, persistent nested updates,
two unaligned builder chunks, and a slice of the frozen bytes. The expected
output is computed directly below, without the IxBy interpreter or compiler.
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


def word(value: int) -> bytes:
    return b"\1\3" + struct.pack("<I", value)


def byte_literal(data: bytes) -> bytes:
    return b"\1\6" + natural(len(data)) + data


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--fuel", type=int, choices=(14, 15), default=15)
    options = parser.parse_args()
    first = bytes(range(31))
    second = bytes((i * 7 + 131) % 256 for i in range(34))
    operations = [
        (49, []),                                      # local1 = empty array
        (53, [local(1), nat(37)]),                      # local2 = [37]
        (52, [local(0), nat(1), local(2)]),              # local3 = [7, [37]]
        (51, [local(3), nat(1)]),                       # local4 = [37]
        (50, [local(4)]),                              # local5 = Nat 1
        (48, [nat((1 << 128) - 1)]),                    # local6 = Nat reduced to field
        (47, [local(6)]),                              # local7 = canonical field Nat
        (54, []),                                      # local8 = empty builder
        (55, [local(8), byte_literal(first)]),          # local9 = first chunk
        (55, [local(9), byte_literal(second)]),         # local10 = both chunks
        (57, [local(10)]),                             # local11 = Nat 65
        (56, [local(10)]),                             # local12 = frozen 65 bytes
        (42, [local(12), word(1), word(63)]),            # local13 = shared slice
    ]
    limits = [1, 0, 14, 14, 3, 0, 8, 128, 0, 128]
    program = header(b"IXBF") + b"".join(map(natural, limits + [options.fuel]))
    program += bytes([0, 0, 1, 1, 0, 14])
    for index, (opcode, arguments) in enumerate(operations):
        program += natural(index + 1) + bytes([0, 1, opcode])
        program += natural(len(arguments)) + b"".join(arguments) + natural(index + 1)
    program += bytes([14, 1]) + local(13)
    inputs = header(b"IXFI") + bytes([1, 4, 2, 0, 0, 7, 0, 0, 9])
    expected = (first + second)[1:64]
    output = header(b"IXFO") + bytes([0, 6]) + natural(len(expected)) + expected
    profile = b"IXFP" + struct.pack("<III", 0, 1, 2)
    profile += b"".join(n.to_bytes(16, "little") for n in limits)
    profile += struct.pack("<Q", options.fuel)
    artifacts = {"program.ixby": program, "input.ixbi": inputs,
                 "output.ixbo": output, "profile.ixfp": profile}
    options.out.mkdir(parents=True, exist_ok=False)
    for name, data in artifacts.items():
        (options.out / name).write_bytes(data)
    print(json.dumps({"artifacts": {name: len(data) for name, data in artifacts.items()},
                      "expected_logical_steps": 15, "fuel": options.fuel,
                      "limits": limits, "opcodes": [op for op, _ in operations],
                      "hex": {name: data.hex() for name, data in artifacts.items()},
                      "directory": str(options.out)}))


if __name__ == "__main__":
    main()
