#!/usr/bin/env python3
"""Independently decode and validate a Compilatrix full-runtime Ixby binary."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys


MODULUS = 18446744069414584321
LIMIT_NAMES = (
    "functions", "constructors", "blocks", "locals", "operands",
    "continuations", "inputNodes", "natBits", "stringBytes", "byteArrayBytes",
)
PRIMITIVES = (
    "natAdd natSub natMul natDiv natMod natEq natLt strAppend strLength strEq "
    "word32Add word32Sub word32Mul word32And word32Or word32Xor word32Shl "
    "word32Shr word32Rotr word32Eq word32Lt word32ToBytes bytesToWord32 word32ToField "
    "fieldAdd fieldSub fieldMul fieldInverse fieldEq fieldToBytes bytesToField "
    "extAdd extSub extMul extInverse extEq extPack extFst extSnd "
    "bytesLength bytesGet bytesAppend bytesSlice bytesEq blake3 natToWord32 word32ToNat fieldToNat natToField arrayEmpty arrayLength arrayGet arraySet arrayPush byteBuilderEmpty byteBuilderAppend byteBuilderFreeze byteBuilderLength"
).split()
UNARY = set((
    "strLength word32ToBytes bytesToWord32 word32ToField fieldInverse fieldToBytes "
    "bytesToField extInverse extFst extSnd bytesLength blake3 natToWord32 word32ToNat fieldToNat natToField arrayLength byteBuilderFreeze byteBuilderLength"
).split())
OP_NAMES = "copy primitive construct project closure call callSelf apply".split()
INSTR_NAMES = "letOp ret tailCall tailCallSelf tailApply caseCtor caseNat branch".split()


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Reader:
    def __init__(self, data):
        require(len(data) <= 67108864, "binary exceeds loader byte limit")
        self.data = data
        self.pos = 0
        self.limits = {}

    def take(self, count):
        require(count <= len(self.data) - self.pos, "truncated binary")
        result = self.data[self.pos:self.pos + count]
        self.pos += count
        return result

    def byte(self):
        return self.take(1)[0]

    def fixed(self, width):
        return int.from_bytes(self.take(width), "little")

    def natural(self):
        value = 0
        for i in range(8192):
            byte = self.byte()
            value |= (byte & 127) << (7 * i)
            if byte < 128:
                require(i == 0 or byte != 0, "nonminimal natural")
                return value
        raise ValueError("natural exceeds loader integer limit")

    def vector(self, read, bound):
        count = self.natural()
        require(count <= min(bound, len(self.data) - self.pos), "invalid vector count")
        return [read() for _ in range(count)]

    def field(self):
        value = self.fixed(8)
        require(value < MODULUS, "noncanonical field")
        return value

    def scalar(self):
        tag = self.byte()
        if tag == 0:
            value = self.natural()
            require(value.bit_length() <= self.limits["natBits"], "Nat capacity exceeded")
        elif tag == 1:
            size = self.natural()
            require(size <= self.limits["stringBytes"], "string capacity exceeded")
            value = self.take(size).decode("utf-8", errors="strict")
        elif tag == 2:
            value = self.byte()
            require(value in (0, 1), "noncanonical Boolean")
        elif tag == 3:
            value = self.fixed(4)
        elif tag == 4:
            value = self.field()
        elif tag == 5:
            value = (self.field(), self.field())
        elif tag == 6:
            size = self.natural()
            require(size <= self.limits["byteArrayBytes"], "byte capacity exceeded")
            value = self.take(size)
        else:
            raise ValueError(f"unknown scalar tag {tag}")
        return tag, value

    def operand(self):
        tag = self.byte()
        if tag == 0:
            return tag, self.natural()
        if tag == 1:
            return tag, self.scalar()
        require(tag == 2, f"unknown operand tag {tag}")
        return tag, None

    def operands(self):
        return self.vector(self.operand, self.limits["operands"])

    def operation(self):
        tag = self.byte()
        if tag == 0:
            return tag, self.operand()
        if tag == 1:
            opcode = self.byte()
            require(opcode < len(PRIMITIVES), f"unknown primitive {opcode}")
            return tag, opcode, self.operands()
        if tag in (2, 4, 5):
            return tag, self.natural(), self.operands()
        if tag == 3:
            return tag, self.operand(), self.natural()
        if tag == 6:
            return tag, self.operands()
        require(tag == 7, f"unknown operation {tag}")
        return tag, self.operand(), self.operands()

    def instruction(self):
        tag = self.byte()
        if tag == 0:
            return tag, self.operation(), self.natural()
        if tag == 1:
            return tag, self.operand()
        if tag == 2:
            return tag, self.natural(), self.operands()
        if tag == 3:
            return tag, self.operands()
        if tag == 4:
            return tag, self.operand(), self.operands()
        if tag == 5:
            value = self.operand()
            alts = self.vector(lambda: (self.natural(), self.natural()), self.limits["constructors"])
            return tag, value, alts
        require(tag in (6, 7), f"unknown instruction {tag}")
        return tag, self.operand(), self.natural(), self.natural()

    def function(self):
        arity, entry = self.natural(), self.natural()
        blocks = self.vector(lambda: (self.natural(), self.instruction()), self.limits["blocks"])
        return arity, entry, blocks

    def artifact(self):
        require(self.take(4) == b"IXBF", "wrong binary magic")
        require(self.fixed(4) == 1 and self.fixed(4) == 2, "unsupported binary version")
        self.limits = {name: self.natural() for name in LIMIT_NAMES}
        max_steps, entry = self.natural(), self.natural()
        constructors = self.vector(
            lambda: ((self.fixed(32), self.natural(), self.natural()), self.natural()),
            self.limits["constructors"],
        )
        functions = self.vector(self.function, self.limits["functions"])
        require(self.pos == len(self.data), "trailing binary bytes")
        return max_steps, entry, constructors, functions


def inspect(data):
    reader = Reader(data)
    max_steps, entry, constructors, functions = reader.artifact()
    limits = reader.limits
    require(entry < len(functions), "invalid entry function")
    require(len({c[0] for c in constructors}) == len(constructors), "duplicate constructor identity")
    require(all(c[1] <= limits["operands"] for c in constructors), "constructor arity limit")
    instruction_counts, primitive_counts = Counter(), Counter()

    def operand(value, locals_count):
        require(value[0] != 0 or value[1] < locals_count, "invalid local")

    def operands(args, locals_count):
        require(len(args) <= limits["operands"], "operand limit")
        for value in args:
            operand(value, locals_count)

    def call(callee, args, locals_count, closure=False):
        operands(args, locals_count)
        require(callee < len(functions), "invalid callee")
        arity = functions[callee][0]
        require(len(args) < arity if closure else len(args) == arity, "invalid call arity")

    for self_id, (arity, first, blocks) in enumerate(functions):
        require(arity <= min(limits["locals"], limits["operands"]), "function arity limit")

        def target(index, expected):
            require(index < len(blocks) and blocks[index][0] == expected, "invalid block frame")

        target(first, arity)
        for locals_count, instruction in blocks:
            require(locals_count <= limits["locals"], "local limit")
            tag = instruction[0]
            if tag == 0:
                op, next_block = instruction[1:]
                op_tag = op[0]
                instruction_counts[OP_NAMES[op_tag]] += 1
                target(next_block, locals_count + 1)
                if op_tag in (0, 3):
                    operand(op[1], locals_count)
                elif op_tag == 1:
                    name = PRIMITIVES[op[1]]
                    primitive_counts["Ix.Ixby.Primitive." + name] += 1
                    operands(op[2], locals_count)
                    require(len(op[2]) == (0 if name in ("arrayEmpty", "byteBuilderEmpty") else 1 if name in UNARY else 3 if name in ("bytesSlice", "arraySet") else 2), "primitive arity")
                elif op_tag == 2:
                    operands(op[2], locals_count)
                    require(op[1] < len(constructors) and len(op[2]) == constructors[op[1]][1], "constructor arity")
                elif op_tag in (4, 5):
                    call(op[1], op[2], locals_count, closure=op_tag == 4)
                elif op_tag == 6:
                    call(self_id, op[1], locals_count)
                else:
                    operand(op[1], locals_count)
                    operands(op[2], locals_count)
                continue
            instruction_counts[INSTR_NAMES[tag]] += 1
            if tag == 1:
                operand(instruction[1], locals_count)
            elif tag == 2:
                call(instruction[1], instruction[2], locals_count)
            elif tag == 3:
                call(self_id, instruction[1], locals_count)
            elif tag == 4:
                operand(instruction[1], locals_count)
                operands(instruction[2], locals_count)
            elif tag == 5:
                operand(instruction[1], locals_count)
                alts = instruction[2]
                require(len({c for c, _ in alts}) == len(alts), "duplicate case")
                for ctor, block in alts:
                    require(ctor < len(constructors), "unknown case constructor")
                    target(block, locals_count + constructors[ctor][1])
            else:
                operand(instruction[1], locals_count)
                target(instruction[2], locals_count)
                target(instruction[3], locals_count + (tag == 6))
    return {
        "artifact": {"format": "compilatrix-ixby-binary/1", "program_semantics": 2, "bytes": len(data),
                     "sha256": hashlib.sha256(data).hexdigest(), "max_steps": max_steps},
        "entry": entry, "functions": len(functions), "constructors": len(constructors),
        "blocks": sum(len(f[2]) for f in functions),
        "maximum_function_blocks": max(len(f[2]) for f in functions),
        "maximum_function_arity": max(f[0] for f in functions),
        "maximum_frame_locals": max(b[0] for f in functions for b in f[2]),
        "reference_limits": limits, "instruction_counts": dict(instruction_counts),
        "primitive_counts": dict(primitive_counts),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("image", type=Path)
    parser.add_argument("--expected", type=Path, help="compare every decoded inventory field")
    args = parser.parse_args()
    result = inspect(args.image.read_bytes())
    if args.expected:
        expected = json.loads(args.expected.read_text())
        for key, value in result.items():
            require(expected.get(key) == value, f"inventory mismatch: {key}")
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print(f"inspect-ixby: {error}", file=sys.stderr)
        raise SystemExit(1)
