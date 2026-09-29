# Complete functional Ixby binary, version 1

`Compilatrix.Ixby.Binary` serializes the complete functional runtime from the
unchanged [pinned Ixby reference](../vendor/ixby/upstream.json). It covers all
seven scalar kinds, all 58 primitives, and every operation and instruction.
It includes persistent array values, execution limits, and maximum transition
count. Internal byte builders are rejected recursively by serialization.
Current artifacts use format 1 and semantics 2, matching the pinned upstream
functional codec. Physical prover admission remains a separate constraint.

The Stage2 handoff is [stage2.ixby](../fixtures/ixby-stage2/stage2.ixby), with
[reference-inventory.json](../fixtures/ixby-stage2/reference-inventory.json):

| Property | Value |
| --- | --- |
| Bytes | 991,071 |
| SHA-256 | `2231dc101b3aa17a95d1cc347dcd5c1bf0f7ab7b4b2b6b6300b1c1c3aff674b4` |
| Entry | Function 669, arity 2 |
| Functions / blocks / constructor layouts | 670 / 5,824 / 140 |
| Maximum reference transitions | 16,000,000,000 |

Both original keys, entrypoints 755/243, and the fixed verifier configuration
are embedded in the binary. Arguments are raw public claim bytes and raw
private native multiproof bytes, each a `Value.scalar (.bytes ...)`.
Success returns raw claim bytes; rejection returns `Value.erased`.

The compiler binds [certified row hashing](ixby-row-hash.md) and
[fixed-width integer writes](ixby-shift-width.md), selects
[FRI loop fusion by source equality](ixby-fri-fusion.md), emits
[certified single-dispatch array reads](ixby-array-read.md)
and applies [certified leaf-call inlining](ixby-inline.md), then produces the
binary and manifest in one command:

```sh
lake build stage2-ixby ixby-exec
lake exe stage2-ixby fixtures/ixby-stage2 compile /tmp/stage2.ixby
python3 scripts/inspect_ixby.py /tmp/stage2.ixby --expected /tmp/stage2.ixby.json
```

The independent Python reader checks the complete instruction graph, scalar
encodings, constructor identities, call arities, locals, and successor frame
contracts. It reproduces inventory fields directly from the binary.
`ixby-exec` loads the binary and runs the kernel-proved chunked implementation
of the reference evaluator without loading Lean source declarations:

```sh
.lake/build/bin/ixby-exec program.ixby input.ixbi output.ixbo execution.json
```

## Encoding conventions

All tags and primitive opcodes are single bytes. `nat` means minimal unsigned
LEB128: seven payload bits per byte, least significant group first; bit 7 marks
continuation. Zero is `00`. A multi-byte value with a final zero payload is
rejected. No format-level Word32 bound applies to naturals, lengths, indices,
constructor members/tags, execution limits, or maximum steps.

`u32`, `u64`, and `u256` are exactly 4, 8, and 32 little-endian bytes.
`vector(T)` is `nat count` followed by exactly that many `T` values.
`bytes` is `nat length` followed by the uninterpreted bytes.
Strings use the same length prefix followed by strictly valid UTF-8; invalid
UTF-8 is rejected. Counts are checked against applicable limits and remaining
file bytes before iterating. Decoders do not preallocate from an unchecked
count. Every file must end exactly after its payload.

A header is four ASCII magic bytes, `u32 formatVersion = 1`, and
`u32 semanticsVersion = 2`. One semantics constant applies to all three files:

| Artifact | Twelve-byte header |
| --- | --- |
| Program | `49 58 42 46 01 00 00 00 02 00 00 00` |
| Input | `49 58 46 49 01 00 00 00 02 00 00 00` |
| Output | `49 58 46 4f 01 00 00 00 02 00 00 00` |

Semantics 0 and 1 reject for every artifact, even when all instructions use
older opcodes. The old `IXBY`/`IXBP` formats and semantic profile selectors
are retired, with no legacy fallback.

## Program file: `IXBF`

The fields occur in this exact order:

```text
header("IXBF")
nat limits.functions
nat limits.constructors
nat limits.blocks
nat limits.locals
nat limits.operands
nat limits.continuations
nat limits.inputNodes
nat limits.natBits
nat limits.stringBytes
nat limits.byteArrayBytes
nat maxSteps
nat program.entry
vector(ConstructorDeclaration) program.constructors
vector(Function) program.functions

ConstructorId          = u256 block, nat member, nat tag
ConstructorDeclaration = ConstructorId id, nat fields
Function               = nat arity, nat entry, vector(Block) blocks
Block                  = nat locals, Instruction instruction
Alternative            = nat constructorIndex, nat targetBlock
```

Function and constructor references are zero-based array indices. Block targets
are zero-based indices within the current function. A `ConstructorId` is a
semantic identity carried by a value; it is distinct from a constructor index.
The Stage2 compiler's identities are local layouts rather than authenticated
source declaration addresses.

The decoder runs the unchanged `validateProgram` before admitting the artifact.
This checks scalar capacities, identities, every reference and operand, function
and primitive arities, entry frames, and all continuation block frames.
Capacities apply exactly as defined by the reference: block count is per
function, locals are per frame, and Nat capacity bounds scalar bit width.

## Scalars, operands, operations, and instructions

| Scalar tag | Payload |
| ---: | --- |
| 0 | `nat` |
| 1 | UTF-8 string bytes |
| 2 | One byte, exactly 0 or 1 |
| 3 | `u32` Word32 |
| 4 | `u64` Goldilocks value, strictly below 18,446,744,069,414,584,321 |
| 5 | Two canonical Goldilocks values, `c0` then `c1`, for `c0 + c1·X`, `X² = 7` |
| 6 | `bytes` |

| Operand tag | Payload |
| ---: | --- |
| 0 | `nat localSlot` |
| 1 | Scalar |
| 2 | Empty: erased |

| Operation tag | Payload |
| ---: | --- |
| 0: copy | Operand |
| 1: primitive | Byte opcode, `vector(Operand)` arguments |
| 2: construct | `nat constructorIndex`, `vector(Operand)` fields |
| 3: project | Operand value, `nat fieldIndex` |
| 4: closure | `nat functionIndex`, `vector(Operand)` captures |
| 5: call | `nat functionIndex`, `vector(Operand)` arguments |
| 6: callSelf | `vector(Operand)` arguments |
| 7: apply | Operand function, `vector(Operand)` arguments |

| Instruction tag | Payload |
| ---: | --- |
| 0: letOp | Operation, `nat nextBlock` |
| 1: ret | Operand |
| 2: tailCall | `nat functionIndex`, `vector(Operand)` arguments |
| 3: tailCallSelf | `vector(Operand)` arguments |
| 4: tailApply | Operand function, `vector(Operand)` arguments |
| 5: caseCtor | Operand value, `vector(Alternative)` alternatives |
| 6: caseNat | Operand value, `nat ifZero`, `nat ifSucc` |
| 7: branch | Operand condition, `nat ifTrue`, `nat ifFalse` |

Primitive opcodes are fixed explicitly by this version:

```text
 0 natAdd          15 word32Xor       30 bytesToField
 1 natSub          16 word32Shl       31 extAdd
 2 natMul          17 word32Shr       32 extSub
 3 natDiv          18 word32Rotr      33 extMul
 4 natMod          19 word32Eq        34 extInverse
 5 natEq           20 word32Lt        35 extEq
 6 natLt           21 word32ToBytes   36 extPack
 7 strAppend       22 bytesToWord32   37 extFst
 8 strLength       23 word32ToField   38 extSnd
 9 strEq           24 fieldAdd        39 bytesLength
10 word32Add       25 fieldSub        40 bytesGet
11 word32Sub       26 fieldMul        41 bytesAppend
12 word32Mul       27 fieldInverse    42 bytesSlice
13 word32And       28 fieldEq         43 bytesEq
14 word32Or        29 fieldToBytes    44 blake3
45 natToWord32     46 word32ToNat     47 fieldToNat
48 natToField      49 arrayEmpty      50 arrayLength
51 arrayGet        52 arraySet        53 arrayPush
54 byteBuilderEmpty 55 byteBuilderAppend
56 byteBuilderFreeze 57 byteBuilderLength
```

The theorem `primitiveOpcode_decodes` covers every primitive by cases.
Arithmetic, word shifts, field zero inverses, string length, byte slicing,
BLAKE3, partial application, oversaturation, and error behavior are those of
[Primitive](../vendor/ixby/Ix/Ixby/Primitive.lean) and the reference evaluator.
The binary format adds serialization, not new evaluation rules.

All four scalar conversions at 45–48 are unary. `natToWord32` validates its
Nat source before returning `n mod 2^32`; an over-limit Nat cannot be made
admissible by truncation. `word32ToNat` returns the exact unsigned value and
validates that result against `natBits`. Zero fits a zero-bit Nat capacity.
Arity checking precedes scalar validation, followed by source-type checking
and result validation. `fieldToNat` returns the canonical representative;
`natToField` reduces modulo the Goldilocks modulus. Wrong types have no
implicit coercion. Opcodes 58–255 reject.

The operation encodings for local slots 0 and 1 are respectively
`01 2d 01 00 00` and `01 2e 01 00 01`. These exclude the surrounding instruction
tag, block frame and successor.

Downstream Flock profiles retain the 184-byte `IXFP` layout: profile revision
0, program format 1, **semantics 2 at byte offset 12**, ten little-endian
u128 limits, then u64 maximum steps. Regenerate the profile, program commitment,
input/output commitments and final statement. Proof setups and proofs must
bind the current artifacts. The
paged backend's immediate Nat128 restriction is separate from the reference
machine's declared Nat capacity.

The [integration record](ixby-runtime-v2.md) includes regenerated Stage2 and
CSLib artifacts, measured transition counts, and an independently generated
conversion fixture with its expected profile and statement.

## Input and output files

```text
Input  = header("IXFI"), vector(Value) arguments
Output = header("IXFO"), Value result
```

| Value tag | Payload |
| ---: | --- |
| 0 | Scalar |
| 1 | ConstructorId, `vector(Value)` fields |
| 2 | `nat functionIndex`, `vector(Value)` captured arguments |
| 3 | Empty: erased |
| 4 | `vector(Value)` native persistent array |

Array length is strictly below `2^32`; elements share input-node and depth
budgets with the other value kinds. Arrays may be nested inside arrays,
constructors, or PAPs. Builders are internal values and cannot be serialized,
including through any nested value. Wire tags 5–255 reject.

`arrayGet` and `arraySet` check full Nat indices before addressing. `arrayPush`
rejects a resulting length of `2^32`. These operations preserve prior aliases.
The two empty primitives have arity zero but still bind a result local.
Builder append accepts Builder and Bytes and checks the resulting byte limit;
freeze returns Bytes, and length returns a capacity-checked Nat. Checked
`bytesSlice` takes Bytes and two Word32 values; its sum uses nonwrapping bounds.

Input arity must equal the entry function's arity. Both input and output
admission use the program's constructor, PAP, scalar, and `inputNodes` bounds.
Files are interpreted with a supplied program artifact; the transport does not
embed a program digest. A caller that requires identity binding must check the
artifact digest separately.

For the retained Stage2 smoke fixture, this prepares an input without the
compiler or its fixture runner:

```python
from pathlib import Path
import gzip
import struct

fixture = Path("fixtures/ixby-stage2")
def nat(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    out.append(n)
    return bytes(out)
def scalar_bytes(data):
    return b"\x00\x06" + nat(len(data)) + data
claim = (fixture / "smoke-public.claim").read_bytes()
proof = gzip.decompress((fixture / "smoke-native-proof.bin.gz").read_bytes())
Path("/tmp/stage2.ixbi").write_bytes(
    b"IXFI" + struct.pack("<II", 1, 2) + nat(2)
    + scalar_bytes(claim) + scalar_bytes(proof))
```

A successful result is 49 bytes: the 12-byte `IXFO` header, scalar-value tag 0,
bytes-scalar tag 6, length 34, and the exact claim. Rejection is 13 bytes: the 12-byte
header followed by erased-value tag 3. The optional execution report records
actual reference transitions and output transport length.

## Loader bounds and evidence

`DecodeLimits` are caller-selected host loader bounds, independent of the
execution capacities stored in the file. Defaults are 64 MiB per file,
8,192 bytes per LEB128 natural, 1,048,576 value nodes, and value depth 1,024.
They can be adjusted through the Lean API. The command-line reader uses these
defaults. Maximum steps is a Nat; the test corpus includes a budget above 2⁷⁰.

An accepted Lean decode carries the kernel-checked equation that re-encoding
its value yields exactly the input bytes. This is an acceptance certificate;
a universal encoder/decoder completeness theorem is not claimed. The tests
execute every runtime scalar and instruction family after decoding, reject
malformed encodings and truncations, and compare fresh complete artifacts.
The independent Python reader checks the exported corpus and Stage2 manifest.

Source refinement of the experimental LCNF compiler remains a separate proof
obligation. The complete artifact and format can be handed directly to the
proving implementation for executor support and proving work.
