# IxBy canonical functional encoding

The current reference [codec](../Ix/Ixby/Codec/) and native
[reader](../flock-stage3/host/src/ixby/ixbf/) use **format 1, semantics 2**.
Old IXBY/IXBP/IXBI/IXBO artifacts and older functional revisions reject.
The [compiler handoff](CompilatrixRuntimeV2Handoff.md) describes migration.

## Conventions and envelopes

`Nat` is minimal unsigned LEB128. `u8`, `u32`, `u64`, `u128`, and `u256`
are fixed-width unsigned little-endian integers. `Vec(T)` is a `Nat` element
count followed by consecutive `T` encodings. There is no padding or terminator.
All files require complete consumption. Nonminimal integers, unknown tags,
wrong revisions, invalid UTF-8, noncanonical Booleans/field elements,
truncation, and trailing bytes reject.

| Artifact | Header | Body |
| --- | --- | --- |
| Program | `"IXBF" || u32(1) || u32(2)` | Limits, maximum fuel, program |
| Input | `"IXFI" || u32(1) || u32(2)` | `Vec(Value)` in entry-argument order |
| Output | `"IXFO" || u32(1) || u32(2)` | Exactly one `Value` |
| Profile | `"IXFP" || u32(0) || u32(1) || u32(2)` | Ten `u128` limits, then `u64` maximum fuel |

The profile is exactly 184 bytes. Limit order is functions, constructors,
blocks, locals, operands, continuations, inputNodes, natBits, stringBytes,
byteArrayBytes. Program bodies begin with these same ten limits as `Nat`, then
maximum fuel as `Nat`. The reference profile requires limits below `2^128`
and fuel below `2^64`; the native proof setup imposes further physical limits.

File-size, syntax-node, and depth budgets are local loader policy, independent
of these committed semantic limits. One value-node budget covers an entire
forest, including constructor fields, PAP captures, and array elements.

## Program layout

```text
Program  = entryFunction:Nat || Vec(CtorDecl) || Vec(Function)
CtorId   = block:u256 || member:Nat || tag:Nat
CtorDecl = CtorId || fieldCount:Nat
Function = arity:Nat || entryBlock:Nat || Vec(Block)
Block    = incomingLocals:Nat || Instr
```

Function and constructor references index their ordered program tables. Block
references index the current function; locals are absolute frame slots. The
whole image is admitted, including unreachable blocks and unused declarations.
The codec does not reorder or optimize the image. Constructor names retain
all 256 bits; their source meaning remains a compiler obligation.

| Operand tag | Variant | Payload |
| ---: | --- | --- |
| 0 | local | `slot:Nat` |
| 1 | literal | `Scalar` |
| 2 | erased | Empty |

| Operation tag | Variant | Payload |
| ---: | --- | --- |
| 0 | copy | `Operand` |
| 1 | primitive | `opcode:u8 || Vec(Operand)` |
| 2 | construct | `constructorIndex:Nat || Vec(Operand)` |
| 3 | project | `Operand || fieldIndex:Nat` |
| 4 | closure | `functionIndex:Nat || Vec(Operand)` |
| 5 | call | `functionIndex:Nat || Vec(Operand)` |
| 6 | callSelf | `Vec(Operand)` |
| 7 | apply | `Operand || Vec(Operand)` |

| Instruction tag | Variant | Payload |
| ---: | --- | --- |
| 0 | letOp | `Op || nextBlock:Nat` |
| 1 | ret | `Operand` |
| 2 | tailCall | `functionIndex:Nat || Vec(Operand)` |
| 3 | tailCallSelf | `Vec(Operand)` |
| 4 | tailApply | `Operand || Vec(Operand)` |
| 5 | caseCtor | `Operand || Vec(constructorIndex:Nat || targetBlock:Nat)` |
| 6 | caseNat | `Operand || ifZero:Nat || ifSucc:Nat` |
| 7 | branch | `Operand || ifTrue:Nat || ifFalse:Nat` |

## Values and scalars

| Value tag | Variant | Payload |
| ---: | --- | --- |
| 0 | scalar | `Scalar` |
| 1 | constructor | `CtorId || Vec(Value)` |
| 2 | PAP | `functionIndex:Nat || Vec(Value)` |
| 3 | erased | Empty |
| 4 | array | `Vec(Value)`; length below `2^32` |

Byte builders are internal values and cannot be encoded, even nested inside
another value. Tags `5..255` reject. Array lengths do not use the operand-vector
limit; elements still consume the shared value-node and depth budgets.

| Scalar tag | Variant | Payload |
| ---: | --- | --- |
| 0 | Nat | `Nat` |
| 1 | String | UTF-8 byte length as `Nat`, then those bytes |
| 2 | Bool | One byte, exactly 0 or 1 |
| 3 | Word32 | `u32` |
| 4 | Field | Canonical `u64` below `p = 2^64 - 2^32 + 1` |
| 5 | extension | Two canonical field coefficients, `c0 || c1` |
| 6 | Bytes | Byte length as `Nat`, then those bytes |

## Primitive opcodes

The explicit table below is shared by the reference codec and functional
reader. The Lean theorem `primitiveOpcode_decodes` checks every constructor.
An operation's vector length must equal its arity; unknown opcodes reject.

| Opcode | Primitive | Arity |
| ---: | --- | ---: |
| 0 | `natAdd` | 2 |
| 1 | `natSub` | 2 |
| 2 | `natMul` | 2 |
| 3 | `natDiv` | 2 |
| 4 | `natMod` | 2 |
| 5 | `natEq` | 2 |
| 6 | `natLt` | 2 |
| 7 | `strAppend` | 2 |
| 8 | `strLength` | 1 |
| 9 | `strEq` | 2 |
| 10 | `word32Add` | 2 |
| 11 | `word32Sub` | 2 |
| 12 | `word32Mul` | 2 |
| 13 | `word32And` | 2 |
| 14 | `word32Or` | 2 |
| 15 | `word32Xor` | 2 |
| 16 | `word32Shl` | 2 |
| 17 | `word32Shr` | 2 |
| 18 | `word32Rotr` | 2 |
| 19 | `word32Eq` | 2 |
| 20 | `word32Lt` | 2 |
| 21 | `word32ToBytes` | 1 |
| 22 | `bytesToWord32` | 1 |
| 23 | `word32ToField` | 1 |
| 24 | `fieldAdd` | 2 |
| 25 | `fieldSub` | 2 |
| 26 | `fieldMul` | 2 |
| 27 | `fieldInverse` | 1 |
| 28 | `fieldEq` | 2 |
| 29 | `fieldToBytes` | 1 |
| 30 | `bytesToField` | 1 |
| 31 | `extAdd` | 2 |
| 32 | `extSub` | 2 |
| 33 | `extMul` | 2 |
| 34 | `extInverse` | 1 |
| 35 | `extEq` | 2 |
| 36 | `extPack` | 2 |
| 37 | `extFst` | 1 |
| 38 | `extSnd` | 1 |
| 39 | `bytesLength` | 1 |
| 40 | `bytesGet` | 2 |
| 41 | `bytesAppend` | 2 |
| 42 | `bytesSlice` | 3 |
| 43 | `bytesEq` | 2 |
| 44 | `blake3` | 1 |
| 45 | `natToWord32` | 1 |
| 46 | `word32ToNat` | 1 |
| 47 | `fieldToNat` | 1 |
| 48 | `natToField` | 1 |
| 49 | `arrayEmpty` | 0 |
| 50 | `arrayLength` | 1 |
| 51 | `arrayGet` | 2 |
| 52 | `arraySet` | 3 |
| 53 | `arrayPush` | 2 |
| 54 | `byteBuilderEmpty` | 0 |
| 55 | `byteBuilderAppend` | 2 |
| 56 | `byteBuilderFreeze` | 1 |
| 57 | `byteBuilderLength` | 1 |

See [primitive semantics](../Ix/Ixby/Primitive.lean) and the
[revision-2 contracts](CompilatrixRuntimeV2Handoff.md) for argument types,
capacity checks, and failures. Wire support does not imply that every physical
proof setup implements every primitive.

## Commitments and claim transports

```text
H_d(x) = BLAKE3("IxBy/commit/v0" || 00 || u8(d) || x)
P = H_0(profile)       B = H_1(P || program)
I = H_2(B || input)    O = H_3(B || output)
S = H_4(P || B || I || O)
```

The current `IXBE` transport is `"IXBE" || u32(1) || u32(2) || P || B || I || O`
(140 bytes). `IXBR` is `"IXBR" || u32(1) || u32(2) || P || B || O` (108 bytes).
Each digest is 32 bytes. These are experimental statement envelopes, not a
new production Ixon `Claim` variant. Profile selection and approved program
identity are external policy inputs; decoding bytes does not authorize them.
