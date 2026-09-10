# IxBy experimental crypto encoding

This documents the reference codec in `Ix/Ixby/Codec/` and commitments in
`Ix/Ixby/Commitment.lean`. The wire revision and crypto semantic revision are
both **0**. This is an experimental target artifact format, not a new
production `Claim` variant, a frozen source ABI, or a circuit-soundness proof.
See [IxBy semantics and implementation status](Ixby.md).

## Integer and collection conventions

`u8`, `u32`, `u64`, and `u256` are unsigned, fixed-width little-endian integers
of 1, 4, 8, and 32 bytes. `||` means concatenation. `Vec(T)` is a `u32` element
count followed by that many consecutive `T` encodings. There is no padding,
alignment, varint, optional terminator, or native machine-size field.

Every logical integer must fit its stated width before encoding. In particular,
constructor members/tags and projection indices cannot silently truncate even
if execution would never inspect them. Byte-array lengths count raw bytes,
not characters. Unknown tags, wrong revisions, truncation, and trailing bytes
are rejected; there is no permissive fallback decoder.

All top-level artifacts start with four literal ASCII bytes and `u32(0)`:

| Artifact | Magic | Body after the eight-byte header |
| --- | --- | --- |
| Profile | `IXBP` | `u32(semanticRevision)` followed by the fourteen parameters below |
| Program | `IXBY` | The program image below |
| Input | `IXBI` | `Vec(Value)` in entry-argument order |
| Output | `IXBO` | One `Value` |

Input and output envelopes cannot be interchanged. The profile is separate
from the program bytes; the program commitment binds it explicitly.

## Profile envelope

The complete envelope is exactly 68 bytes. Offset 8 holds semantic revision
0. The remaining fields, in order, are all `u32`:

| Byte offset | Parameter | Bound or meaning |
| --- | --- | --- |
| 12 | `limits.functions` | Function table size |
| 16 | `limits.constructors` | Constructor table size and case-alternative count |
| 20 | `limits.blocks` | Blocks per function, not total blocks in the image |
| 24 | `limits.locals` | Local frame size |
| 28 | `limits.operands` | Operand vectors, function arity, fields, and captures |
| 32 | `limits.continuations` | Continuation stack depth |
| 36 | `limits.inputNodes` | Total nodes across the input forest; separately, output nodes |
| 40 | `limits.natBits` | Must be zero; does not enable Nat scalars |
| 44 | `limits.stringBytes` | Must be zero; does not enable String scalars |
| 48 | `limits.byteArrayBytes` | Individual byte scalars, including literals and primitive results |
| 52 | `programBytes` | Complete encoded program size, including header |
| 56 | `valueBytes` | Complete input size and, separately, complete output size, including headers |
| 60 | `valueDepth` | Maximum value-tree depth; each root consumes one level |
| 64 | `maxSteps` | Maximum supplied execution fuel |

All parameters must be less than `2^32`. Zero capacities are representable but
can prevent admission or successful execution. `Profile.execute` enforces
logical admission and value/step limits; program/value byte caps additionally
apply at the codec boundary. The profile envelope has its own fixed 68-byte cap.

Decoding a profile does not authorize it. A caller must select an approved
profile/resource policy before using it to decode or execute large artifacts.
Neither the defaults nor the largest representable capacities are security
recommendations. These limits do not yet bound all intermediate tree expansion,
host allocation, or eventual prover memory costs.

## Program image

The body is encoded as follows, preserving each array/list's declared order:

```text
Program  = entryFunction:u32 || Vec(CtorDecl) || Vec(Function)
CtorId   = block:u256 || member:u32 || tag:u32
CtorDecl = CtorId || fieldCount:u32
Function = arity:u32 || entryBlock:u32 || Vec(Block)
Block    = incomingLocals:u32 || Instr
```

The constructor block is the full numeric 256-bit logical name, encoded
little-endian. Encoding it does not authenticate its source declaration;
source identity transport remains a compiler obligation. Function and
constructor references index their program tables; block references index
the current function. Locals are absolute slots in its immutable local frame.

The whole image is encoded and admitted, including unused functions,
unreachable blocks, and unused constructor declarations. There is no reordering,
dead-code elimination, external import resolution, or semantic normalization
in the codec. Two behaviorally equivalent but differently arranged images may
have different bytes and commitments. Canonicality concerns representation of
the structured image, not equivalence of programs.

### Operands and operations

Each variant begins with the indicated `u8` tag. Payload order is exact.

| Operand tag | Variant | Payload |
| --- | --- | --- |
| 0 | `local` | `slot:u32` |
| 1 | `literal` | `Scalar` |
| 2 | `erased` | Empty |

| Operation tag | Variant | Payload |
| --- | --- | --- |
| 0 | `copy` | `Operand` |
| 1 | `primitive` | `opcode:u8 || Vec(Operand)` |
| 2 | `construct` | `constructorIndex:u32 || Vec(Operand)` |
| 3 | `project` | `Operand || fieldIndex:u32` |
| 4 | `closure` | `functionIndex:u32 || Vec(Operand)` |
| 5 | `call` | `functionIndex:u32 || Vec(Operand)` |
| 6 | `callSelf` | `Vec(Operand)` |
| 7 | `apply` | `Operand || Vec(Operand)` |

| Instruction tag | Variant | Payload |
| --- | --- | --- |
| 0 | `letOp` | `Op || nextBlock:u32` |
| 1 | `ret` | `Operand` |
| 2 | `tailCall` | `functionIndex:u32 || Vec(Operand)` |
| 3 | `tailCallSelf` | `Vec(Operand)` |
| 4 | `tailApply` | `Operand || Vec(Operand)` |
| 5 | `caseCtor` | `Operand || Vec(constructorIndex:u32 || targetBlock:u32)` |
| 6 | `branch` | `Operand || ifTrueBlock:u32 || ifFalseBlock:u32` |

`caseNat` has no tag in this profile. Whole-image admission enforces local and
successor-frame bounds, call/capture/constructor arities, valid references,
unique constructor identities, and unique case alternatives. It does not
statically prove operand types or that every execution succeeds.

### Primitive opcodes

These are the explicit `cryptoPrimitives` order in `Profile.lean`, not Lean's
internal constructor tags. Each table row assigns one opcode. Argument order,
result types, and failures are defined by `Primitive.eval` and the
[scalar and cryptographic semantics](Ixby.md#current-scalar-primitives).

| Opcode | Primitive | Arity |
| --- | --- | --- |
| 0 | `word32Add` | 2 |
| 1 | `word32Sub` | 2 |
| 2 | `word32Mul` | 2 |
| 3 | `word32And` | 2 |
| 4 | `word32Or` | 2 |
| 5 | `word32Xor` | 2 |
| 6 | `word32Shl` | 2 |
| 7 | `word32Shr` | 2 |
| 8 | `word32Rotr` | 2 |
| 9 | `word32Eq` | 2 |
| 10 | `word32Lt` | 2 |
| 11 | `word32ToBytes` | 1 |
| 12 | `bytesToWord32` | 1 |
| 13 | `word32ToField` | 1 |
| 14 | `fieldAdd` | 2 |
| 15 | `fieldSub` | 2 |
| 16 | `fieldMul` | 2 |
| 17 | `fieldInverse` | 1 |
| 18 | `fieldEq` | 2 |
| 19 | `fieldToBytes` | 1 |
| 20 | `bytesToField` | 1 |
| 21 | `extAdd` | 2 |
| 22 | `extSub` | 2 |
| 23 | `extMul` | 2 |
| 24 | `extInverse` | 1 |
| 25 | `extEq` | 2 |
| 26 | `extPack` | 2 |
| 27 | `extFst` | 1 |
| 28 | `extSnd` | 1 |
| 29 | `bytesLength` | 1 |
| 30 | `bytesGet` | 2 |
| 31 | `bytesAppend` | 2 |
| 32 | `bytesSlice` | 3 |
| 33 | `bytesEq` | 2 |
| 34 | `blake3` | 1 |

Nat and String primitives have no opcodes. Word32 remains a scalar value;
fixed-width bytecode indices do not turn CEK-family control into mutable
register-machine execution.

## Scalars and external values

Scalars start with a `u8` tag:

| Tag | Scalar | Payload |
| --- | --- | --- |
| 0 | Bool | One byte, exactly 0 or 1 |
| 1 | Word32 | `u32` |
| 2 | Goldilocks | `u64`, strictly less than `18446744069414584321` |
| 3 | Extension field | Two canonical Goldilocks `u64`s, `c0` then `c1`, for `c0 + c1*X`, `X² = 7` |
| 4 | Bytes | `u32` byte count followed by the raw bytes |

Field decoding rejects noncanonical integers instead of reducing them modulo
the field. Bytes need not be UTF-8. Nat and String scalars, including zero and
the empty string, are excluded rather than coerced to Word32 or Bytes.

Values start with a separate `u8` tag:

| Tag | Value | Payload |
| --- | --- | --- |
| 0 | Scalar | `Scalar`, including its scalar tag |
| 1 | Constructor | `CtorId || Vec(Value)` |
| 2 | PAP | `functionIndex:u32 || Vec(Value)` |
| 3 | Erased | Empty |

External values are inline finite trees. There are no object-pointer tags,
cycles, observable physical sharing, or backend object-table identifiers.
Constructors must name a declaration in the admitted program and have exactly
its field count. PAPs must name a function and capture strictly fewer values
than its arity. Inputs must have exactly the entry function's arity.

One node budget is shared across the entire input forest, including nested
fields and captures; a separate budget applies to the single output. Every
value, including a scalar or erased value, consumes one node and one depth
level. Collection counts are bounded before iteration and do not trigger
count-sized preallocation. Parsing stops on the first missing required byte.
Byte caps are checked before parsing, and the encoder checks its cap before
appending bytes. A future interned backend representation needs a refinement
to these values; it is not automatically the external ABI.

## Commitments

Let `H_d(x)` be the unkeyed 32-byte BLAKE3 hash of
`ASCII("IxBy/commit/v0") || 0x00 || u8(d) || x`. Domain tags are profile = 0,
program = 1, input = 2, output = 3, statement = 4. For admitted canonical
artifacts:

```text
P = H_0(encodedProfile)
B = H_1(P || encodedProgram)
I = H_2(B || encodedInput)
O = H_3(B || encodedOutput)
statementDigest = H_4(P || B || I || O)
```

Every digest is exactly 32 bytes. Each variable-length artifact is the final,
complete payload after any fixed-width digest prefixes; concatenation is
unambiguous. All profile parameters and every encoded program record are
bound. The statement is the four digests `(P, B, I, O)`; its compact digest is
available separately. There is no production statement/claim envelope yet.

`Commitment.ofArtifacts` admits the program, inputs, and output before computing
this statement. **It does not check that execution produces that output.**
`Commitment.ofExecution` derives the statement from a successful reference run.
`Commitment.executeAndCheck` runs the byte evaluator and compares all four
expected digests. It is host/reference execution, not succinct verification,
program authorization, or a source correctness certificate. The low-level
`hash` and `Internal.bind` helpers do not perform admission at all.

Binding relies on BLAKE3's cryptographic assumptions; no finite-hash
injectivity axiom or collision-resistance proof is introduced.

## Checked execution contract and remaining work

Each successful public decoder returns `Decoded`, containing the decoded
value and an equation that its encoder returns exactly the supplied bytes.
The implementation re-encodes and checks equality at acceptance. This is a
checked acceptance condition, not yet a general encoder/decoder inverse or
injectivity theorem.

`Codec.execute` decodes the exact program and inputs, runs `Profile.execute`,
and encodes the admitted output. Its `Execution` result retains the encoding
and evaluation equations. `Execution.reference_evaluates` connects that result
to the original functional `Ix.Ixby.Evaluates` relation through
`Profile.execute_refines`.

`Codec.Evaluates(profile, programBytes, inputBytes, outputBytes)` states that
some finite fuel witness makes this exact byte execution succeed. Fuel is not
a separate committed field: the profile's `maxSteps` is bound, and the witness
must respect it. Nonterminal runs, failed admission, primitive errors, or output
encoding failures do not establish successful execution.

`Tests/IxbyCodec.lean` covers independent golden bytes, every primitive and
operation, structured values, strict-prefix truncation, malformed tags/ranges,
resource boundaries, execution, and altered commitments. These tests and Lean
equations do not implement constrained decoding, authenticated program fetch,
object consistency, primitive gadgets, or STARK soundness. The separate
[scalar Aiur backend](IxbyAiur.md) authenticates and executes a restricted
straight-line subset with real proofs. The [control backend](IxbyControl.md)
adds whole-image tables, scalar branches, direct/tail calls, and explicit
continuations. The [object backend](IxbyObjects.md) adds immutable constructors,
projections, and constructor cases, with shared I/O budgets and a ranked-heap
contract. All use the same wire/semantic revision. General application, byte
scalars, the remaining primitives, and a formal circuit-to-reference
refinement remain backend obligations; source lowering and the source-value
ABI proof remain the later Compilatrix companion work.

Any encoding or opcode-assignment change requires an explicit wire revision;
any change of meaning requires a semantic revision. Commitment framing changes
require a new domain prefix. Preserve or explicitly reject old revisions;
do not silently reinterpret their artifacts. This experimental specification
must still be validated at the compiler and proving boundaries before a
permanent protocol or interpreter key is frozen.
