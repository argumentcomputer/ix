# Typed Ixby runtime representation proofs

The revision 2 runtime uses unboxed scalars, persistent arrays, packed byte
views, and immutable byte builders. The [current proof aggregate](../Compilatrix/Ixby/Runtime/Native.lean)
connects exact generated helper bodies to the pinned reference evaluator.
The [chunked executor proof](../Compilatrix/Ixby/Runtime/Chunked/Simulation.lean)
establishes equality for every program, input, semantic limit, fuel budget,
successful result, and error.

General LCNF compilation, proof erasure, specialization, and complete Stage2
source refinement remain outside these contracts. Native proof-circuit
refinement is a separate upstream obligation. See the [integration record](ixby-runtime-v2.md)
for execution and artifact evidence.

## Scalar representation

| Boundary | Value |
| --- | --- |
| Nat and erased `Fin.val` | `.scalar (.nat n)` |
| UInt8 / UInt32 | `.scalar (.word32 w)`; UInt8 values are below 256 |
| USize | Nat scalar, with explicit 64-bit source semantics |
| Runtime Goldilocks | `.scalar (.field f)` |
| Extension field | `.scalar (.ext f)` |

The typed image contains no `Number`, `RawNumber`, or `FieldNumber` wrapper.
LCNF erases source Goldilocks to its Nat representation. Field wrappers
convert Nat to Field before arithmetic and Field to Nat afterward. Ordinary
Nat comparison retains the exact input without implicit modular reduction.
[Native/Image](../Compilatrix/Ixby/Runtime/Native/Image.lean) proves strict
image encoding/decoding laws.

The nine conversion helpers retain their interfaces. `toWord n weight acc`
returns the Word32 result `acc + n.toUInt32 * weight`; `fromWordLoop w weight acc`
returns the exact Nat `acc + w.toNat * weight`. Both execute four instructions,
require six locals, and preserve arbitrary continuations. Input validation
occurs even at zero weight. The maximum-word conversion succeeds with 32 Nat
bits and rejects at 31; results and intermediates must fit the declared limit.

[Scalars](../Compilatrix/Ixby/Runtime/Native/Scalars.lean),
[Fields](../Compilatrix/Ixby/Runtime/Native/Fields.lean),
[Words](../Compilatrix/Ixby/Runtime/Native/Words.lean), and
[USize](../Compilatrix/Ixby/Runtime/Native/USize.lean) prove conversion,
arithmetic, equality, order, masking, modular word arithmetic, and field
packing/projection contracts for the emitted bodies. Nat division by zero
returns zero; remainder by zero returns the dividend. UInt8/UInt32 shifts
reduce source counts modulo 8/32. USize retains the platform premise and
65-bit intermediates before reduction.

[NatLoops](../Compilatrix/Ixby/Runtime/Native/NatLoops.lean) proves complete
shift, logarithm, and repeated-squaring paths returning `n >>> shift`,
`acc + n.log2`, and `acc * base^exponent`. The power premise bounds both the
unscaled power and accumulated result: a zero accumulator does not excuse an
overflowing square. The final unused square is skipped. These loops need no
extra continuation.

Semantic Nat capacity and physical Nat128 admission are distinct.
[Values](../Compilatrix/Ixby/Runtime/Native/Values.lean) states the physical
bound and proves that a semantically valid 129-bit Nat lies outside it.
A 4,096-bit reference execution does not establish arbitrary-precision native
proof support.

## Native arrays and bytes

`ArrayRep encode source value` relates a source sequence to a native
`.array (source.map encode)` in a one-field dispatch constructor. The wrapper
distinguishes generic arrays from packed byte views after type erasure; it
contains no interpreted tree, height, or capacity. Representation laws prove
length, indexing, update, push, append, and preservation of original aliases
for arbitrary element encodings.

[ArrayBasic](../Compilatrix/Ixby/Runtime/Native/ArrayBasic.lean) and
[ArrayAccess](../Compilatrix/Ixby/Runtime/Native/ArrayAccess.lean) execute native
size, empty, lookup, default lookup, push, `set!`, and `uset` paths. Guards use
full-width Nat indices. Invalid `set!` returns the original array without
inspecting its replacement; checked lookup and `uset` fail; default lookup
returns its fallback. Length stays below `2^32`, independently of operand limits.
The [single-dispatch read](ixby-array-read.md) retains these contracts, uses
no spare continuation slot, and lowers packed reads to nine locals.
[ArrayRead](../Compilatrix/Ixby/Runtime/Native/ArrayRead.lean) adds writer reads,
full-Nat rejection paths, and length-before-index validation contracts.

[ArrayLoops](../Compilatrix/Ixby/Runtime/Native/ArrayLoops.lean),
[ArrayAppend](../Compilatrix/Ixby/Runtime/Native/ArrayAppend.lean), and
[ArrayExtract](../Compilatrix/Ixby/Runtime/Native/ArrayExtract.lean) prove native
copy/append/extract sequence preservation, arbitrary accumulators, clamped
upper bounds, reversed ranges, empty inputs, and caller restoration. Native
extract requires two spare continuation slots.

`BytesRep` permits packed scalar bytes or an array of UInt8 Word32 values.
[ByteLoops](../Compilatrix/Ixby/Runtime/Native/ByteLoops.lean) proves serialization
through one immutable builder and final freeze, preserving an existing prefix.
[PackedArray](../Compilatrix/Ixby/Runtime/Native/PackedArray.lean) proves packed
indexing, append, and half-open slices. Bounds precede Word32 address conversion;
empty/reversed extracts use the empty native array representation.

[CollectionLaws](../Compilatrix/Ixby/Runtime/Native/CollectionLaws.lean) proves
primitive array/builder laws and independent freezes of old/new aliases.
[WireWrite](../Compilatrix/Ixby/Runtime/Native/WireWrite.lean) proves writer-buffer
append and source byte-limit rejection while preserving other state fields.
[WireEncode](../Compilatrix/Ixby/Runtime/Native/WireEncode.lean) composes a writer's
specified result with initialization and final freezing. Internal builders
never cross a serialized boundary.

The checker also binds list/replicate/pop, representation widening,
little-endian, field-reader/writer, hash, and byte-equality bodies. These have
independent execution oracles; a source-operation theorem for every branch of
every helper is not claimed. The source `readBytes` LCNF body remains outside
the native-body certificate, while its call target is bound.

## Body certificates and machine composition

[Certificate](../Compilatrix/Ixby/Runtime/Native/Certificate.lean) checks all 97
scalar, collection, and field helpers against complete templates.
[WireCertificate](../Compilatrix/Ixby/Runtime/Native/WireCertificate.lean) adds ten
wire helpers and constructor declarations. Image checking binds names and
function slots. Equality covers arity, entry, every block/local/instruction/
operand, and unreachable blocks. Acceptance retains propositional equality
to the actual program; structural admission alone does not establish this.

The [execution relation](../Compilatrix/Ixby/Runtime/Execution.lean) stops at
return control with the existing continuation intact. [Call interfaces](../Compilatrix/Ixby/Runtime/Native/Machine.lean)
restore the saved frame and append the exact result. Local contracts state
scalar, local-slot, and continuation bounds. Whole-program execution also
requires ordinary program/input admission; local bounds need not admit
unrelated functions or literals in the complete image.

The chunked executor stores immutable byte chunks with a proved cached
length. Append preserves previous chunks; freeze traverses them once and
copies bytes into one accumulator. Its recursive value relation covers
arrays, constructors, PAPs, frames, and continuations. Primitive, operation,
Eval, Apply, step, and run simulations preserve validation precedence and
exact logical counters. This introduces no axiom, unsafe implementation,
FFI, or compiler rewrite rule.

## Logical fuel

Counts start at helper entry and include final halt. Caller resumption
replaces that last transition when composing calls. Here `n` is the number of
byte/element iterations; the append formulas use nonempty `a` and `b`.

| Path | Exact transitions |
| --- | ---: |
| Weighted `toWord` / `fromWordLoop` | 5 |
| Direct unary/binary scalar helper | 3 |
| Native / packed array size | 4 / 3 |
| Native push / valid get / valid set | 5 / 7 / 12 |
| Packed / writer valid get | 7 / 9 |
| Invalid native `set!` | 9 |
| Native `toBytes` / internal byte loop | `8*n + 9` / `8*n + 5` |
| Native nonempty extract | `18*n + 20` |
| Native empty/reversed extract | 13 |
| Packed nonempty / empty extract | 16 / 12 |
| Native append, both nonempty | `18*b.size + 24` |
| Native append, empty left / empty right | 14 / 16 |
| Packed append, both nonempty | 25 |
| Packed append, empty left / empty right | 12 / 14 |
| Little-endian builder loop of width `w` | `8*((w-1)/4) + 10` |
| Little-endian decoding loop | `8*n + 4` |
| Public Nat log2 | `5*n.log2 + 5` |

Shift-loop cost is 3 at zero count, 5 for zero input and positive count, and
otherwise 7 plus the recursive cost at `(n/2, count-1)`. Power-loop cost is 3
at exponent zero, 10 at one, and otherwise 10 for an even exponent or 11 for
an odd exponent, plus the cost at half the exponent. Public wrappers add two.
The [fuel suite](../CompilatrixTests/Ixby/Native/Fuel.lean) checks 501 instances
against both executors and exhaustion with one less step. Correctness theorems
establish finite paths; this table is not a universal closed-form cost theorem
for every helper. Native array/copy microsteps consume no guest fuel.

## Required validation and retained coverage

`lake exe check-ixby-lean` runs 40,839 independent helper-oracle cases, 900
bounds rejections, 107 caller cases, 90 resource cases, 501 fuel cases, and the
retained 4,585 source comparisons. It rejects 2,258 body/layout/binding
mutations, including 1,416 structurally admitted programs. Another 22,680
array-read cases compare the previous complete helper body and both evaluators.
The inlined source suite repeats all 4,585 source comparisons. Every current
image and Stage2 export obtains the current certificates.

All 2,414 previous exact axiom assertions remain unchanged. Former boxed
number and interpreted-tree proofs remain checked mathematical models through
[NumberImageModel](../Compilatrix/Ixby/Runtime/NumberImageModel.lean); they no longer
certify emitted revision 2 bodies. Old gate categories map to the focused
[Native test modules](../CompilatrixTests/Ixby/Native/Main.lean): conversions,
Nat, fields, words, collections, callers, mutations, and resources. Obsolete
three-layout/cache and tree-capacity executions are replaced by typed scalar,
full-Nat index, persistent-array, packed-byte, and builder cases. The source
corpus remains intact in [SourceRuntime](../CompilatrixTests/Ixby/SourceRuntime.lean).

[IxbyNative](../CompilatrixTests/Fences/IxbyNative.lean) adds 235 exact theorem
roots using subsets of `propext`, `Classical.choice`, and `Quot.sound`.
[IxbyArrayRead](../CompilatrixTests/Fences/IxbyArrayRead.lean) adds seven roots
on the same basis, preserving the prior helper and inliner assertions.
The required proof aggregate, trust audit, binary gate, fresh artifact checks,
and all eight serialized Stage2 executions include the new modules.
