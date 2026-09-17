# Typed Lean to full-runtime Ixby

The typed frontend emits a complete format-1, semantics-2 [Ixby binary](ixby-binary.md).
The retained [Stage2 artifact](../fixtures/ixby-stage2/stage2.ixby) includes both
fixed keys and the verifier code: 991,082 bytes, 672 functions, 5,822 blocks,
140 constructor layouts, and entry function 671. A separate `ixby-exec`
process loads the binary without a compiler environment or Lean source.
Its chunked executor is kernel-proved equivalent to the pinned reference,
including errors and exact logical fuel.

`Compilatrix.Ixby.LeanFrontend.compile` lowers pure monomorphic LCNF after
Lean's proof erasure and specialization. Every emitted block passes reference
whole-program validation. Unknown runtime externs reject; packed-byte capacity
must be below `2^32`. [Runtime certificates](ixby-representation.md) bind all 97
scalar/collection/field helpers and ten optional wire helpers to their complete
bodies before Stage2 export.

Stage2 export additionally applies [certified ordinary leaf-call inlining](ixby-inline.md)
and checks the decoded binary against the original image. The pass preserves
successful executions at the same fuel and limits; reverse simulation allows
the explicitly bounded call overhead. `compile-baseline` disables this pass.

The frontend remains experimental. General LCNF source refinement, source
authentication, proof erasure, and specialization are outside these contracts.
This entry does not produce an `IxonCompilation`; constructor identities are
local layout identifiers.

## Runtime ABI

Nat and erased `Fin.val` use unboxed Nat scalars; UInt8/UInt32 use Word32;
USize uses Nat with 64-bit source semantics. Explicit Nat/Word32/Field
conversions check input and result capacities. Source field wrappers convert
Nat to Field for arithmetic and back afterward. No cached numeric wrapper or
implicit field reduction occurs in Nat equality. Extension values use native
extension scalars.

Ordinary arrays hold native persistent arrays in one-field dispatch wrappers.
Packed byte views retain scalar Bytes and length. Invalid `set!` keeps the
original array, checked access fails, and default access preserves its
fallback. Guards use full Nat indices. Packed updates can widen to generic
arrays while preserving earlier values.
[Array reads dispatch once](ixby-array-read.md), saving four transitions per
successful read while retaining the certified helper contracts and bounds.

Byte serialization accumulates immutable chunks and freezes once. Wire
encoding retains an internal writer buffer across writes, checks the source
byte limit, and freezes before returning. Direct writer calls retain their
ordinary source array representation. Subranges use checked `bytesSlice`;
field I/O preserves canonicality, source error, and read-offset behavior.
Calls, PAPs, oversaturation, joins, and tail calls use reference instructions.

The format supports seven scalars, 58 primitives, persistent array values,
and every operation/instruction. Serialization recursively rejects internal
builders. IXBF, IXFI, and IXFO share semantics 2; one 184-byte IXFP profile
replaces the retired semantic modes.

## Stage2 and CSLib evidence

The Stage2 adapter embeds 925,789 original key bytes, entrypoints 755/243,
and fixed source configuration. Inputs are public claim Bytes and private
native proof Bytes. Success returns the exact 34-byte claim; rejection returns
erased. Its valid execution takes **544,834,777 logical transitions** after
inlining and single-dispatch reads, versus 711,293,203 in the runtime revision 2 baseline.
All eight cases remain separate required Nix checks: valid, changed claim,
empty/truncated/malformed proof, trailing public/proof bytes, and wrong claim
kind. Step exhaustion fails the gate; the image permits 16 billion transitions.

The independently keyed CSLib image is recompiled and compared with its
retained expected output. It takes **276,667,563 logical transitions** after
inlining and single-dispatch reads, versus 360,337,913 in runtime revision 2
and 2,033,412,182 in revision 1. The [array-read record](ixby-array-read.md)
documents the latest contracts and measurements, following the
[inlining record](ixby-inline.md).
The earlier [integration record](ixby-runtime-v2.md)
contains artifacts, commitments, the helper census, measurement conditions,
and native fixture verification. A complete CSLib native proof has not been
generated.

## Reproduction and required checks

```sh
lake build stage2-ixby ixby-exec check-ixby-lean check-ixby-binary CompilatrixTests.Proofs
lake exe check-ixby-lean
lake exe check-ixby-binary
lake exe stage2-ixby fixtures/ixby-stage2 compile /tmp/stage2.ixby
python3 scripts/inspect_ixby.py /tmp/stage2.ixby --expected /tmp/stage2.ixby.json
lake exe stage2-ixby fixtures/ixby-stage2 valid /tmp/stage2.ixby
nix build .#checks.x86_64-linux.ixby-lean
```

Compilation and source comparisons use Lake's environment to load LCNF.
Case mode loads the supplied binary and never recompiles. Standalone execution:

```sh
.lake/build/bin/ixby-exec program.ixby input.ixbi output.ixbo execution.json
```

The helper suite includes 40,839 independent result cases, complete body
mutations, caller/resource checks, and exact fuel formulas. The retained 4,585
source comparisons cover large Nat, fields/extensions, closures, persistent
arrays, byte aliases, wire outputs/errors, and 10,000 tail-call iterations
under eight continuations. Two compiler rejections retain unsupported Float
extern and byte-index capacity checks. See the [proof/coverage mapping](ixby-representation.md).

The binary gate executes 94 decoded images, all 58 opcodes, all five wire value
kinds, malformed encodings, recursive builder rejection, and independent
conversion and eleven-opcode fixtures. It also runs 22,794 chunked/reference
comparisons. Required Nix checks compare fresh repeated Stage2 compilation
with the retained binary/inventory, run an independent Python reader, and
execute standalone with `LEAN_PATH` unset.
