# Captured scalar exports

[`Captured.compileSource`](../Compilatrix/X86/PhysicalScalarCapturedExport.lean)
compiles a closed source module exporting a function with one static Word
capture and one runtime Word argument. It consumes the ordinary validated
source-to-physical-IxIR₂ attachment, checks module initialization, selects the
actual binary physical function, and emits a certified unary ELF entry.

[`Captured.Compiled.sourceNatReturns`](../Compilatrix/X86/PhysicalScalarCapturedSourceObject.lean)
proves that successful runtime Ixon application returns the exact Nat observed
in RAX. It derives the actual IxIR₁ PAP application, capture-first invocation,
complete closure reclamation, physical execution, and ELF execution. Its
premises are source evaluation/application, the existing sharing and oracle
relations, and the stated finite-stack ABI conditions. Runtime inputs are
universally quantified; no per-input native execution certificate is required.

## Admitted initialization and body

The closed initializer runs once during compilation, with default limits of
4,096 control steps, 16,384 heap-work units, and 256 allocated slots. The
dependent checker retains the successful physical evaluator equation as a
kernel proof. Initialization must return its sole live heap value: a shared
PAP with reference count one, arity two, and exactly one literal Nat capture
strictly below `2^64`. Its declared target must be binary and PAP-safe.

Dead slots are allowed at arbitrary positions. The check requires allocation
count equal to slot count, no reuse, and `frees + 1 = allocs`. Saturated
application supplies `[capture, argument]`, performs one additional RC
operation and free, and leaves every slot dead with `frees = allocs`.
`Initialized.reclaimed` records these exact facts. The scalar physical body
preserves the resulting heap and all its counters.

The body uses the existing [physical scalar CFG fragment](source-native-physical-scalar.md):
literal Words, scalar ownership operations, moves, Nat peeling, jumps/joins,
and nonrecursive direct calls. It supports the same block, instruction,
local-slot, and expansion limits. An appended checked scalar function binds
the capture and calls the selected entry; the complete table has at most 32
functions, leaving at most 31 selected physical functions. Existing call
indices remain valid, and the wrapper is checked against the full extended
table. This extension adds no allocating native instructions.

Initializer failure, excessive limits, non-Word or multiple captures,
additional live values, incorrect RC/arity, missing or unsafe targets, and
unsupported bodies return an error. The ordinary checked physical attachment
remains available for fallback. Runtime Nat conversion uses
`Scalar.encodeArguments` and rejects inputs at or above `2^64` without
wrapping.

These initializer bounds constrain the compiler's closed evaluation. They
are not a general occupied-heap capacity theorem or a native heap allocator.
Runtime captures, captured heap objects, allocating native bodies, general
recursion, and the unchanged upstream C3 captured-closure fixture retain
their existing boundaries.

## ABI and proof chain

The regression gate exports:

```c
struct scalar_result { uint64_t value, status; };
struct scalar_result compilatrix_scalar(uint64_t argument);
```

RDI carries the argument; RSI is unrestricted. RAX contains the exact Nat and
RDX is zero. The capture is embedded in the emitted wrapper. No native
initialization or heap argument is needed. `Scalar.Stack` requires an aligned,
nonwrapping, readable/writable reservation of `272 * D` bytes, including the
eight-byte return slot, where `D` exceeds the wrapper's entry index.
The object theorem proves return to that slot's original address, RSP advanced
by eight after RET, preserved System V saved registers, and unchanged memory
outside the reservation.

`checkInitializer` supplies the actual initial heap and value. The ordinary
source-to-physical theorem identifies their source value graph across both
compiler address passes. `Heap.owned` supplies ownership to the generic source
application theorem; `Heap.applied` exposes capture-first dispatch and complete
reclamation. The existing structured lowering simulation derives physical
function execution. `Scalar.Bound.evaluates` embeds its result into the checked
unary wrapper. `Compiled.nativeReturns` and `Compiled.physicalReturns` then
compose physical selection with the scalar, stream, and complete-object proofs.

Twelve new axiom fences cover these contracts. Initialization, ownership,
binding, and physical-to-object results use the ordinary logical basis.
The source endpoints retain the existing Blake3 compiler hash boundary.
There is no new axiom or native interface. Reference ISA agreement, immutable
executable text, system linking/loading, and the compiler/runtime seed retain
their existing trust assumptions.

Objects bind the actual IxIR₁ graph root with lowering version **7**, policy
version **1**, and policy name `physical-scalar-capture/1`. Diagnostic physical
JSON remains separate from canonical IxIR₂ persistence. The uncaptured
version-6 gate and its seven objects retain their existing contracts.

## Evidence and reproduction

Each family is compiled separately with captures `0`, `7`, and `2^64 - 1`:

| Family | Result for runtime argument `a` | Selected / emitted functions | Text / object bytes | Stack bytes |
| --- | --- | --- | --- | --- |
| `capture-project` | capture | 1 / 2 | 201 / 1,064 | 544 |
| `capture-choice` | capture if `a = 0`, otherwise `a - 1` | 2 / 3 | 419 / 1,280 | 816 |
| `capture-nested` | capture if `a ≤ 2`, otherwise `a - 3` | 3 / 4 | 712 / 1,568 | 1,088 |

The synthetic sources use an ordinary closed `let` around a lambda and
nonrecursive Nat recursors. Their checked compilation creates a temporary
literal-helper PAP followed by the captured export. Initialization takes
eight physical control steps and two heap-work units: two allocated slots,
one free, one RC operation, no reuse, and one live node at peak. Application
leaves two frees, two RC operations, and zero live nodes.

All 171 boundary cases run through Ixon application, raw IxIR₀, addressed
IxIR₁ initialization/application/invocation, logical and physical IxIR₂,
typed x86, and the complete ELF evaluator. Rejections cover 15 initializer
variants per object (135 runs), two wrapper limits, three oversized source or
runtime conversions, 36 application/arity boundaries, and 18 inadequate stack
mappings.

The independent checker imports no compiler or evaluator. It checks the
initializer's literal/helper/capture structure, source/IR/export bindings,
selection maps, stack bounds, ELF interpretation, hashes, provenance,
argument order, and exact heap observations. All 135 deliberate corruptions
must reject. Two fresh generations of all 19 files must be byte-identical.
On x86-64 Linux, independent C arithmetic checks 19 boundary and 64
deterministic random inputs on ordinary and guarded finite stacks for each
object: **1,494 linked calls**, including varied unused RSI values. Other
configured platforms run artifact checks without claiming x86 execution.

```sh
lake build source-native-captured-scalar check-source-native-captured-scalar
.lake/build/bin/check-source-native-captured-scalar \
  --fixture .lake/build/bin/source-native-captured-scalar \
  --cc cc --harness fixtures/source-native-captured-scalar/native_harness.c
```

The Nix check is `source-native-captured-scalar`. These are correctness
observations, with no performance claim.
