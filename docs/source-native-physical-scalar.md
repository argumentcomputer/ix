# Physical scalar CFG selection

The second N3 slice selects a bounded fragment of **actual physical IxIR₂**.
[`compileSourceExport`](../Compilatrix/X86/PhysicalScalarExport.lean) consumes
the existing validated source-to-IxIR₂ attachment, follows its exported
uncaptured closure, and emits one certified scalar ELF object. Selection
uses instruction, edge, and function contracts for every accepted CFG.

The universal endpoint is
[`Compiled.physicalReturns`](../Compilatrix/X86/PhysicalScalarObject.lean):
every successful execution of the selected physical function on exact Word
Nats agrees with execution of the emitted ELF on a sufficient finite stack.
`Compiled.nativeReturns` also proves that every admitted Word input returns;
it needs no physical or native execution certificate from the caller.

## Fragment and representation

| Boundary | Contract |
| --- | --- |
| Runtime values | Unsigned 64-bit Words representing exactly `IxIR₂.RVal.lit (.nat n)`, with `0 ≤ n < 2^64` |
| Signatures | Zero, one, or two scalar parameters and a scalar Nat result; source exports in the gate have two parameters |
| Instructions | `move`, `retainShared`, `releaseShared`, `dropUnique`, and direct `call` |
| Terminators | `ret`, `jump`, direct `tailCall`, and `switchValue` with Nat peeling and no constructor alternatives |
| Edges | Arbitrary simultaneous value-argument substitutions, including joins and permutations; successor edges prepend the predecessor Nat |
| Control | Acyclic CFG expansion and nonrecursive calls to earlier selected functions |
| Credits and heap | No transferred reuse credits or allocating instructions; all runtime registers contain literal Nats |

Scalar ownership operations preserve the whole physical store. Release/drop
consume traversal fuel in the reference evaluator, even for scalar leaves;
the proof constructs that fuel and preserves its unused suffix. The native
invocation needs no heap capacity. The module's separate initialization
returns one ordinary shared PAP identifying the uncaptured entry function.

The low-level selector proves runtime simulation. The source attachment also
supplies the existing IxIR₂ capability validation. Other declarations may be
outside the selected fragment; only the selected functions are emitted.
Dependency discovery conservatively includes direct calls in every block of
a selected function, including blocks unreachable from its entry.

Limits are 32 selected functions, 32 native local slots including parameters,
128 blocks and 128 instructions per block, expansion depth 128, and 4,096
expansion work units per function. Expansion spends a shared work budget
across both branch arms **before** building further output. The existing
scalar checker additionally bounds each resulting expression to 4,096 nodes.
Block IDs need not be in topological order. Joins are expanded with their
argument substitutions; this pass does not optimize duplicated continuations.

IxIR₂ has no primitive add/subtract instruction. This fragment lowers Nat
peeling to an exact zero test and predecessor calculation. For a positive
Word `w`, the emitted subtraction computes `w.toNat - 1`; zero takes its own
edge. Inputs, intermediates, and results therefore remain representable, and
the native status is always zero. The shared scalar backend's overflow exit
is unreachable for this fragment. The earlier
[erased-source arithmetic attachment](source-native-scalar.md) separately
proves runtime addition, truncated subtraction, and explicit overflow fallback.

Callers converting arbitrary Nats use `Scalar.encodeArguments` from
`ScalarNat.lean`; it rejects values at or above `2^64` without wrapping.
Unsupported graphs, captured exports, cyclic aliases/CFGs, recursion, missing
targets, incorrect arities, credits, and exceeded limits return an error.
The existing checked physical artifact remains available for fallback.

## ABI and finite resources

The gate exports the same scalar ABI as the first slice:

```c
struct scalar_result { uint64_t value, status; };
struct scalar_result compilatrix_scalar(uint64_t left, uint64_t right);
```

Arguments use RDI/RSI; RAX contains the exact result and RDX is zero.
`Scalar.Stack` requires an aligned, nonwrapping, readable/writable reservation
of `272 * D` bytes, where `D > selected entry index`. This includes the caller's
eight-byte return slot; `272 * D - 8` bytes lie below entry RSP. The bound is
conservative and includes earlier helper ranks even on shorter paths.

The emitted-object theorem proves return to the initial stack return address,
RSP advancing by eight after RET, preserved System V saved registers, and
unchanged bytes outside the reservation. Invalid mappings trap in the model;
the ABI requires the mapping and alignment and does not install native stack
guards. General occupied heap bounds and allocating calls remain F1/A1 work.

## Proof and source boundaries

`PhysicalScalarValues` relates every physical register to its selected scalar
operand. `PhysicalScalarControl` composes instruction and edge executions
under arbitrary suspended callers and heaps. `Code.simulate` composes these
contracts over the actual syntax certificate; `Selected.contract` closes the
induction over earlier callees. `Runs.agrees` compares the constructed run with
any successful physical run, even with different evaluator budgets.

`ExportPath.runMain` proves that the actual module entry returns the
uncaptured closure selected for the runtime ABI. `Compiled.physicalReturns`
then composes physical agreement with the existing scalar frame/call,
finite-stack, instruction-stream, and complete-object proofs. Nine axiom
fences retain the ordinary `propext`, `Classical.choice`, and `Quot.sound`
basis; this extension adds no axiom or native interface.

The retained source attachment binds selection to the ordinary compiler's
physical output. This new universal theorem starts at a **physical function
invocation**; a general open Ixon-application-to-physical-invocation bridge is
not claimed here. Source agreement for the six fixtures is independently
executed across all stages on every boundary pair. The earlier arithmetic
attachment retains its own universal source-application theorem.

Objects use the actual IxIR₁ graph root with lowering version **6**, policy
version **1**, and policy name `physical-scalar-cfg/1`. Physical JSON is a full
diagnostic snapshot, not a canonical IxIR₂ persistence format; I2 remains
separate. The local reference ISA, immutable text mapping, system
linker/loader, and compiler/runtime seed retain their existing trust boundaries.

## Reproduction and evidence

```sh
lake build source-native-physical-scalar check-source-native-physical-scalar
.lake/build/bin/check-source-native-physical-scalar \
  --fixture .lake/build/bin/source-native-physical-scalar \
  --cc cc --harness fixtures/source-native-physical-scalar/native_harness.c
```

| Source family | Selected functions / physical blocks | Text / object bytes | Stack bytes |
| --- | --- | --- | --- |
| `project` | 1 / 1 | 90 / 952 | 272 |
| `tag` | 2 / 4 | 310 / 1,168 | 544 |
| `pred` | 2 / 4 | 307 / 1,168 | 544 |
| `choose` | 2 / 4 | 308 / 1,168 | 544 |
| `helpers` | 3 / 7 | 551 / 1,408 | 816 |
| `nested` | 3 / 7 | 601 / 1,464 | 816 |

The synthetic sources use nonrecursive Nat recursors and direct mutual-member
references. The source compiler supplies every intermediate graph. All 114
boundary inputs run in Ixon, raw IxIR₀, addressed IxIR₁, logical and physical
IxIR₂, typed x86, and the actual ELF interpreter, including maximum Words.
Four separate physical CFG cases exercise joins, simultaneous swaps,
nonmonotonic block ordering, and a nullary helper on 76 more inputs.

The gate rejects 26 malformed/oversized CFGs, 30 invalid exports, three
oversized input vectors, and 11 insufficient/unwritable stack cases. An
independent checker verifies source/IR/export bindings, selection maps, ELF
fields, text hashes, provenance, observations, and complete fresh artifact
inventories; 42 deliberate corruptions must reject. Two fresh generations of
all 13 files must be byte-identical.

On x86-64 Linux, an independent C oracle checks 19 boundary and 64
deterministic random pairs per object on normal and guarded finite stacks:
**996 linked native calls**. The Nix check is `source-native-physical-scalar`;
other configured platforms run artifact checks without claiming x86 execution.
These are correctness checks, not a performance experiment.
