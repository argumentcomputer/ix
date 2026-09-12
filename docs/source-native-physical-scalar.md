# Physical scalar CFG selection

The second N3 slice selects a bounded fragment of **actual physical IxIR₂**.
[`compileSourceExport`](../Compilatrix/X86/PhysicalScalarExport.lean) consumes
the existing validated source-to-IxIR₂ attachment, follows its exported
uncaptured closure, and emits one certified scalar ELF object. Selection
uses instruction, edge, and function contracts for every accepted CFG.

The universal source endpoint is
[`Exported.sourceNatReturns`](../Compilatrix/X86/PhysicalScalarSourceObject.lean):
successful runtime Ixon application on one or two exact Word Nats implies
execution of the emitted ELF with the same Nat result on a sufficient finite
stack. It derives the compiled closure application, physical invocation, and
native execution from the retained ordinary compilation. Source evaluation,
sharing/oracle assumptions, argument arity, and the stated ABI conditions are
its premises. It also proves complete reclamation of the source module's
exported closure in IxIR₁.

[`Compiled.physicalReturns`](../Compilatrix/X86/PhysicalScalarObject.lean)
retains the corresponding successful physical-run theorem.
`Compiled.nativeReturns` proves that every admitted Word input returns,
independently of source or physical execution certificates.

## Fragment and representation

| Boundary | Contract |
| --- | --- |
| Runtime values | Unsigned 64-bit Words representing exactly `IxIR₂.RVal.lit (.nat n)`, with `0 ≤ n < 2^64` |
| Signatures | Zero, one, or two scalar parameters and a scalar Nat result; uncaptured source exports have one or two parameters |
| Instructions | `move`, `retainShared`, `releaseShared`, `dropUnique`, and direct `call` |
| Terminators | `ret`, `jump`, direct `tailCall`, and `switchValue` with Nat peeling and no constructor alternatives |
| Edges | Arbitrary simultaneous value-argument substitutions, including joins and permutations; successor edges prepend the predecessor Nat |
| Control | Acyclic CFG expansion and nonrecursive calls to earlier selected functions |
| Credits and heap | No transferred reuse credits or allocating instructions; all runtime registers contain literal Nats |

Scalar ownership operations preserve the whole physical store. Release/drop
consume traversal fuel in the reference evaluator, even for scalar leaves;
the proof constructs that fuel and preserves its unused suffix. The native
invocation needs no heap capacity. Source module initialization returns one
ordinary shared PAP identifying the uncaptured entry function. Saturated
IxIR₁ application reclaims it before the scalar body runs: one dead slot,
one allocation, one free, one RC operation, zero reuse, and zero live nodes.
The physical body preserves this exact heap and its counters. The native
export enters the scalar body directly.

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
Unsupported graphs, captured exports through this adapter, cyclic aliases/CFGs, recursion, missing
targets, incorrect arities, credits, and exceeded limits return an error.
The existing checked physical artifact remains available for fallback.
The separate [captured export adapter](source-native-captured-scalar.md)
accepts one static Word capture and a unary runtime argument.

## ABI and finite resources

The gate exports the same scalar ABI as the first slice:

```c
struct scalar_result { uint64_t value, status; };
struct scalar_result compilatrix_scalar(uint64_t left, uint64_t right);
```

Arguments use RDI/RSI; RAX contains the exact result and RDX is zero.
The unary export takes one `uint64_t` argument in RDI; RSI is unrestricted.
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
uncaptured closure selected for the runtime ABI. `Exported.sourceFunction`
uses the ordinary source-to-physical theorem to identify that same closure
in the source value relation. The variadic source-application simulation
retains projection-safe IxIR₀ traces across mutual-block readdressing.
`ValidatedCompilation.runtimeApply` derives progress, value agreement, and
ownership from the retained IxIR₁ lowering run. `closureStore.applied` exposes
the actual PAP dispatch and reclamation prefix.

`CompiledAttachment.successfulFunctionSimulation` then derives physical
function execution through the existing structured lowering trace worker.
The source endpoint supplies its ownership, runtime invariants, and reachable
heap provenance internally. `Compiled.physicalReturns` composes that run
with scalar frame/call, finite-stack, instruction-stream, and complete-object
proofs. `Exported.sourceReturns` retains the general source value relation;
`Exported.sourceNatReturns` specializes it to `word.toNat = sourceNat`, with
no truncation. These theorems quantify over every accepted uncaptured scalar
source export and every successful admitted application, independently of
the fixture families. Source termination itself is a premise.

Nine physical-to-object axiom fences retain the ordinary `propext`,
`Classical.choice`, and `Quot.sound` basis. Eleven further fences cover the
source application bridge. The complete source-compiler endpoints also use
the existing Blake3 hash `native_decide` boundary, as the upstream compiler
theorems do. This extension adds no axiom or native interface. Allocating
bodies, broader recursion, and general occupied heaps remain outside the
fragment. Static captured exports use their separate adapter and provenance
policy. The earlier arithmetic attachment retains its
own universal source-application theorem.

Objects use the actual IxIR₁ graph root with lowering version **6**, policy
version **1**, and policy name `physical-scalar-cfg/1`. Physical JSON is a full
diagnostic snapshot. The separate [canonical IxIR₂ snapshot](ixir2-wire.md)
contract is available without changing this native provenance format.
The local reference ISA, immutable text mapping, system
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
| `unary-pred` | 2 / 4 | 300 / 1,160 | 544 |

The synthetic sources use nonrecursive Nat recursors and direct mutual-member
references. The source compiler supplies every intermediate graph. All 133
boundary inputs run through Ixon `applyMany`, raw IxIR₀ application,
addressed IxIR₁ module initialization and PAP application, logical and
physical IxIR₂ invocation, typed x86, and the actual ELF interpreter,
including maximum Words. Every application checks complete closure
reclamation and the physical body's preservation of the resulting heap.
The unary case supplies one source argument and checks a one-argument C call;
the varied second register remains unconstrained. The six existing objects
remain byte-identical to the original physical CFG slice.
Four separate physical CFG cases exercise joins, simultaneous swaps,
nonmonotonic block ordering, and a nullary helper on 76 more inputs.

The gate rejects 26 malformed/oversized CFGs, 35 invalid exports, three
oversized input vectors, and 13 insufficient/unwritable stack cases. Another
42 application boundary checks cover source/IxIR₁ partial application and
completion, excess application rejection, and missing/excess physical
arguments. An independent checker verifies source/IR/export bindings,
selection maps, ELF fields, text hashes, provenance, observations, and complete fresh artifact
inventories; 70 deliberate corruptions must reject, including changed
argument arity, runtime source arguments, and reclamation counts. Two fresh
generations of all 15 files must be byte-identical. Evidence format version
2 records source arities, actual application arguments, and exact heap counts.

On x86-64 Linux, an independent C oracle checks 19 boundary and 64
deterministic random pairs per object on normal and guarded finite stacks:
**1,162 linked native calls**. The Nix check is `source-native-physical-scalar`;
other configured platforms run artifact checks without claiming x86 execution.
These are correctness checks, not a performance experiment.
