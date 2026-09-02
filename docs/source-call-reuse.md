# Source maps with reuse across calls

R5 adds an optional `CallReuse.compileMap` endpoint for canonical synthetic
Ixon maps over closed Nat lists. The selected physical program keeps a reuse
credit in its caller while a worker call and recursive `callSelf` execute.
For three unaliased cons cells, this reduces allocations from 11 to 8 and RC
operations from 13 to 4, with peak live nodes unchanged at 4. The composed
source theorem covers actual selected execution, checked fallback, complete
shared-result reclamation, and the R3/R4 allocation, free, RC, and peak laws.

This first source schema maps a constant-returning worker over a finite list.
It accepts arbitrary Nat elements and replacement values, including values
above 64 bits, and an optional retained suffix that forces some or all resets
cold. It does not establish general higher-order map specialization, ordinary
Std compilation, static unique reuse, general credit-language refinement, or
native heap execution.

## Versioned call contract

[`CreditPolicy.lean`](../Compilatrix/IxIR2/CreditPolicy.lean) defines
`call-local/0` and `suspended-direct-calls/1`.
The existing `Validate.validateWith` and `Eval.runMain` APIs retain v0.
`Validate.validateWithPolicy` and `Eval.Policy.runMain` take the explicit
policy; `Policy.runMain_v0` proves exact agreement with the old runner.

Under v1, only non-tail `call` and `callSelf` may execute with live credits.
The entire caller frame, including its credit file, moves into the return
continuation. The callee begins with an empty credit file and cannot access
ancestor reservations. A return restores the caller's credits unchanged.
The caller must subsequently consume or discard every credit, or transfer it
once per outgoing CFG edge. Required credits and optional present/absent credits
follow the same ownership rule. Return, tail calls, PAP construction, dynamic
application, and extern invocation retain their empty-credit boundary.

`Machine.ReservationOwnership` counts present physical reservations across
the current frame and every suspended continuation. Its locations are unique
and refer to existing empty heap slots. Ordinary steps and v1 call suspension
preserve this invariant; `runMain_prefix_reservationOwnership` derives it
for every actual execution prefix from an empty initial machine.
The allocation account includes suspended reservations:

```text
live nodes + frees + present reservations = allocs
```

At halt no continuation or credit remains, giving `live + frees = allocs`.
A required or present optional discard increments `frees`; consuming a
present credit increments `reuses` instead of `allocs`. An absent optional
credit allocates fresh. Reservation identity remains separate from layout
compatibility and from runtime value identity.

## Checked source and compiler path

[`Sources.lean`](../Compilatrix/CallReuse/Sources.lean) creates twelve canonical
Ixon constants per case. The list and its generic recursor belong to the same
data block, as required by Ixon evaluation. The generic recursor receives base
and step minors; the step invokes the worker and constructs the mapped cons.
The inputs to this endpoint are Ixon constants and a root, never replacement
IxIR₁ or IxIR₂ programs.

[`IxIR0/MapRecovery.lean`](../Compilatrix/IxIR0/MapRecovery.lean) recognizes the
actual raw erasure. It checks the entry, generic recursor, base, step, worker,
nil/cons identities and layouts, and optional retained suffix against an exact
schema. It specializes that checked schema to a direct recursor under
`closed-map-specialize/1`. The derived declaration receives a canonical IxIR₀
address; conflicts and failed target checks select the original source.
`MapRecoverySim.lean` proves successful eager-fold and direct-map evaluation
for every finite Nat list in the checked schema, and composes their equality
with the selection, including literal fallback.

[`MapPipeline.lean`](../Compilatrix/CallReuse/MapPipeline.lean) sends the checked
specialization through ordinary ownership lowering and addressed rebuilding.
It derives parameter worlds from the actual emitted signatures, constructor
sidecars from the checked source identities, and HPT artifacts from the actual
IxIR₁ graph. The common lowering certificate and checked IxIR₂ attachment retain
the exact compiler equations. An optional specialization or backend failure
keeps the original validated literal IxIR₁ artifact and its owned execution.

The backend pass [`IxIR2/CallReuse.lean`](../Compilatrix/IxIR2/CallReuse.lean)
uses policy `shared-call-reuse/1`. Its accepted block shape is:

```text
fetch every field; retain every field; release the source owner
one or more direct call / callSelf instructions
allocate a compatible shared constructor; return
```

The pass replaces the consuming prefix with `resetShared` and register moves,
suspends its optional credit through the calls, then uses `allocWith`.
It checks exact syntax, positive field count, an owned shared source,
last use, a nonempty direct-call sequence, and exact layout compatibility.
Register moves preserve the original call/result numbering.
The whole target is validated under v1. Unsupported source structure or target
rejection retains the checked baseline and its v0 execution policy.

`CallReuse.compileValidated` also exposes this pass directly on an ordinary
checked IxIR₂ source attachment. The map endpoint adds only the separately
checked source specialization needed to produce this non-tail recursive shape.

## Semantic and resource interfaces

`CallReuse.Sim.simulate_to_halt` proves simulation of actual finite baseline
execution. It reconstructs the accepted fetch/retain/release prefix from that
execution, relates hot and cold resets, and follows direct and recursive calls,
caller return, ordinary instructions, CFG edges, PAP application, and residual
dispatch. The proof derives reservation ownership from the actual target steps.
It handles suspended credits while related callees allocate and free nodes;
no caller-supplied continuation or per-step proof callback is needed.

The heap transition carries separate allocation-event and RC/peak facts.
`Output.mainSimulation` and `Selection.mainSimulation` preserve the existing
`StableHeapRel` and `RValIso` semantic interfaces. The common
[`PipelineCallReuse.lean`](../Compilatrix/IxIR2/PipelineCallReuse.lean) derives
owned baseline heaps from the compiler's actual successful source run.
Its selected and arbitrary-successful-run theorems prove:

```text
baseline.allocs = selected.allocs + selected.reuses
baseline.frees  = selected.frees  + selected.reuses
selected.rcops <= baseline.rcops
selected.peakLiveNodes <= baseline.peakLiveNodes
```

Both results have complete shared-result releases to empty balanced heaps.
The same releases preserve the free equation and RC/peak bounds.
Every selected prefix has its RC count, recorded peak, and live-node count
bounded by the actual baseline's terminal counters. These include states
inside reset macros and nested calls. The successful-run interface allows
independent sufficient control and heap budgets for the two executions.

`CallReuse.Compilation.sourceRefinesWithCostLaws` and
`CallReuse.MapCompilation.sourceRefinesWithCostLaws` compose these results
from only the existing successful Ixon evaluation, source sharing, and
configured oracle premises. The map theorem covers every accepted record,
both inner reuse selections, and owned literal fallback with reclamation.
Comparative costs use the specialized program's checked physical baseline;
literal-to-specialized allocation differences are separate observations.
The ordinary and map value relations retain source inlining, addressed value
graphs, lowering's outcome relation, and the established heap/value relation.

Twenty-five new [axiom fences](../Compilatrix/Fence.lean) retain the existing
Lean and addressed-BLAKE3 trust basis. The generic call simulation, reservation
ownership, and local resource laws use only ordinary logical axioms.

## Executable evidence

All nine cases run actual Ixon, raw/addressed IxIR₀, specialized IxIR₀,
literal and specialized raw/addressed owned IxIR₁, and logical/physical
baseline and selected IxIR₂. They compare full constructor-aware values and
reclaim every heap. The retained suffix remains observable in the result.

| Case | Baseline allocs → selected | Baseline RC → selected | Peak | Hot / cold resets |
| --- | --- | --- | --- | --- |
| Empty, unaliased | 2 → 2 | 1 → 1 | 1 | 0 / 0 |
| Empty, retained alias | 3 → 3 | 2 → 2 | 3 | 0 / 0 |
| Singleton, unaliased | 5 → 4 | 5 → 2 | 2 | 1 / 0 |
| Singleton, retained alias | 6 → 6 | 5 → 5 | 5 | 0 / 1 |
| Three, unaliased | 11 → 8 | 13 → 4 | 4 | 3 / 0 |
| Three, retained alias | 12 → 12 | 11 → 11 | 9 | 0 / 3 |
| Seven mixed Nat values, unaliased | 23 → 16 | 29 → 8 | 8 | 7 / 0 |
| Seven mixed Nat values, retained alias | 24 → 24 | 23 → 23 | 17 | 0 / 7 |
| Five values, retained suffix after two | 18 → 16 | 19 → 13 | 11 | 2 / 3 |

Peak is unchanged in each comparison. Every nonempty run suspends a caller
twice per cons, and recursive descent holds up to one optional credit per cons.
The final case exercises hot and cold credits in the same recursive execution.

The 35 additional checks cover required/optional call credits, both reset
decisions, discards after return, nested independent owners, CFG transfer,
callee exclusion from ancestor credits, duplicate/omitted credits, incompatible
layouts, prohibited boundaries, unsupported rewrite sites, source-schema
mutations, derived-address conflicts, and actual checked/literal fallback.

## Reproducibility gate

```sh
lake build source-call-reuse check-source-call-reuse
lake exe check-source-call-reuse --fixture .lake/build/bin/source-call-reuse
# Optional: write all snapshots to a new directory.
lake exe source-call-reuse -- /tmp/source-call-reuse-snapshots
```

The `source-call-reuse` Nix check runs
[`CheckSourceCallReuse.lean`](../scripts/CheckSourceCallReuse.lean).
This independent checker imports only shared check helpers. It compares the
complete file inventory and every byte from two fresh compiler processes,
then checks the [reviewed report](../fixtures/source-call-reuse/expected.json).

Snapshots retain the canonical source, raw/addressed/specialized graphs,
complete HPT records, finite sidecars and lowering checks, baseline/selected
IxIR₂ diagnostics, every value and heap, and all actual selected prefixes.
For each prefix the checker independently checks unique reservation owners,
empty-slot exclusion, allocation balance, and RC/peak/live bounds.
It also checks terminal/reclaimed comparative laws. Seven corruption
regressions alter RC and peak counters at halt and after release, the execution
policy, duplicated reservation owners, and a reservation's empty-slot evidence.

[`Provenance.lean`](../Compilatrix/CallReuse/Provenance.lean) hashes canonical
metadata under `compilatrix/call-reuse-provenance/1\0`: source root, complete
addressed IxIR₁ graph root, ordered HPT roots, lowering depth/version, pass
version, selected execution policy, selection outcome, and optional source
specialization policy/address. Each case verifies that changing execution
policy changes both the preimage and its digest.
This is IxIR₁-plus-policy provenance. IxIR₂ diagnostic JSON has no wire,
persistence, or cache identity claim; a canonical IxIR₂ codec remains future
work. The new checker and reviewed report are pinned in the trust ledger.

