# Checked source recursion recovery

D1's first schema, D2's physical composition, and R2's terminal resources are delivered by
[`Recursion.compileValidated`](../Compilatrix/Recursion/Pipeline.lean).
Canonical synthetic Ixon programs pass the existing validated compiler,
recover a direct accumulator loop from its exact raw IxIR₀ erasure, and run
through ordinary ownership lowering, complete IxIR₁ addressing, checked
IxIR₂ lowering, and dynamic reuse. Callers supply source constants and
configuration; they supply no intermediate IR.

The source-facing theorem reaches the actual selected physical IxIR₂ after
recovery, including checked baseline fallback when reuse is skipped. Outer
fallback preserves successful execution of the original owned IxIR₁ artifact.
All intermediate executions and compiler contracts are derived internally.
This exit does not establish general `brecOn`
recognition, ordinary Lean/Std compilation, native heap execution, or a
universal optimized cost theorem.

## Recognized source and checked replacement

The [source builder](../Compilatrix/Recursion/Sources.lean) constructs a
non-nested Nat-list inductive with one immediate recursive tail, a generic
structural recursor with base and step minors, and known minor definitions
that eagerly construct a `below` tuple. Its function field reverses the list
onto an accumulator. In schematic notation, omitting the source gate's
erased-argument wrappers:

```text
base                 = pack (fun acc => acc) unit
step head tail below = pack (fun acc => (proj 0 below) (cons head acc)) below
literal xs acc       = (proj 0 (List.rec base step xs)) acc

direct acc nil           = acc
direct acc (cons head xs) = direct (cons head acc) xs
```

The eager source fold creates its entire tuple chain before applying the
function projection. The derived recursor absorbs the accumulator before
the major argument, so its recursive call is saturated and in tail position.
The ordinary lowerers preserve that call as one `tailCallSelf`; the reuse
pass inserts one reset/credit diamond with two helper blocks.

[`IxIR0.Recursion.propose`](../Compilatrix/IxIR0/Recursion.lean) extracts only
addresses, literal Nat-list contents, and the optional returned-pair shape.
The separate `check` compares the complete recursor rules, minor bodies,
constructors, binders, projections, and entry against the actual environment
using its first-binding lookup rule. A proposal cannot choose a replacement
body. The current entry grammar is a closed list call with an empty
accumulator, optionally returning the original input alongside its reversal.
The fixture builder permits at most 64 elements; ordinary compiler budgets
still bound validation and lowering.

The derived declaration gets its canonical `IxIR0.Decl.address`. Recovery
rejects a collision with any original declaration key and checks the target
lookups. Source constructor identities are preserved. Complete IxIR₁
addressing then gives the emitted loop its actual target key, which owns the
checked case-constructor and shared-parameter sidecars.

The original `Pipeline.ValidatedCompilation` remains in every successful
result. Unrecognized shapes, rejected proposals, and optional ownership/CFG
lowering or attachment failures retain that literal artifact and a typed reason. Reuse
selection separately retains its checked baseline if its optional rewrite
fails. Original source validation failures remain errors.

## Theorem boundary

[`IxIR0/RecursionSim.lean`](../Compilatrix/IxIR0/RecursionSim.lean) proves the
eager tuple fold, the projected function application, and the direct loop
against the actual fuelled IxIR₀ evaluator. `recursorForwardSimulation`
covers arbitrary finite lists of element values and arbitrary accumulator
values, beyond the recognizer's literal Nat-list entry grammar.
`Recovered.forwardSimulation` covers the exact checked closed entry,
including its erased-argument wrappers and retained alias.
`Selection.forwardSimulation` includes literal fallback.

[`Compilation.sourceRefines`](../Compilatrix/Recursion/Sim.lean) composes the
validated source certificate, erasure in its actual member scope, and this
selection theorem. Its premises are successful Ixon evaluation and the
existing sharing/oracle contracts. It derives a successful evaluation of
the exact selected IxIR₀ program with the existing `InlinedValRel`; callers
supply no intermediate execution or recognizer correctness premise.

[`Compilation.sourceRefinesSelected`](../Compilatrix/Recursion/PhysicalSim.lean)
extends that result through the actual executable outcome. It has the same
successful Ixon evaluation and sharing/oracle premises. Its `SelectedExecution`
conclusion has two branches:

- A recovered result executes `lowered.reuse.target` under the physical
  IxIR₂ evaluator, with existential control and heap fuel. The value relation
  composes source erasure, fully addressed ownership lowering, baseline
  lowering, and the existing stable-heap/value relation for selected reuse.
- A literal result executes the original compilation's owned, fully addressed
  IxIR₁ main. Its relation retains both the original IxIR₀ address map and the
  complete IxIR₁ rebuild map. This also covers optional backend failures.

[`LoweredCompilation`](../Compilatrix/LoweredCompilation.lean) retains the
exact IxIR₀ input and `FullyAddressedTrace`, plus a checked certificate that
each source row matches first-binding lookup and both declaration environments
exclude externs. Existing validated source compilations project this common
record without recompilation. Recovery checks the certificate on its generated
program, then uses the same HPT producer and checked CFG attachment as the
original source frontend. `CompiledAttachment` retains the exact input,
sidecars, HPT certificate, compiler equation, and trace checks. The public
source `Attached` record remains available through its `.compiled` projection;
existing backend theorem names remain aliases for direct application.

[`Recovered.projectionSafe`](../Compilatrix/Recursion/Trace.lean) derives the
call-aware trace from successful evaluation of the projection-free recovered
program. The [common lowering proof](../Compilatrix/LoweredCompilationSim.lean)
derives declaration correspondence, compiler contracts, progress, ownership,
and addressed execution from its retained trace and certificate. The baseline
physical bridge and `selectedPhysicalMainSimulation` then derive execution of
the selected program. Callers supply none of these intermediate premises.

Fifty [axiom fences](../Compilatrix/Fence.lean) pin the recovery, composition,
resource, and comparative boundaries: D1's five, D2's seven, R2's nine, and
R3's twelve, plus R4's seventeen. The local
tuple and recursor theorems use `propext`, `Classical.choice`, and `Quot.sound`.
The addressed wrappers additionally retain the existing ledgered BLAKE3
assumption through the derived declaration's identity. No new axiom or native
interface is introduced. The source-facing endpoint uses the shared main
world accepted by this recovery frontend; the common compilation record is
parameterized by the main world.

[`Compilation.sourceRefinesSelectedWithResources`](../Compilatrix/Recursion/Resources.lean)
adds resource guarantees to the same source premises and the same returned
value. For recovered outcomes, `Result.SharedResources` states
`live + frees = allocs` at physical halt and supplies a successful shared
release with `live = 0` and `allocs = frees`. Literal fallback retains its
original owned IxIR₁ execution, value relation, and complete result release.
The theorem covers every accepted recovery/attachment record, including the
selected optimizer's checked baseline branch; it is not restricted to the
eight fixtures.

The proof separates resources from the unchanged semantic heap relation.
[`HeapAccounting.lean`](../Compilatrix/IxIR2/HeapAccounting.lean) proves the
actual heap-operation and credit-transfer balances.
[`Resources.lean`](../Compilatrix/IxIR2/Resources.lean) proves that every
successful physical step preserves
`live + frees + presentCredits = allocs`, counting credits in the current
frame and every continuation. Initial execution establishes this invariant;
halt leaves no outstanding reservation balance. The store represents freed
and reserved slots with the same absent-node entry, so the balance accounts
for reservations without inventing a separate bitmap.

[`ReuseResources.lean`](../Compilatrix/IxIR2/ReuseResources.lean) transports
successful result release through the existing exact-content or history
isomorphism. [`PipelineResources.lean`](../Compilatrix/IxIR2/PipelineResources.lean)
derives the baseline's ownership, allocation order, and positive RC facts
from its actual owned execution and checked compiler attachment. Its
`selectedSuccessfulSharedResources` theorem also covers any successful run
of the selected program with different sufficient fuel. No caller supplies
a heap invariant, release witness, or intermediate compiler fact.

Allocation accounting applies to successful physical executions in either
ownership world; the selected reclamation and source composition endpoints
currently require a shared main result. Release has its own sufficient fuel
budget.

[`Compilation.sourceRefinesSelectedWithAllocationLaws`](../Compilatrix/Recursion/Allocation.lean)
retains exactly that source domain, value relation, and resource endpoint.
For a recovered result, it additionally supplies an actual physical run of
the checked ownership/CFG baseline and proves
`baseline.allocs = selected.allocs + selected.reuses` and
`baseline.frees = selected.frees + selected.reuses` at halt. Both results
admit complete shared release at the same sufficient traversal budget, after
which the free equation still holds. The comparison is with the recovered
baseline; it does not quantify the separate tuple-fold recovery savings.

[`AllocationEvents.lean`](../Compilatrix/IxIR2/AllocationEvents.lean) counts
fresh allocations plus physical reuses. The actual compiler macros preserve
this total, including hot/cold prefixes, partial application, and recursive
returns. The common lowering trace derives zero baseline reuse internally.
[`PipelineAllocation.lean`](../Compilatrix/IxIR2/PipelineAllocation.lean)
combines this evidence with equal live-node counts and R2's heap balances.
`successfulPhysicalAllocationLaws` covers any actual successful baseline and
selected runs with independent sufficient fuel, in either selection branch.
The counter invariant remains separate from `StableHeapRel` and
`PhysicalValueRel`; no extra rewrite-shape or heap premise narrows the shared
compiler domain.

[`Compilation.sourceRefinesSelectedWithCostLaws`](../Compilatrix/Recursion/Costs.lean)
adds `selected.rcops ≤ baseline.rcops` and
`selected.peakLiveNodes ≤ baseline.peakLiveNodes` to the same source premises.
Its `CostComparison` retains the actual baseline, R3's allocation/free laws,
and both results' shared resources. `ReclaimedCostLaws` carries the two actual
releases at a common sufficient budget, their empty balanced heaps, the free
equation, and both cost bounds after release. Literal fallback retains R3's
endpoint. Neither a new heap assumption nor a narrower rewrite-shape domain
is required.

The existing IxIR₁ reference-count potential now lives in
[`RcPotential.lean`](../Compilatrix/IxIR1/RcPotential.lean), with its original
public cost names preserved. `rcops + pendingRC` accounts for executed RC
operations and outstanding shared references. Deep release conserves this
sum; retaining a heap reference increases it by two. Heap correspondence
preserves pending references, so corresponding ordinary steps have equal RC
increments. The hot macro performs no selected RC work, while the cold macro
retains the same fields and decrements the same shared owner as the baseline.
[`CostObservations.lean`](../Compilatrix/IxIR2/CostObservations.lean) and
[`ReuseCost.lean`](../Compilatrix/IxIR2/ReuseCost.lean) supply these facts as
separate cost evidence, leaving semantic relations unchanged.

[`CostSteps.lean`](../Compilatrix/IxIR2/CostSteps.lean) proves the exact peak
update for every successful instruction and terminator, including heap work
inside dynamic application. Peaks record every allocation and never decrease.
`PrefixCostBounds` covers every actual selected execution prefix, including
the reset/branch/allocation states inside a macro: its RC count, recorded peak,
and live-node count fit within the actual baseline's terminal RC and peak
counters. [`successfulPhysicalCostLaws`](../Compilatrix/IxIR2/PipelineCosts.lean)
also covers independently chosen sufficient control and heap budgets for the
two runs, in both selection branches. Separate [source-map](source-call-reuse.md)
and [unique reversal](source-unique-reuse.md) endpoints extend calls and static
reuse, and [native unique reversal](source-native-unique.md) supplies the bounded
heap witness. General credit refinement and native execution of this shared
fold schema remain further work.

## Source observations

The [reviewed matrix](../fixtures/source-recursion/expected.json) covers
empty, singleton `[17]`, three-element `[1, 2, 3]`, and mixed
`[0, 3, 3, 2^64, 1, 42, 0]` inputs, each with and without a retained alias.
All eight cases contain 14 canonical Ixon constants. These are synthetic
sources exercising the real ingress and compiler, rather than upstream
exports. The large Nat is preserved without a machine-word conversion.

[`Observations.lean`](../Compilatrix/Recursion/Observations.lean) checks the
source block, inductive index, constructor tag, and fields when reading Ixon
values, and the full constructor identities at every IR stage. Ixon, literal
raw/addressed IxIR₀, recovered IxIR₀, literal and recovered raw/addressed
IxIR₁, and both interpretations of the baseline and rewrite agree.
Addressing preserves complete terminal stores; the baseline interpretation
comparison also preserves counters and remaining budgets. Every one of the
eight heap executions per case releases the actual returned value, leaves
zero live nodes, and balances allocations with frees.

The three-cons observations before final reclamation are:

| Input ownership | Executed stage | Allocations | Frees | RC operations | Hot / cold resets | Reuses |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Unaliased | Literal IxIR₁ | 29 | 25 | 69 | — | 0 |
| Unaliased | Recovered baseline | 8 | 4 | 10 | 0 / 0 | 0 |
| Unaliased | Physical reuse | 5 | 1 | 1 | 3 / 0 | 3 |
| Retained alias | Literal IxIR₁ | 30 | 21 | 67 | — | 0 |
| Retained alias | Recovered baseline | 9 | 0 | 8 | 0 / 0 | 0 |
| Retained alias | Physical reuse | 9 | 0 | 8 | 0 / 3 | 0 |

The unaliased physical run reuses six payload units and peaks at five live
nodes; the aliased run peaks at nine. These reproduce the established
IxIR₀-sourced witness's recovered counters. Every nonempty input has one
reset per cons; the empty cases have none. The logical rewrite counts fresh
allocation/free pairs where physical execution reuses a slot. The checker
compares the corresponding terminal accounting equations and reruns the
optimizer to check idempotence. The baseline/selected allocation and free
equations instantiate R3's general shared-main theorem. The physical
baseline/selected RC and peak comparisons instantiate R4; the checker verifies
both inequalities at halt and after release. Exact per-case counts and the
separate literal-to-recovered savings remain finite fixture measurements.

The 25 [rejection and fallback checks](../Compilatrix/Recursion/Rejections.lean)
exercise the actual source erasure, recovered lowering certificate, and
compiler fallbacks. They cover altered recursor arity,
Nat peeling, extra rules, non-immediate recursion, constructor layout/tag,
minor bodies, escaping or deeper `below` projections, accumulator changes,
extra entry uses, first-binding shadowing, and fresh-address conflicts.
A real zero-depth CFG resource failure preserves the original checked
IxIR₁ bytes. An ordinary scalar still compiles and evaluates through literal
fallback; source freeze and extern rejection remain unchanged. Three common
lowering checks reject shadowed source declarations, a source extern, and an
emitted target extern.

## Reproducibility gate

```sh
lake build source-recursion check-source-recursion
lake exe source-recursion /tmp/new-recursion
lake exe check-source-recursion --fixture .lake/build/bin/source-recursion
```

The producer requires a new output directory and completes all cases and
negative checks before writing files. Without a directory it only runs the
checks. The independent
[`CheckSourceRecursion.lean`](../scripts/CheckSourceRecursion.lean) imports
no compiler or evaluator. It starts two fresh compiler processes, checks
their report against the reviewed matrix, verifies the exact nine-file
inventory, and compares every file byte for byte. It also checks snapshot
roots, HPT identities, and observations against the report, checks that the
common lowering input and sidecars match the recorded recovered graphs, and independently inspects all
reclaimed heaps for empty slots and balanced allocation counters. It checks
the physical baseline/selected allocation and free equations before and after
release, independently of the producer's checks and reviewed counter matrix.

Each snapshot contains canonical source bytes, literal-resolution and budget
configuration, complete literal raw/addressed IxIR₀ graphs and maps, the
checked recovery proposal and new declaration key, literal and recovered
IxIR₁ graphs with complete addressing preimages/maps, the common lowering
certificate checks, complete HPT candidates and canonical checked cache records,
all finite sidecars, and both IxIR₂ programs
with finite schemas, parameter worlds, case identities, rewrite reports,
and terminal/reclaimed stores. Proof terms are erased. IxIR₂ JSON remains a
diagnostic without a codec or persistent content-address claim. The case
snapshot format is `compilatrix/source-recursion-case/2`; the recovery policy
and report format are unchanged because the recognized and generated programs
are unchanged.

The `source-recursion` Nix check runs this gate alongside C1's unchanged
13-case coverage gate. The checker and frozen matrix have reviewed integrity
pins in the [trust ledger](trusted-extern-ledger.md). Refresh expectations
only after reviewing the source or compiler change explaining the drift;
the checker never updates them.
