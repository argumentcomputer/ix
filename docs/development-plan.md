# Development plan

Reviewed 2026-09-07 against the current working tree, including IxIR₂, x86,
source coverage, recursion recovery, physical composition, terminal resources,
comparative costs, reuse across non-tail calls, static unique reversal, and
the Lean checks.
The [roadmap](roadmap.md) owns milestone states and queue
order. This document records the review findings, implementation boundaries,
and acceptance criteria behind that queue. Local `plans/` documents retain
the broader design alternatives.

## Review findings

The strongest part of the codebase is its checked artifact boundary: exact
compiler equations, source provenance, bounded analysis checks, executable
semantics, and axiom fences connect substantial pieces of the pipeline.
The highest-value next work is composing those pieces into source-facing
entry points and exercising them on accepted source programs.

| Finding | Code evidence | Planning consequence |
| --- | --- | --- |
| The baseline lowering induction is assembled. | [`Attached.successfulCanonicalMainSimulation`](../Compilatrix/IxIR2/PipelineSim.lean) derives the IxIR₁→logical-IxIR₂ whole-main result from a checked attachment. | Retire “finish the baseline induction” from active plans. Preserve its exact source-success and fragment boundary. |
| Dynamic reuse now has semantic, resource, and comparative cost boundaries. | [`OptimizedAttachment.physicalMainSimulationWithCosts`](../Compilatrix/IxIR2/ReuseLiveSim.lean) preserves the selected physical execution with RC/peak bounds. [`PipelineResources.lean`](../Compilatrix/IxIR2/PipelineResources.lean), [`PipelineAllocation.lean`](../Compilatrix/IxIR2/PipelineAllocation.lean), and [`PipelineCosts.lean`](../Compilatrix/IxIR2/PipelineCosts.lean) compose reclamation and counter laws, including all intermediate selected states. | Preserve the separate semantic and cost interfaces when extending credit lifetimes. |
| Baseline interpretation transport is now explicit. | [`Attached.successfulPhysicalMainSimulation`](../Compilatrix/IxIR2/PipelinePhysical.lean) composes logical lowering with exact execution transport using the checked absence of credit operations. | Reuse this public bridge; general credit refinement remains a separate, stronger obligation. |
| A synthetic Ixon input now reaches native execution. | [`ValidatedScalar.compile`](../Compilatrix/X86/ValidatedScalar.lean) retains the real compiler and selector equations. [`sourceScalarRefines`](../Compilatrix/X86/PipelineSim.lean) connects successful source evaluation to the actual typed target. C1 compares complete artifacts across fresh compiler processes. | Preserve the scalar and coverage gates; keep native heap/FIP support separate from this exit. |
| Reuse has separate diagnostic and production selection APIs. | [`Reuse.selectWith`](../Compilatrix/IxIR2/Reuse.lean) retains a checked baseline and typed skip report after target rejection; `selectAttachment` is total on checked compiler attachments, and `selectedPhysicalMainSimulation` covers both outcomes. | Preserve source rejection as an error and keep optional rewrite failure separate from compilation failure. |
| Recursion recovery now has a composed source cost endpoint. | The [source-recursion record](source-recursion.md) covers eight synthetic Ixon list folds and 25 rejection/fallback checks. `Compilation.sourceRefinesSelectedWithCostLaws` derives the actual selection, unchanged value relation, shared reclamation, and allocation/free/RC/peak comparison with the checked physical baseline from D2's source premises. | Preserve the shared-result domain; generalize recognition from measured source cases. Ordinary Lean/Std acceptance remains unestablished. |
| Shared reuse now survives direct calls. | The [source-map record](source-call-reuse.md) covers a separately versioned validator/runner, unique continuation-owned reservations, a checked source specialization, and actual selected source execution with reclamation and comparative costs. | Preserve v0 behavior and the explicit v1 compiler domain when extending selection. |
| Static unique reversal now has a source cost endpoint. | The [unique-list record](source-unique-reuse.md) connects checked Ixon usage and mode identities to consuming IxIR₁, validated IxIR₂, exact no-RC costs, all-prefix ownership, and full release for arbitrary accepted finite Nat lists. | Use this actual compiler artifact as the first native heap-selection input; general unique lowering retains a separate domain gate. |
| Production-source coverage is still narrow. | The [C1 matrix](source-coverage.md) covers accepted synthetic Ixon calls/dispatch and preserves the Std `freezeNeeded` rejection in a closed 17-constant slice. | Preserve this real production boundary; synthetic recovery does not remove it. |
| Proof organization is becoming a maintenance risk. | At review time `ReuseLiveSim.lean` exceeds 25,000 lines, `ReuseSim.lean` 19,000, and both lowering/pipeline simulation modules 11,000. | Consolidate stable interfaces after the current composition cut; measure elaboration cost before choosing performance refactors. File size alone is not evidence of slow builds. |

## R1 — dynamic reuse composition, delivered

Work in `IxIR2/ReuseLiveSim.lean`, using the existing checked lowering and
rewrite traces. Keep accepted reset prefixes as positive execution macros;
their internal fetch/retain/release states need not satisfy the global
synchronization invariant. Keep dead append-only caller registers outside
the observable-root relation, while retaining every pending `applyMore`
argument.

Delivered cuts:

1. **Delivered:** reconstruct an accepted constructor child's entry and
   recognized prefix from the selected edge, child trace, and actual successful
   baseline suffix. `attachedPhysicalSwitchCtorMacroOfTarget` handles empty
   and nonempty generated prologues; `attachedPhysicalTerminatorAdvanceHistory`
   no longer takes an accepted-child callback. Ordinary entries and constructor
   children share the retain/release/allocation/tail suffix proof.
2. **Delivered:** `CompilerStackHistory` carries source execution through
   operations, cases, calls, PAP preparation, and both tail-call forms.
   `returnResumeOfTarget` reconstructs ordinary caller resumption internally;
   `attachedPhysicalTerminatorAdvanceHistory` no longer takes an ordinary-return
   callback. `returnApplyMoreOfTarget` reconstructs all four residual dispatcher
   branches from the actual transfer. It restores the caller or composes its
   original PAP prefix into the next callee's history, including repeated
   over-application. The physical terminator wrapper has no return callbacks.
3. **Delivered:** `attachedPhysicalCompilerAdvance` derives progress for every
   successful baseline head. The physical finite-execution and runner theorems
   discharge their progress obligations internally from the halted suffix.
4. **Delivered:** `OptimizedAttachment.physicalMainSimulation` instantiates the
   exact initial machines and preserves successful physical baseline main runs
   in the exact validated optimizer output. It retains related heaps and values
   and at least the baseline's remaining heap budget. N1 now supplies the
   baseline interpretation bridge needed by source-facing composition.
5. **Delivered:** `Reuse.selectWith` and `selectCheckedWith` retain a checked
   baseline with a typed skip report after target rejection. `selectAttachment`
   is total at the compiler boundary; `selectedPhysicalMainSimulation` covers
   optimized and fallback execution. Invalid source input remains an error.

Exit evidence: axiom-fenced whole-main theorems whose callers supply the
checked artifact and a successful physical baseline execution, without progress
callbacks or manufactured ownership/continuation facts. The regressions cover
accepted constructor children, reuse after suspended calls, both tail-call
forms, recursive over-application, all four residual dispatch branches, and
hot/cold resets. A real target-validation limit failure exercises fallback;
the corresponding source limit failure remains an error.

The existing three-cons fixture supplies useful counter expectations: three
hot resets and reuses with five fresh allocations when unaliased; three cold
resets, zero reuses, and nine allocations with the retained alias. Both
results must reclaim fully. This is an IxIR₀-sourced compiler witness;
source-recursion recovery has its own exit below. An additional IxIR₁-sourced
regression selects a nullary constructor branch and reuses a different inherited
node: the unaliased case has one hot reset, one reuse, and three allocations;
the aliased case has one cold reset, zero reuses, and five allocations. Its
physical baseline, logical rewrite, and physical rewrite agree and reclaim fully.

The PAP-return regression adds explicit IxIR₁ adapters around the IxIR₀-derived
reversal. Exact application and two successive over-applications reach an
addressed tail call followed by self tail calls. All four hot/cold routes compare
logical and physical baselines with both rewrites and reclaim fully. The exact
route adds one PAP allocation/free and three RC operations; the recursive route
adds three PAP allocations/frees and five RC operations.

Two further hand-written IxIR₁ fixtures force immediate residual dispatch.
The erased route allocates and frees three nodes with three RC operations.
The under-saturated route returns a PAP holding two distinct shared owners:
five allocations, two frees, four RC operations, and three live nodes before
final reclamation. The baseline and rewrite agree in both interpretations and
reclaim fully.
The production selector regression permits three blocks per function, accepts
the baseline, rejects the proposed five-block function, reports the exact
target limit, and runs the baseline to the expected result with no reuse.

Semantic reuse relations intentionally forget some counters. R2 now proves
terminal allocation accounting and shared-result reclamation separately from
those relations. R3 supplies the allocation-event trace proof for comparative
allocation/free laws. R4 adds separate RC/peak certificates to the same actual
compiler macros, with a prefix theorem that covers their intermediate states.

## N1 — validated source-to-native scalar, delivered

`X86.ValidatedScalar.compile` builds a canonical synthetic Ixon constant for
an erased-argument lambda application returning a configured Nat. It retains
the exact `IxIR2.Pipeline.compileValidated` and selector equations. This input
passes the existing shared-result checker; a bare unique literal still fails
at `freezeNeeded`. The fixture pins the literal resolver, all compiler limits,
and lowering/pass-policy versions. It supplies no hand-written intermediate
IR and makes no claim to be an upstream Lean export.

Delivered cuts:

1. **Compiler graph:** two addressed declarations and a main tail call produce
   three blocks, three instructions, and three terminators. The worker releases
   its erased shared argument; the entry allocates and applies its PAP. Exact
   graph recognition extends selection without pruning or normalizing the
   compiler artifact. Both scalar families select `movabs rax, word; ret`.
2. **Physical baseline:** `lowerCheckedWithTrace` retains an executable
   instruction-inventory proof. `runMain_creditFree` transports successful
   baseline execution between interpretations with the exact same store,
   counters, and budgets; `Attached.successfulPhysicalMainSimulation` composes
   it with logical lowering. Certified extern closure remains in force.
3. **Actual selector result:** `Output.refinesSuccessfulRun` uses exact graph
   recognition and successful-result uniqueness across control/heap budgets.
   Any successful physical execution returns the actual selected word and
   agrees with typed local x86 execution, preserving arbitrary entry `rsp`.
4. **Source composition:** `sourceRefines` derives addressed erasure, owned
   addressed IxIR₁ execution, and physical baseline execution from the checked
   attachment. `sourceScalarRefines` proves equality of the selected word's
   `toNat` with the source Nat. Source sharing well-formedness, the configured
   oracle relation, and successful source evaluation remain explicit premises.
5. **Object/native evidence:** each source fixture executes Ixon, raw and
   addressed IxIR₀, owned IxIR₁, both IxIR₂ interpretations, and typed x86.
   Emission uses the actual addressed IxIR₁ `graphRoot` in `ixir1Policy`
   provenance with versions 1/1. Two fresh compiler processes produce identical
   bytes and pinned address roots for zero, 42, and `2^64 - 1`. Independent
   decoding, linking, and native execution agree; `2^64` is rejected before
   writing an object. Runtime coverage also includes `2^32`.

The [optimizer harness](optimizer-harness.md#validated-source-to-native-scalar-check)
records the commands, exact graph, configuration, and counters. The
[simulation strategy](simulation-strategy.md#baseline-physical-and-scalar-target-composition)
records the theorem interfaces. Eleven added axiom fences retain the existing
trust basis. The local ISA, E0 encoder, and ELF writer remain ledgered
specification assumptions.

This completes the scalar integration exit. The native FIP exit additionally
needs heap operations, reset/reuse selection, native memory observations, and
the corresponding resource theorems.

## C1 — source coverage and reproducibility (delivered)

The [source coverage gate](source-coverage.md) records 11 synthetic Ixon
cases and two production rejection cases, alongside the existing 280-case
generated IxIR₀ corpus. Accepted sources exercise direct calls, constructor
and Nat dispatch, and PAP/application paths through baseline IxIR₂. Zero,
42, and the largest 64-bit Nat also reach native execution.

The original 54-constant Std contact keeps its exact `freezeNeeded` boundary.
Its closed 17-constant failing dependency slice preserves that rejection;
removing any non-root member breaks closure. The isolated root instead
rejects with `typeBinderRuntimeUse .linear`, so deleting its dependencies
would not be a valid minimization of the same failure.

The Lean checker runs two fresh compiler processes and compares every output
file byte for byte: canonical source/IR graphs, all recorded provenance maps,
HPT candidate and certificate/cache records, finite IxIR₂ sidecars, stage
observations, and ELF objects. A reviewed matrix pins roots, HPT identities,
exact rejection codes, and memory counters. IxIR₂ JSON remains a diagnostic;
it is not an independently addressed codec or persistent cache format.

All repository check scripts are Lean executables. The trust, encoder,
object, and coverage checks retain their external tool comparisons, and
the trust auditor has isolated regression tests for rejection paths.

## D1 — source recursion recovery, first schema delivered

[`Recursion.compileValidated`](../Compilatrix/Recursion/Pipeline.lean) runs
the original validated source compiler, checks recovery against its exact
raw erasure, and derives an accumulator-before-major recursor. Ordinary
ownership lowering, complete IxIR₁ addressing, checked CFG lowering, and
reuse selection consume the generated program. The original validated
artifact remains available after every optional failure.

The first schema recognizes a known eager `below` fold over one non-mutual,
non-nested list inductive with an immediate recursive tail. Its entry grammar
is a closed Nat list, optionally retaining the input in a returned pair.
The checker verifies complete rules, minor definitions, projections, and
entry uses; the proposed replacement body is fixed by the proved schema.
The generic evaluator theorem covers arbitrary list elements and accumulators.
`Compilation.sourceRefines` composes validated Ixon evaluation to the exact
selected IxIR₀ program, including literal fallback, with the existing source
sharing/oracle premises.

The [focused D1 record](source-recursion.md) includes eight synthetic Ixon
cases, initially 22 rejection/fallback checks, and complete artifact comparisons from
two fresh compiler processes. All stages agree and all observed heaps reclaim.
For three unaliased cons cells, literal IxIR₁ allocates 29 nodes, recovered
baseline execution allocates eight, and physical reuse allocates five with
three hot resets. Retaining the original list forces three cold resets,
zero reuses, and nine recovered allocations. Five axiom fences retain the
existing trust basis.

This closes the first schema's source-recovery and executable reuse exit.
General `brecOn`, open source entries, mutual/nested recursion, well-founded
erasure, static unique recursor modes, and upstream Lean/Std exports remain
outside the recognizer. D2 supplies the composed source-to-physical theorem.

## D2 — recovered source execution through physical reuse, delivered

[`Compilation.sourceRefinesSelected`](../Compilatrix/Recursion/PhysicalSim.lean)
starts with successful Ixon evaluation and the existing source sharing/oracle
contracts. Its `SelectedExecution` conclusion executes the exact selected
physical IxIR₂ for recovered outcomes, including checked reuse fallback, or
the original owned addressed IxIR₁ artifact on literal fallback.

The new [common lowering record](../Compilatrix/LoweredCompilation.lean)
retains the exact IxIR₀ input, full lowering/addressing trace, first-binding
row checks, and closed extern certificate. Original source compilations
project it; recovered programs check it. Both feed the same HPT/sidecar/CFG
attachment. The source-facing `Attached` API remains available through
`.compiled`, with aliases for existing backend theorem names.

The recovered schema supplies projection-free call-aware traces.
`LoweredCompilation.addressedOwnedMain` reconstructs compiler contracts,
declaration correspondence, progress, and ownership from the retained trace.
The existing baseline interpretation and selected reuse theorems then produce
the physical run. No caller supplies intermediate execution or compiler facts.
Seven additional axiom fences retain the existing trust basis.

The eight D1 cases preserve their roots and hot/cold counters. Three added
negative cases reject source shadowing and source/target externs at the common
lowering boundary. Version-2 case snapshots add the actual HPT certificate and
canonical cache records, full finite sidecars, and common lowering input/checks;
the independent checker verifies their links and pinned HPT identities.

## R2 — terminal resources for selected reuse, delivered

[`IxIR2/HeapAccounting.lean`](../Compilatrix/IxIR2/HeapAccounting.lean) isolates
actual heap-operation and credit-transfer algebra.
[`IxIR2/Resources.lean`](../Compilatrix/IxIR2/Resources.lean) proves that physical
steps preserve `live + frees + presentCredits = allocs`, including credits in
continuations. Fresh execution establishes this invariant, and halt yields
`live + frees = allocs`: no outstanding reservation balance. This accounts for
the store's representation, in which freed and reserved slots both have absent
node entries.

[`IxIR2/ReuseResources.lean`](../Compilatrix/IxIR2/ReuseResources.lean) transports
successful shared release through the existing semantic heap relation.
[`IxIR2/PipelineResources.lean`](../Compilatrix/IxIR2/PipelineResources.lean)
derives the baseline release, positive reference counts, and allocation order
from the actual owned execution and common checked compiler record. It covers
optimized and checked baseline selection. Any successful selected execution,
with any sufficient fuel, can release its shared result to `live = 0` and
`allocs = frees`.

[`Compilation.sourceRefinesSelectedWithResources`](../Compilatrix/Recursion/Resources.lean)
composes these guarantees using exactly D2's source premises and value
relation. Literal fallback retains the original owned IxIR₁ execution and
reclamation. Allocation accounting applies to either ownership world;
selected reclamation and source composition cover shared main results.
Release receives its own sufficient fuel. Nine new fences retain the existing
axiom basis and native interface inventory.

The eight hot/cold source cases, 25 negative checks, identities, complete
artifact comparisons, and reviewed cost matrix remain unchanged. The producer
and independent fresh-process checker now check terminal allocation balance
before checking the fully reclaimed heap. These resource proofs do not claim
universal savings relative to the baseline.

## R3 — comparative allocation and free laws, delivered

[`AllocationEvents.lean`](../Compilatrix/IxIR2/AllocationEvents.lean) counts
`allocs + reuses` independently of semantic heap correspondence. Actual fresh
allocation and reuse each add one; all other heap operations preserve the
total. Related unchanged steps have equal increments, including dynamic PAP
application and returns through `applyMore`. Accepted hot and cold macros
each contribute one event on both sides. Their `AllocationDelta` certificates
compose through the existing compiler synchronization proof.

[`ReuseAllocation.lean`](../Compilatrix/IxIR2/ReuseAllocation.lean) derives
equal live-node counts from allocation history and combines them with R2's
terminal balances. [`PipelineAllocation.lean`](../Compilatrix/IxIR2/PipelineAllocation.lean)
derives zero baseline reuse from the actual owned execution and checked
lowering trace. For compiled shared mains, it proves
`baseline.allocs = selected.allocs + selected.reuses` and
`baseline.frees = selected.frees + selected.reuses` at physical halt. The
free law also holds after both actual shared releases complete at the same
sufficient traversal budget. Optimized and checked baseline selection are
covered, including any independent sufficient execution fuel.

[`Compilation.sourceRefinesSelectedWithAllocationLaws`](../Compilatrix/Recursion/Allocation.lean)
uses exactly D2/R2's source premises and value relation. Its recovered branch
compares the selected result with an actual physical run of that recovered
program's checked ownership/CFG baseline. Literal fallback retains R2's
original owned IxIR₁ execution and reclamation. No extra rewrite-shape, heap,
compiler-state, or comparative-cost premise narrows the shared-main domain.
The counter invariant remains separate from `PhysicalValueRel`,
`StableHeapRel`, and the semantic machine relation. Existing semantic and
resource theorem interfaces remain available.

Twelve new fences retain the existing axiom basis. The hot/cold, discard,
recursive-return, and checked-fallback regressions remain in the complete
build. The producer and independent fresh-process checker check the direct
physical baseline/selected laws at halt and after reclamation. The report,
programs, counters, and complete snapshots remain byte-identical to R2.
General credit refinement, static unique reuse, and native heap/runtime
selection remain separate extensions. R5 below extends credit lifetimes
across non-tail direct calls.

## R4 — RC and peak-live bounds, delivered

`Compilation.sourceRefinesSelectedWithCostLaws` in
[`Recursion/Costs.lean`](../Compilatrix/Recursion/Costs.lean) proves
`selected.rcops ≤ baseline.rcops` and
`selected.peakLiveNodes ≤ baseline.peakLiveNodes` for actual checked shared-main
baseline and selected physical executions. It preserves R3's allocation/free
laws, the exact physical value relation, and both results' shared resources.
`ReclaimedCostLaws` carries both actual complete releases at the same sufficient
budget, empty balanced heaps, the free equation, and RC/peak bounds after release.
Literal fallback retains R3's original owned IxIR₁ endpoint.

The source theorem uses exactly the existing successful Ixon evaluation,
sharing, and oracle premises. It covers all accepted recovered shared-main
records and both optimizer selection branches, with no additional heap,
compiler-state, cost, or rewrite-shape premise. At the backend,
`successfulPhysicalCostLaws` permits independent sufficient control and heap
budgets for the actual baseline and selected runs. The comparison remains with
the recovered program's checked physical baseline; literal-to-recovered savings
are still separate measurements.

[`RcPotential.lean`](../Compilatrix/IxIR1/RcPotential.lean) extracts the existing
shared RC algebra from `IxIR1/CostTrace.lean`, preserving its public names and
old proofs. [`CostObservations.lean`](../Compilatrix/IxIR2/CostObservations.lean)
proves actual heap-operation charges and peak updates. Deep release conserves
executed RC operations plus pending shared references; a retain adds two units
per heap reference. Heap correspondence preserves pending references, allowing
ordinary matched steps to compare raw RC increments. Hot reset performs no RC
work, while cold reset retains the same fields and decrements the same owner
as the baseline. `CostDelta` composes these facts separately from semantic
heap and value relations.

[`CostSteps.lean`](../Compilatrix/IxIR2/CostSteps.lean) proves that every successful
step records every allocation peak, including heap work inside partial and
residual application. RC counts and recorded peaks never decrease.
`PrefixCostBounds` covers every actual selected prefix, including reset, branch,
and allocation states inside synchronization macros: its RC count, peak, and
live-node count are bounded by the actual baseline's terminal counters.
The compiler establishes the cost invariant internally and the original
semantic, resource, and allocation theorem interfaces remain available.

Seventeen new fences retain the existing axiom basis. The source producer and
independent checker verify both physical cost inequalities at halt and after
release. Four new corruption regressions preserve all earlier allocation/free
laws and are rejected at the new RC/peak checks. The complete report and eight
snapshots remain byte-identical to R3, including the existing counter matrix.

## R5 — credits across non-tail calls, delivered

`CreditPolicy.suspendedCallsV1` adds explicit validation and execution under
`suspended-direct-calls/1`. Direct `call` and `callSelf` suspend the caller's
entire credit file in its return continuation; the callee starts empty, and
return restores the caller unchanged. Required and optional credits must then
be consumed, discarded, or transferred once per edge. The original v0 APIs
retain their call rejection, with exact runner compatibility proved.

`ReservationOwnership` proves unique ownership and empty-slot exclusion for
every present physical reservation across active and suspended frames.
All physical steps preserve it, and actual main prefixes derive it internally.
Allocation accounting includes suspended reservations. The new
`shared-call-reuse/1` pass checks the exact consuming field prefix, nonempty
direct-call sequence, last use, and layout before replacing the prefix and
allocation with reset/reuse. It validates its target and retains a checked
v0 baseline on unsupported input or target rejection.

The finite compiler simulation reconstructs accepted prefixes and continuation
history from actual baseline execution. It covers nested calls and ordinary
PAP/residual dispatch, preserves the existing heap/value relation, and carries
separate allocation-event and RC/peak evidence. `PipelineCallReuse.lean`
derives initial heap ownership from actual compiler output and proves R3/R4's
terminal and reclaimed allocation/free/RC/peak laws, including every selected
prefix and independent sufficient budgets. Both inner selection branches are
covered without additional caller-supplied heap, shape, or cost premises.

`CallReuse.compileMap` supplies the source witness. It checks the literal
erasure of a valid generic Ixon list recursor and its base/step/constant worker,
then specializes it to a direct map under `closed-map-specialize/1`.
The source checker and simulation cover arbitrary finite closed Nat lists,
replacement values, and an optional retained suffix. Ordinary ownership
lowering, rebuilding, HPT production, and the common checked backend produce
the final program. `MapCompilation.sourceRefinesWithCostLaws` composes actual
selected execution, full reclamation, and comparative costs from only the
original source sharing/oracle/success premises. Optional source/backend
failure retains literal owned IxIR₁ execution and reclamation.

The [source-map record](source-call-reuse.md) gives the exact domain and all
interfaces. Nine source cases compare every stage, reclaim every result, and
check actual reservation prefixes. Three unaliased cons cells reduce physical
allocations from 11 to 8 and RC operations from 13 to 4, with peak 4 unchanged.
A five-element retained-suffix case performs two hot and three cold resets
in one run. Thirty-five policy/rejection checks include nested reservations,
discards, prohibited boundaries, source mutations, and executable fallbacks.
The independent checker compares complete artifacts from two fresh processes
and rejects seven deliberate policy/reservation/cost corruptions.

Canonical IxIR₁-plus-policy provenance includes the source and graph roots,
HPT roots, lowering depth/version, pass, execution policy, selection outcome,
and specialization policy/address. Diagnostic IxIR₂ JSON is not used as a
content address. Twenty-five new axiom fences retain the existing trust basis.
Static unique reuse is delivered below. General credit refinement and native
heap selection remain separate extensions.

## Static unique reuse — delivered

`UniqueReuse.compile` checks an explicit closed Ixon entry under the opt-in
`recursor-modes/1` policy. Saturated rule checking retains binder types and
tracks every unique move and result; source work limits include the standalone
entry. `ModeEvidence` connects source telescopes to canonical recursor-instance
world vectors. The recognizer checks the entire erased list-reversal schema,
including its builder and declarations, before specializing the known builder.
The source proof covers all finite closed Nat lists accepted by this schema.

The exact generated IxIR₁ function extracts both cons fields, shallow-frees
their parent, allocates the new accumulator cell, and tail-recurses. The
independently validated `UniqueLower.Translation` is indexed by that artifact.
It translates consuming operations into `takeUnique` and `discardCredit`;
static selection checks liveness and layout before replacing the cons credit
discard/allocation pair with `allocWith`. The nil branch discards its credit,
and each tail boundary has no remaining credit. Execution uses `call-local/0`.
Source/usage rejection stays an error, optional reuse failure keeps the exact
checked target baseline, and target-validation failure keeps consuming IxIR₁.

`Compilation.sourceRefinesWithCostLaws` derives the complete actual execution
and owned result from only the established source oracle, sharing, and success
premises. It supplies full release and comparative target costs without a
caller-provided heap, liveness, shape, ownership, or counter premise.
`Translation.forwardSimulation` additionally covers every successful execution
of the indexed IxIR₁ input, with independent target budgets and both
interpretations. Separate heap, step, loop, entry, resource, and pipeline
modules keep the new proofs out of the large shared-reuse simulation modules.

For `n` cons cells the physical selected target uses `n + 2` allocations,
`n` reuses, one free, zero RC, and peak `n + 2`. Its physical baseline uses
`2n + 2` allocations and `n + 1` frees, with the same RC and peak.
All physical prefixes have distinct reservations in empty slots and satisfy
`live + frees + reservations = allocs`. Main execution accepts zero heap fuel;
full result release uses `2n + 1`, empties the heap, and balances allocations
with frees. Reclamation uses a finite owned list view and supports the forward
links created by in-place reversal.

The [source unique record](source-unique-reuse.md) gives the full domain and
public interfaces. Seven source cases cover empty, singleton, repeated and
large Nat values, 64 elements, and checked disabled/budget fallbacks.
Forty-three source, identity, validation, fallback, and budget checks exercise
the excluded boundaries. The independent checker reconstructs canonical
source, recursor-mode, IxIR₁, and policy preimages; verifies full constructor
identities and unit unique ownership in returned heaps; checks every physical
reservation prefix; and compares complete artifacts from two fresh processes.
Twelve corruptions exercise identity, ownership, reservation, and cost checks.
Twenty-four new theorem fences preserve the existing trust basis.

## Native heap selection — next

Select the actual validated unique-reversal artifact into a bounded typed
machine heap/runtime ABI. Prove the selected operations preserve the existing
source result, ownership, reservation, and resource observations, then emit,
link, and run a source-produced native witness with complete reclamation and
allocation/reuse evidence. Keep scalar selection and all source artifact and
trust gates. General credit refinement, broader source unique compilation,
borrow inference, and independent IxIR₂ persistence are separate extensions.

## Artifact and proof-maintenance gates

IxIR₂ has no canonical codec or content address yet. The first source-driven
native object may use the implemented IxIR₁-plus-policy provenance form.
Strict IxIR₂ encoding/decoding, canonicality, and exact dependency/schema/
policy preimages are required before persisting or caching independently
addressed IxIR₂ artifacts, advertising an `IxIR2/v0` wire identity, or relying
on that identity for self-hosted reproducibility. Block order is part of the
initial contract; renumbering is a separate pass. Do not hash an ad hoc
`repr` or treat an inherited IxIR₁ declaration key as its rewritten body hash.

After R1 stabilizes, separate reusable live-heap algebra, compiler history,
accepted-site composition, and the public pipeline wrappers behind narrow
module interfaces. Preserve public theorem names through imports where
practical and keep their axiom sets unchanged. Profile the affected modules
before targeting elaboration time. This is a bounded maintenance cut attached
to the next proof extension, not an independent rewrite of the proof library.

## Verification for this review

The reviewed gates can be run locally with:

```sh
lake build Compilatrix tests catalog-contact x86-object-fixture \
  source-coverage source-recursion source-call-reuse source-unique-reuse \
  check-trusted-externs check-x86-encoder check-x86-object \
  check-source-coverage check-source-recursion check-source-call-reuse \
  check-source-unique-reuse check-tools-tests
./.lake/build/bin/tests
lake exe check-trusted-externs --root .
lake exe check-tools-tests --root .
lake exe check-x86-encoder --objdump objdump
lake exe check-x86-object \
  --fixture .lake/build/bin/x86-object-fixture \
  --readelf readelf --objdump objdump --cc cc \
  --harness fixtures/x86/native_harness.c
lake exe check-source-coverage \
  --fixture .lake/build/bin/source-coverage \
  --cc cc --harness fixtures/x86/native_harness.c
lake exe check-source-recursion --fixture .lake/build/bin/source-recursion
lake exe check-source-call-reuse --fixture .lake/build/bin/source-call-reuse
lake exe check-source-unique-reuse --fixture .lake/build/bin/source-unique-reuse
```

The checks cover 13 encoder forms, seven object fixtures, C1's 13-case source
matrix, the eight source-recursion cases and 25 rejection/fallback checks,
the nine source maps and 35 policy/rejection checks, the seven unique-list
cases and 43 boundary checks, complete artifact comparisons, and the trust
auditor's rejection regressions.
Every observed D1 heap reclaims fully. The native objects retain their address/provenance goldens,
scalar boundaries, independent disassembly, and native result agreement.
N1's eleven axiom fences still cover interpretation transport,
budget-independent results, actual selection, and source composition.
D1 adds five fences for the eager fold, generic recursor simulation, checked
entry, selected fallback, and source composition. D2 adds seven for common
lowering contracts and owned execution, recovered trace completeness, the
common physical bridge, and recovered/literal/selected source execution.
R2 adds nine for machine allocation accounting, heap-release transport,
common/selected reclamation, arbitrary successful selected fuel, and source
resource composition.
R3 adds twelve for actual allocation events, macro deltas, live-node counts,
terminal/reclaimed counter laws, both selection branches, independent
sufficient fuel, and source allocation composition.
R4 adds seventeen for RC potential, exact step peaks, arbitrary selected
prefixes, hot/cold cost deltas, both selection branches, complete reclamation,
independent sufficient fuel, and source cost composition.
R5 adds twenty-five for v0 compatibility, suspended reservation ownership,
resource/prefix laws, actual selected compiler simulation, owned baseline
heaps, checked source-map specialization, and source/resource/cost composition.
Static unique reuse adds twenty-four for mode identity, checked specialization,
consuming source/target execution, ownership, complete release, exact costs,
all physical prefixes, checked fallbacks, and the public source endpoint.
These extensions and the Lean script migration add no trusted axioms or native interfaces;
the ledger retains two native interfaces and three specification assumptions.
The changed scripts, build inputs, and source matrices have reviewed pins.
The complete local static-unique build passed 524 jobs and the runtime suite reported
`tests-ok`. The final auditor regressions additionally cover quoted CI pins
and proof holes adjacent to Unicode syntax. Deliberately altering a reviewed
D1 allocation count produced the expected matrix-drift rejection. D2's
independent checker also rejects deliberately corrupted lowering input,
lowering certificate checks, and sidecar HPT certificate links, even when both
fresh processes produce the same corrupted snapshot.
R2 adds deliberate corruption of a terminal physical free count and a literal
live-node array; the independent checker rejects both through its new terminal
balance check, even with identical corruption in both fresh outputs.
R3 additionally rejects four corruptions that preserve each individual heap's
allocation balance: matched allocation/free offsets at halt and after release,
a terminal free offset paired with removal of a live node, and a nonzero
baseline reuse count. Both fresh outputs receive identical corruption.
R4 adds four RC/peak corruptions, separately at halt and after release, that
preserve every earlier per-heap balance and comparative allocation/free law.
The independent checker rejects each through its corresponding new bound.
The report and all eight complete source-recursion snapshots are byte-identical
to R3 (and R2/D2), so the added checks leave the reviewed artifacts and counter
observations unchanged.
R5 adds seven independent corruption regressions for terminal/reclaimed RC and
peak counters, execution policy, duplicate reservations, and live-slot aliasing.
The previous source-recursion report and all eight complete snapshots remain
unchanged. All 130 pre-existing public attachment names remain available
through their aliases.
Static unique reuse adds twelve independent corruption regressions covering
terminal/reclaimed RC and peak counts, mode/policy/graph identity, constructor
identity and ownership, duplicate owners, and live-slot reservations.

A fresh `nix flake check` passed all eleven final static-unique checks on
`x86_64-linux`, including workflow linting, the Nix-evaluated dependency/version
audit and its rejection regressions, all four source artifact comparisons,
canonical source/mode/graph/policy preimage checks, the twelve new corruption
regressions, runtime tests, and native execution. The runtime build completed
469 jobs and reported `tests-ok`. It used an isolated source copy containing
all new files without staging the working tree. The previous source reports
and their reviewed integrity pins are unchanged. The other three configured
host systems were outside this local run. Existing Lean linter warnings remain.

CI runs the same complete flake gate. Local ignored `plans/` edits do not
become tracked release documentation; contributor decisions are recorded
here and in the roadmap.
