# IxIR₁ optimizer harness

Status: the default O1 bundle was attached to the validated compilation
semantics on 2026-08-31. The checked HPT consumers propagate facts through complete
stored function bodies, prune impossible alternatives, collapse a certified
detailed unary case to one checked `fetch`, forward certified scalar fields
after allocation or successful reuse, specialize certified destructor sites,
and fuse adjacent PAP/application pairs. Rooted reachability then filters the
rewritten old-keyed graph before all five consumers share one content-address
rebuild.

The harness implementation is `Compilatrix/IxIR1/Optimizer.lean`; release
transport is in `Compilatrix/IxIR1/OptimizerReclamation.lean`; and the
validated artifact projection is in `Compilatrix/PipelineSound.lean`.
Compiler-facing entry points remain
`Pipeline.Artifact.optimizeWithProducedHPT` and `optimizeWithCachedHPT`.

## Policy and fallback

`Optimizer.Policy` carries harness version 5, case-simplifier version 3,
fetch-forwarding version 1, destruction version 1, PAP-fusion version 1, and
reachability version 1. The five passes have independent enable bits and are
enabled by default.
Reachability additionally carries an ordered list of exported declaration
roots. The shared deterministic bounds cover input instructions, canonical
code bytes, and checked-certificate bytes. The harness is disabled only when
all five pass bits are false.

Fetch forwarding recognizes an `alloc` or `reuse` immediately followed by a
fetch of any field from its result. The selected constructor argument must be
HPT-proven scalar. The pass retains both binders and replaces the fetch with
`pure` of the source atom lifted across the constructor-result binder, so fuel,
stores, numeric locations, and cost counters are preserved exactly. Heap-valued
and out-of-range fields fail closed.

Destruction removes a `drop` or `dropU` of an HPT-proven scalar by replacing
it with `pure erased`. It also replaces `dropU` with shallow `free` when HPT
proves one exact constructor with a complete all-scalar field vector. The
rewrite preserves the result binder and the root free, while avoiding generic
tag dispatch and the recursive field walk. Shared constructor roots,
heap-valued fields, identity-only facts, multiple shapes, widened facts, and
unresolved operands stay on the generic path. The successful-run theorem is
one-way because the specialized shallow free can succeed with less fuel than
the generic deep destructor.

PAP fusion recognizes adjacent `papp`/`apply` binders and classifies their
combined arguments as under-, exactly-, or over-saturated. It retains both
binder slots, lowers supplied operands across the retired PAP slot, and rejects
the rewrite unless the continuation cannot mention that slot. Captures must be
HPT-proven scalar: IxIR₁ no longer carries function-parameter ownership modes,
so the local checker cannot soundly classify an arbitrary heap capture as
shared.

Reachability hashes the exact ordered rewritten declaration rows, exact main,
and exact configured roots into a checked certificate. Its retained list must
be in input-key order, contain every exported root, and be closed under every
direct `call` and `papp` edge in main and retained declarations. `callSelf`
remains within its retained owner. Version 1 treats a reachable dynamic
`apply` as open-world and accepts only the complete declaration set; an
unreachable apply does not pin an otherwise dead component. A producer/checker
disagreement or nonexistent configured root retains the complete input graph.

Every inferred-optimization failure is fail-soft. An unsupported version,
disabled pass, exhausted optimizer budget, or rejected content-address rebuild
returns the original graph and records a typed skip reason. These conditions
cannot reject an otherwise accepted compiler artifact. HPT production and
checking retain their own separately versioned structural limits.

## Validated semantic attachment

`Optimizer.Outcome.RunRefines` exposes the selected execution relation for
both the literal skip branch and a successful content-address rebuild.
Direct-production and persistent-cache wrappers turn one successful source
run into a selected target run. They also preserve full-result reclamation:
evaluator determinism identifies every successful selected run with the
forwarded witness, heap-history isomorphism transports shared or unique deep
release, and the checked rebuild transports the released heap through its
final address map.

`ValidatedCompilation` instantiates that authority for the artifact returned
by `optimizeWithProducedHPT`. Its public endpoints state forward simulation,
target progress, all-fuel memory-error exclusion, and reclamation directly on
the selected artifact's declaration environment and main, not merely on an
internal optimizer outcome. The persistent-cache path has the same generic
successful-run and reclamation theorems and does not duplicate the pipeline
projection.

The selected artifact also exposes `frees ≤ allocs`, the evaluator's general
fresh-store balance. Heap-history refinement intentionally omits counters, and
successful PAP fusion or destruction may change allocations or frees, so the
pre-optimization no-reuse and ownership-amortized four-counter contracts are
not claimed through this interface without a separate syntactic or cost
preservation proof.

## Observations

One `Observation` scans all stored function bodies plus the main and reports:

- artifact, mutual-block, function, and extern counts;
- `ret`, `letOp`, `case`, and alternative counts;
- alloc, reuse, free, RC increment/decrement, unique-drop, and fetch counts;
- direct call, self call, PAP allocation, dynamic apply, and extern-call
  counts;
- canonical code bytes; and
- stored ordinary/mutual artifact bytes.

`instructions` counts each `ret`, `letOp`, and `case` node once. These are
static compiler observations. Dynamic allocation, reclamation, RC, and live
heap counters remain in the IxIR₁ evaluator/cost model. Machine-dependent
wall time is deliberately absent from addressed reports.

## Identities and reports

The input and output graph roots use
`compilatrix/ixir1/optimizer-graph/1\0`. The preimage commits to artifact kind
and order, stable ABI address and declaration payload, ordinary declaration
address and payload, symbolic mutual-block payload, and exact main bytes.

Checked HPT certificate identity is the digest of its canonical cache-store
spelling; its exact framed byte count is reported separately. A pass report
contains the complete policy, typed disposition, input/output/certificate
roots, certificate size, before/after observations, case-pruning counters,
total forwarded fetches, scalar drops elided, unique leaf drops specialized,
total fused PAPs, under/exact/over fusion counters, removed declarations, and
a rebuild diagnostic only on fallback. Report schema 6 uses
`compilatrix/ixir1/optimizer-report/6\0`; pass behavior is
versioned separately inside the encoded policy.

This makes equality of reports executable byte equality rather than equality
of human-formatted text.

## Regression boundary

The compiled tests pin nine properties:

1. two independent runs over the same checked input produce identical output
   roots, report bytes, and report addresses;
2. a non-degenerate whole-program case rewrite removes one impossible
   alternative through an intervening alias binding, eliminates the remaining
   unary case, materializes one checked fetch, shrinks canonical code bytes,
   readdresses the changed caller, rewrites the main edge, and preserves
   pipeline producer-to-target provenance;
3. disabled and one-below instruction-budget policies select the exact input
   root;
4. after HPT is recomputed on the transformed root, the default shrinking pass
   reports `unchanged` and reproduces that root;
5. the default PAP pass fuses under-, exact-, and over-saturation in one graph,
   reports each class, rejects non-scalar captures and binder-sensitive shapes,
   preserves the scalar result with an empty live heap, and reaches a fixed
   point after HPT recomputation;
6. the default fetch pass forwards one allocation projection and one successful
   reuse projection, checks the lifted variable form, rejects heap-valued and
   out-of-range sources, preserves the exact result and all heap counters, and
   reaches a fixed point after HPT recomputation;
7. the destruction pass elides one scalar drop and specializes one exact
   all-scalar unique leaf, replaces the generic deep drop with shallow free,
   preserves the exact scalar result and allocation/free/live observations,
   rejects every conservative fact boundary, and reaches an unchanged second
   run, while an unsupported destruction version selects the input graph;
8. a direct-call closure removes a dead two-function SCC, a PAP root retains
   its target, and an explicit exported root retains the whole SCC; and
9. stale input identity, substituted roots, and a canonical but non-closed
   retained set fail closed, while reachable dynamic apply retains the whole
   graph and both the filtered and rebuilt programs return the same result.

The production Ixon→IxIR₁ integration fixtures separately exercise default
report generation and the disable path on compiler-emitted code. A
constructor-only main also emits six stored functions, five of which have no
runtime path from main; the default pass reports and removes those five while
preserving the exact constructor result. Default-pass semantic authority comes
from the checked whole-program history-refinement and
exact readdressing theorems documented in
[HPT certificates](hpt-certificates.md). `fusePair?_refines` proves each local
PAP decision; `FetchForward.runCode_forwardHead?_eq` proves literal evaluator
equality for each accepted fetch decision;
`Destroy.runOp_specialize?_success` proves arbitrary-fuel successful-run
refinement for each accepted destructor decision; and
`runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle` lifts the composed
decisions through main, stored declarations, recursive self calls, direct
calls, PAP application, and the final one-rebuild path.

## Staged extension boundary

The scalar and exact-leaf cases are the complete destruction slice for the
current IxIR₁ instruction set. Recursive expansion is not merely a code-size
question: inline `fetch`/`free` expansion reduces the fuel available to the
continuation, while moving that expansion into a content-addressed helper adds
call/invoke fuel at the generic destructor's minimum successful boundary.
`HPTDestroy.recursiveExpansionFuelBoundary` executes both counterexamples.
A shared-root specialization additionally needs an explicit RC-zero branch,
which IxIR₁ does not expose as code.

Recursive unique destruction and the known-shape shared zero branch therefore
resume with the fuel-neutral consuming-destructure/reset operation in the
IxIR₂ final-RC path (or an equivalently primitive operation with the same
semantic contract). That contract is now frozen in the
[IxIR₂ v0 specification](ixir2-spec.md): consuming/reset is one CFG transition,
credits are affine and exact-layout, and the shared decision is an explicit
optional-credit branch. Exact-case collapse beyond the checked unary form
remains the next extension that fits the current IxIR₁ contract.

## IxIR₂ dynamic-reuse checkpoint

The first compiler-emitted reuse benchmark now lives in
`Compilatrix/IxIR2/ReuseExamples.lean`. A hand-written IxIR₀ shared list
recursor is compiled through the ordinary IxIR₁ compiler and baseline IxIR₂
CFG lowerer. The new `IxIR2.Reuse.optimize` endpoint validates that baseline,
rewrites only its exact current accumulator-loop shape to
`resetShared`/`branchCredit`/`allocWith`, and validates the result again.

For three input cons cells, the unaliased physical run performs three hot
resets and three reuses, allocates only the five input/accumulator nodes, and
reports six reused payload units. Retaining the original list forces three
cold resets, zero reuses, and the same nine allocations as the baseline. The
source, baseline, logical rewrite, and physical rewrite return the same list
observations, and each target result deep-releases to an empty heap. Regression
checks also pin exact compiler-shape provenance, the emitted optional-credit
diamond, fixed-point behavior, and fail-closed layout incompatibility.

D1 now reproduces these counters from canonical synthetic Ixon through
[`Recursion.compileValidated`](../Compilatrix/Recursion/Pipeline.lean).
The [source-recursion gate](source-recursion.md) checks eight inputs and
25 rejection/fallback cases and compares complete artifacts across fresh
compiler processes. It measures the literal tuple-fold overhead as well:
three unaliased cons cells allocate 29 nodes in literal IxIR₁, eight after
checked recovery, and five with physical reuse. D2's composed source theorem
reaches the actual selected physical IxIR₂ after recovery and preserves
the original owned IxIR₁ on outer fallback. R2 separately proves terminal
allocation balance and complete shared-result reclamation for the actual
selection; it retains D2's semantic relation and source premises. R3 proves
the recovered baseline/selected allocation and free equations for the shared
compiler domain, both at halt and after release. R4 bounds selected RC operations
and peak live nodes by the actual physical baseline, including every selected
prefix and complete result release. Exact counters and the separate
literal-to-recovered savings remain finite observations.

A separate IxIR₁-sourced fixture covers an empty constructor prologue followed
by reuse of a different inherited node. It checks the compiler's zero-PC child
trace and selected reset block, compares physical baseline, logical rewrite,
and physical rewrite observations, and fully releases every result. The hot
case records one reuse and three allocations; retaining an alias forces one
cold reset, zero reuses, and five allocations. This exercises the empty-prologue
arm of the constructor-child composition boundary alongside the reversal's
nonempty prologues.

A further regression adds handwritten IxIR₁ PAP adapters around that
IxIR₀-derived reversal. Exact application and nested over-application both
reach an addressed tail call before the recursive self tail calls. Each route
runs with and without an alias, compares logical and physical baselines with
both rewrites, and fully releases every result. Exact application adds one PAP
allocation/free and three RC operations; the two over-applications add three
PAP allocations/frees and five RC operations in total.

This checkpoint is intentionally not folded into the IxIR₁ optimizer's
addressed report format yet. It uses the theorem-facing transient IxIR₁
compiler result, and its semantic comparison is a bounded proof-carrying
benchmark check rather than the general rewrite simulation required for the
production O2 pass.

The next proof now has a stable evaluator boundary: public reduction lemmas
cover both reset decisions, fresh and reused credit allocation, credit discard,
unique extraction, both optional-credit branches, arbitrary credit-carrying
CFG edge transfer, and every call boundary with a fully consumed credit file.
Exhaustive public instruction, terminator, and whole-step classifiers feed
trace-aware lockstep dispatchers, including extern-targeted PAP construction;
the resulting one-step theorem closes every literally unchanged block under
both exact contents and an arbitrary allocation history. Relation-aware batch
credit consumption and edge transfer include physical reservation addresses.
A positive finite-macro relation and trace-driven block eliminator now select
that one-step arm or one complete accepted macro, and a uniform `StableHeapRel`
entry point hides whether the input heap relation is exact or isomorphic.
The checked lowering trace also pins inherited target parameters to their
exact producer capabilities; compiler state uses that audit to recover the
accepted source owner and derive continuation-stack avoidance at unit
refcount. Exact ownership now executes the complete field-retain batch, and
the audited allocation transition exposes the new-field roots plus all
surviving source and frame roots. Hot-prefix cancellation and inert-scalar
balancing turn those two presentations into the physical macro's padded root
partition. The physical-hot constructor consumes and extends an existing
live-location bijection and transports the non-aliasing continuation stack. A new
history-aware cold constructor preserves distinct locations after earlier hot
reuse, including the reset retain loop, corresponding fresh allocation, call
arguments, and stack. Deterministic prefix cancellation plus an
invariant-preserving macro relation now yield finite whole-machine simulation
and an exact rewritten `runMachine` budget. The trust fence pins those
interfaces. Exact ownership transport through an arbitrary live heap
isomorphism now preserves incoming multiplicities, root and edge worlds, PAP
sharing, and refcounts. Fixed-prefix preimage synthesis plus pointwise
permutation transport carries the padded hot-prefix accounting to the
rewritten heap, while entry-live planner support pulls mapped locations back
through the same root isomorphism. The physical-hot accounting wrapper
therefore derives rewritten ownership, both root partitions, and rewritten
mapped support from baseline producer facts. The compiler attachment now
adapts its allocation-history state to that interface, executes the complete
accepted baseline prefix with a compiler witness, and joins the compiler and
semantic recursive-call endpoints at their shared exact step count.

The physical compiler/reuse composition is now complete for this insertion
family. `IxIR1/EvalHistory.lean` joins successful source prefixes and suffixes;
`CompilerStackHistory` retains suspended callers through tail calls and repeated
over-application. `returnApplyMoreOfTarget` reconstructs erased, under-saturated,
exact, and over-saturated dispatch from the actual target transfer.
`attachedPhysicalCompilerAdvance` covers every successful baseline head, and
`OptimizedAttachment.physicalMainSimulation` applies the public runner to the
exact initial machines and validated optimizer output. Its callers supply a
successful physical baseline run, with no progress callback or source suffix.

`Reuse.selectWith` keeps source errors and converts target-validation failures
to checked baseline selections with typed skip reports. `selectAttachment` is
total on an already-checked compiler attachment; `selectedPhysicalMainSimulation`
covers both outcomes. A regression limits each function to the baseline's three
blocks: the proposed five-block rewrite is rejected, and baseline execution
still returns `[3, 2, 1]` and reclaims fully. Additional hand-written IxIR₁
fixtures exercise erased and under-saturated residual returns, with exact
allocation/free/RC counts of `3/3/3` and `5/2/4` before final reclamation.

The baseline logical-to-physical bridge is now available in
`IxIR2/PipelinePhysical.lean`. `IxIR2/PipelineResources.lean` now composes
allocation accounting and shared-result reclamation with the actual selected
execution. `IxIR2/PipelineAllocation.lean` adds comparative allocation/free
laws from the actual rewrite execution, including checked baseline fallback
and independent sufficient fuel. The source composition is in
`Recursion/Allocation.lean`. `IxIR2/PipelineCosts.lean` and `Recursion/Costs.lean`
add RC/peak bounds without changing the source premises or narrowing the shared
compiler domain. Intermediate macro states and both actual complete releases
are covered. Semantic heap relations still omit runtime counters; the
[source-recursion record](source-recursion.md) details the separate cost
invariants. The [roadmap](roadmap.md#r6-general-credit-refinement) defines the
next general credit-refinement boundary.

## Validated source-to-native scalar check

`X86.ValidatedScalar.compile` constructs a synthetic canonical Ixon constant
and calls `IxIR2.Pipeline.compileValidated` and the actual selector. Its erased
lambda application returns the configured Nat. The source is synthetic Ixon,
with an explicitly configured literal resolver; it is not an upstream Lean
export or a claim about the catalog literal codec. No optional IxIR₁ or IxIR₂
optimizer runs in this fixture.

The compiler emits two addressed function declarations and a main tail call:
the worker releases its erased shared argument and returns the literal; the
entry creates and applies the worker PAP. Across three blocks there are three
instructions and three terminators. Selection recognizes the complete graph
without pruning or normalizing the artifact, then emits `movabs rax, word; ret`.
The owned IxIR₁ run and both IxIR₂ interpretations report one allocation, one
free, one RC operation, no reuse, and no live nodes. IxIR₂ takes six control
steps and two heap-work units, with peak live nodes equal to one and all reset
counters zero.
These are fixture observations, not a native heap or FIP theorem.

Generate the source-driven object with:

```sh
lake exe x86-object-fixture validated-scalar /tmp/scalar.o 42
```

The optional Nat defaults to 42. The ELF `ixir1Policy` note contains the actual
`IxIR1.Optimizer.graphRoot` of the addressed compiler output, with lowering and
pass-policy versions both 1. `ValidatedScalar.config` pins all compiler limits,
the absent Nat block, and the literal resolver. Its literal key hashes the
UTF-8 domain `compilatrix/native-scalar-literal/1`, a NUL byte, and the canonical
IxIR Nat encoding. The executable reports both the canonical Ixon root and
the addressed IxIR₁ root.

```sh
lake exe check-x86-object \
  --fixture .lake/build/bin/x86-object-fixture \
  --readelf readelf --objdump objdump --cc cc \
  --harness fixtures/x86/native_harness.c
```

This checks seven fixtures: the earlier four and validated source scalars
zero, 42, and `2^64 - 1`. Each is generated in two fresh processes; the source
cases perform independent complete compilations. It compares exact object
bytes, frozen source/IR₁ address goldens, exact provenance descriptors, local
observations, independent disassembly, and native results. `2^64` must reach
`unsupportedScalarShape` and leave no object. Runtime tests additionally cover
`2^32` and preserve the bare literal's exact source `freezeNeeded` rejection;
a valid graph with a changed entry must fail exact selector recognition.

The source-to-typed-target theorem is `X86.Select.sourceScalarRefines`.
The local ISA, encoder, and object writer retain their existing ledger entries.
The delivered [source-coverage gate](source-coverage.md) also compares complete
addressed graphs, maps, and certificate/cache records across fresh compiler
processes. Its 13 Ixon cases include direct calls, constructor/Nat dispatch,
PAP/application, the native scalar family, and exact negative boundaries.
The separate [source-recursion gate](source-recursion.md#reproducibility-gate)
adds eight source list-fold cases and complete literal/recovered artifacts,
including terminal and reclaimed heaps. It emits no native object.

## Source maps with suspended call credits

The [R5 gate](source-call-reuse.md#reproducibility-gate) adds nine valid Ixon
maps whose checked closed-source specialization feeds ordinary ownership
lowering. The `shared-call-reuse/1` pass emits reset/reuse around direct worker
and recursive calls under `suspended-direct-calls/1`. Three unaliased cons cells
reduce physical allocations from 11 to 8 and RC operations from 13 to 4 at
unchanged peak 4. A retained suffix gives two hot and three cold resets in one
execution. All values agree across stages and every returned heap reclaims.

```sh
lake build source-call-reuse check-source-call-reuse
lake exe check-source-call-reuse --fixture .lake/build/bin/source-call-reuse
```

The independent Lean checker compares every byte of two fresh artifact sets
and the reviewed report. It checks actual prefix reservations for unique
ownership and empty-slot exclusion, allocation accounting, and RC/peak/live
bounds; terminal and reclaimed costs are checked separately. Seven deliberate
corruptions exercise the policy, reservation, and cost checks. Thirty-five
additional policy/source/fallback cases execute in the producer and runtime
suite. The new `source-call-reuse` Nix check runs the complete gate.

Provenance commits to canonical addressed IxIR₁ and HPT roots, the source root,
lowering depth/version, pass, selected execution policy, selection outcome,
and source-specialization policy/address. IxIR₂ JSON remains diagnostic.
The source theorem separately proves actual selection, fallback, shared
reclamation, and R3/R4 costs for the checked domain; finite counters are
observations against the specialized program's physical baseline.

## Source static unique reversal

The [unique-list gate](source-unique-reuse.md#reproducibility-gate) compiles
seven checked Ixon reversals through canonical recursor-mode evidence,
consuming IxIR₁, and independently validated IxIR₂ static reuse. Forty-three
additional checks cover excluded source schemas, mode identity, target
ownership and liveness, fallback execution, and independent budgets.

```sh
lake build source-unique-reuse check-source-unique-reuse
lake exe check-source-unique-reuse --fixture .lake/build/bin/source-unique-reuse
```

Three elements use 5 physical allocations, 3 reuses, one free, zero RC, and
peak 5. Every physical prefix has distinct reservations in empty slots and
exact allocation balance. Complete release empties the heap with five frees,
preserving reuse, RC, payload, and peak observations. Disabled and exhausted
reuse retain the exact checked target baseline.

The independent Lean checker rebuilds source, mode-instance, IxIR₁ graph, and
policy preimages before checking their hashes. It follows each returned heap
using full constructor identities and unit unique ownership, verifies all
reservation prefixes and complete release, and compares every artifact byte
from two fresh processes against the reviewed matrix. Twelve deliberate
corruptions exercise identity, ownership, reservation, and cost checks. The
`source-unique-reuse` Nix check runs this complete gate. Provenance identifies
canonical IxIR₁ and policy metadata; IxIR₂ JSON remains diagnostic.

## Native unique reversal

The [native gate](source-native-unique.md) consumes the actual selected unique
artifact, emits main and release objects, and compares eight complete source
artifact sets from two fresh processes. The checker shares the independent
source/graph/policy validation above and adds exact native ABI and role
preimages, ELF text decoding, finite pointer graphs, arena-cell counts,
operation-boundary ownership, and complete release. Twelve additional native
corruptions exercise these checks.

On x86-64 Linux every object pair is linked against the pinned C harness. It
observes the actual reversed list and normalized heap, checks all saved
registers and canaries, and rejects capacity errors without writes. The native
heap observations match the byte evaluator exactly, including Word max and
64-element inputs. `source-native-unique` runs this gate in Nix. Cell counts
exclude allocation of the containing host buffer, and no timing claim is made.

## Borrowed direct calls

The [B1 gate](source-borrow.md) applies optional unary shared borrowing to an
actual validated source attachment. Every summary addition reconstructs and
validates the complete caller/callee graph. Owned wrappers preserve PAP entry;
root retains and releases can disappear only in accepted borrowed variants.
Bounded source/baseline/selected executions certify scalar result agreement,
full reclamation, strict RC improvement, and nonincreasing peak live nodes.
Any optional failure selects the exact checked baseline.

Eighteen source chains execute 5 baseline RC operations and 3 selected RC
operations, with three allocations/frees and peak two in both. Wrappers add
three control transitions; complete declaration/instruction growth, inference
attempts, and execution work are reported. Wall times are printed outside
deterministic artifacts. The independent gate reconstructs the rewrite and
replays all physical prefixes with a separate interpreter, compares complete
fresh artifacts, and rejects thirteen corruptions. The `source-borrow` Nix
check runs it. This closed-execution boundary does not generalize the IxIR₁
optimizer's open-function simulation or introduce an IxIR₂ cache identity.

The [B2 runtime gate](source-borrow-runtime.md) selects each of nine accepted
source functions once with a structural certificate, then supplies eight
runtime inputs to each artifact. Independent direct and PAP callers produce
144 baseline/selected comparisons: exactly two fewer RC operations, full
reclamation, and unchanged peak. The owned wrapper adds one control step;
stored declarations grow from `d + 4` to `2d + 6` and instructions from 7 to
`2d + 9`. Complete artifacts report inference work, source/compiler graphs,
input heaps, and every runtime prefix; wall times remain outside snapshots.

The separate interpreter also checks nine aliased borrowed lenders and their
subsequent caller releases. All ten files agree across fresh processes; four
source fallback policies, eight structural/lifetime guards, all twelve B1
negatives, and twenty artifact corruptions are checked. The
`source-borrow-runtime` Nix check runs this gate. Its finite measurements
exercise the universal structural proof; selection does not replay an input.
Native measurement waits for this shared family to become selectable.
