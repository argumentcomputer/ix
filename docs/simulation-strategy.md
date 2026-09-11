# Simulation strategy

This guide explains the relations and proof structure used to connect the
compiler stages. The [roadmap](roadmap.md) owns delivery state; focused source
contracts own accepted domains, public endpoints, and regression evidence.

## Proof boundaries

| Boundary | Relation and main obligation |
| --- | --- |
| Ixon → IxIR₀ | Typed/table-indexed source values to erased values; account for removed arguments and environment slots |
| IxIR₀ → IxIR₁ | Pure values to heap roots; preserve ownership, aliasing, and reclamation |
| IxIR₁ → logical IxIR₂ | Structured code to CFG execution through the actual checked lowering trace |
| Baseline → selected physical IxIR₂ | Live values and owned roots across changed allocation histories and variable-length reuse macros |
| Logical → physical credits | The same program under two heap interpretations, with reservation and resource accounting |
| Source/IR → native | The selected family's representation, ABI, instruction/stream/object execution, and remaining environment assumptions |

Keep four claims separate: successful-run forward simulation, memory
safety/progress, complete-result reclamation, and cost refinement. Differential
runs are regression evidence; a finite execution certificate has exactly its
checked input/state scope. Public compiler theorems derive the internal
invariants from accepted artifacts instead of asking callers to supply missing
compiler-step proofs.

## Scaling Ixon → IxIR₀

[`Sim.lean`](../Compilatrix/Sim.lean) and its supporting modules prove erasure
for the accepted source fragment. [`EraseValidator.lean`](../Compilatrix/EraseValidator.lean)
constructs syntax/program relation witnesses for the real eraser's output.
The semantic proof consumes those witnesses.

### Segment-aware application relation

Recursor applications have source segments:

```text
[params] [motives] [minors] [indices] [major]
```

The target retains parameter/motive slots as required by policy, keeps minors
and the major, and removes indices. Constructor applications remove parameters
and keep fields. [`Sim/Segment.lean`](../Compilatrix/Sim/Segment.lean) uses the
same `ArgPolicy` list as erasure:

| Policy | Relation |
| --- | --- |
| `keep` | Consume one source and target argument and require `ValRel`. |
| `ghost` | Consume both slots. Expression erasure emits `erased`; the runtime PAP relation leaves the target value unconstrained to support generic application. |
| `drop` | Consume a source slot only; the target PAP stutters. |

`PolicyPrefix` and `RuntimePolicyPrefix` retain the remaining policy and
account for source/target lengths. Ordinary `papRec` covers the slot-preserving
parameter/motive/minor prefix. `RecEraseSpine` covers the complete indexed
policy, and `papRecI` represents a completed pre-major spine.

A source PAP that escapes before its dropped prefix is complete needs a
protected target continuation. `captureThenIgnoreN` evaluates and let-captures
the target PAP before adding ignored binders, preserving surrounding de Bruijn
references. `PErase.recW`/`ValRel.papRecIW` handle remaining indices;
`PErase.ctorW`/`ValRel.papCtorParams` handle constructor parameters. Generic
application consumes the wrapper before exposing a ready target PAP.

This protection is semantic: an unwrapped target recursor could fire while
the source still expects indices. Constructor-value and recursor-major
relations also agree on block identity and parameter layout, because the
simulation is not protected by a global typing theorem. `RecMember` records
`BlockParams`; partially supplied constructor parameters remain hidden behind
the wrapper until the full constructor relation applies.

Rule environments use the mask:

```text
kept params ++ dropped motives ++ kept minors ++ kept fields
```

Indices are not rule binders. `fireSim` obtains the reversed environment from
the completed policy cursor. Rule-local indexed self calls use
`RecEraseSpine.selfHead` and recover membership through `EnvRel.selfB`, allowing
rule certification without circularly requiring its own semantic member proof.

### Shares factor out before erasure

[`Ixon/Sharing/Eval.lean`](../Compilatrix/Ixon/Sharing/Eval.lean) proves that
inlining a structurally valid sharing table preserves successful source
evaluation and recursively inlines the returned value. The proof covers all
mutually recursive evaluator functions and lifts to closed entries/constants.

`erasure_sim_inlineSharing` composes that result with share-free erasure.
`shareFree_inlineExpr_of_layer1` and `inlineBodies_shareFree` discharge the
structural prerequisite. Shared-program/expression certification runs the real
eraser on the original input, then checks its exact target against the inlined
`PErase` source. `CertifiedSharedExpr.simulatesClosed` supplies the composed
endpoint. Canonical compressor policy remains outside the semantic induction;
see [canonical sharing](canonical-sharing.md).

### Strict evaluation and configured primitives

The source evaluator has opt-in behavior for neutral eliminations and String
literal expansion. Certified erasure uses `EvalCtx.Strict`:
`preserveNeutralElims = false` and `stringLiteral = none`. Coverage certificates
retain this restriction. A successful source projection must therefore select
an actual constructor with matching projection, inductive member, block, and
field bounds. The opt-in evaluator behaviors do not widen the IxIR₀ theorem.

Quotient computation is address/kind configuration, rather than a name test.
The configured source primitive must match its constant and emitted
`quotientBody`. `ValRel.quotType`, `papQuot`, and `quotV` relate the type,
strict partial applications, and wrapped representative. Saturated `Quot.lift`
and `Quot.ind` apply the supplied function at smaller source fuel. Coverage
also checks source-telescope result ownership; sharing coherence preserves
configuration and representatives.

### Coverage and remaining frontiers

| Case | Established relation and limit |
| --- | --- |
| Computed-erased occurrences | `UsageSound` combines accepted zero usage, exact `PErase`, and two environments related to one target. Successful runs share an erased observation; raw closure captures need not be equal. Direct live reads of dropped slots reject. Typed higher-order and error/termination non-interference remain separate. |
| Configured externs | Structural coverage pins source kind, address, arity, and target declaration. `OracleRel` supplies semantic correspondence. These reusable theorems do not reopen the extern-free certified production path. |
| Split indexed recursion | Protected continuations remain related after escape through variables/lets and include rule-local indexed self calls. |
| Mutual members | `MemberScope.plan` and `MemberCoverage` certify a finite definition/recursor group against common holes, supporting cycles. Public projections, synthetic member aliases, and non-self inductive members retain exact resolver identities. Opaque members additionally require configured same-address oracle correspondence. |

The [source coverage](source-coverage.md) and [restriction ledger](lowering-restrictions.md)
record which concrete upstream inputs cross these boundaries. Keep unsupported
syntax explicit rather than broadening `ValRel` with a false neutral-to-erased
or dropped-variable clause.

## IxIR₀ → IxIR₁ ownership relation

[`IxIR1/Sim.lean`](../Compilatrix/IxIR1/Sim.lean) defines three layers:

1. `ValueGraph`/`RootsGraph` realize source scalars directly and constructors or
   PAPs through live heap nodes with related fields/captures.
2. `RootOwnership` counts environment/result roots. Shared RC equals incoming
   shared edges plus owners; unique nodes have exactly one incoming owner.
3. `HeapIso` relates locations by a finite renaming. Numeric location equality,
   dead slots, and counters are outside semantic equality.

Primitive ownership proofs cover allocation, retain, borrow-only fetch,
shallow free, shared recursive drop, and unique recursive drop. When shared RC
reaches one, freeing a parent converts outgoing edges to temporary child roots;
mutual induction over `dropVal`/`dropMany` proves recursive reclamation. The
unique dual uses `dropUVal`/`dropManyU` with no RC work. `reuse_sound` factors
reuse into inverse allocation and allocation, updating the heap bijection.

Function result worlds are part of the source/target declarations and checked
on return. `rootsForWorlds` handles heterogeneous direct-call arguments.
`FnOwnershipContract` consumes those roots and produces the declared result;
`ApplyOwnershipContract` consumes a shared function and shared arguments and
produces a shared result. Constructor dispatch exposes fields as borrows while
preserving owners. Nat dispatch extends the environment without heap effects.

### Compiler induction

[`IxIR1/LowerSim.lean`](../Compilatrix/IxIR1/LowerSim.lean) connects these
interfaces to the executable lowerer:

| Interface | Role |
| --- | --- |
| Held `VEnv` entries | Realize exact roots through stable absolute slots while emitted pushes change relative indices. |
| `EmitSound` | Treat the lowerer's `Code → Code` difference lists as weakest-precondition transformers; composition is sequencing. |
| `LowerResultSound` | Relate input/output environments and the returned descriptor to exact roots. Final uses move an owner; non-final shared uses retain it. |
| `LowerArgsSound` | Protect earlier descriptors across later argument emission and assemble the exact call/allocation root telescope. |
| `ReleasePlan` / `FieldRetainPlan` | Derive parameter cleanup and recursor field retention from generated code, including arbitrary-width telescopes. |
| `CompilerContracts` | Seal generated declaration and higher-order application obligations jointly by strong fuel induction. |

The application proof covers erased, under-, exact-, and over-saturated
execution; known, self, dynamic, and generated-wrapper calls; and lambda
lifting. Erased application still releases evaluated arguments. Dynamic PAP
entry checks the declaration's `papSafe` bit and a shared entry contract;
direct known calls retain their own mixed-world contract. `SourcePapSafe` is
therefore weaker than requiring every source declaration to be all-shared.

The production attachment rejects extern rows in both addressed IxIR₀ and
emitted IxIR₁, deriving the corresponding semantic obligations vacuously.
The unvalidated engineering evaluator retains scalar-only extern behavior;
heap-bearing externs require a separate ownership/effect ABI.

### Heap history and optimization

Shrinking passes use `HeapHistoryIso`, a finite partial bijection over live
heaps with historical dead rows where recursive release needs their names.
Unmatched dead allocation holes are allowed and counters are omitted. This
relation permits PAP fusion or destruction to change literal stores while
preserving rooted observations and complete release.

The [optimizer harness](optimizer-harness.md) composes local refinement,
whole-program history transport, and exact readdressing. Its general selected
counter result is `frees ≤ allocs`; stronger allocation/reuse/RC laws require
separate proofs. Address transport and hash-dependent wrappers retain the
[ledgered axiom boundary](trusted-extern-ledger.md).

## Structured CFG and physical execution

The [IxIR₂ specification](ixir2-spec.md) defines the syntax and checked
lowering trace. `CodeStateRel` carries the actual target definition, block, PC,
register count, source map, and environment alignment. `TraceStateRel` adds the
literal source suffix and held HPT environment. Accepted traces derive operand
translation, schema/fetch/free facts, edge arity, child entry, and declaration
lookup; semantic callers do not reconstruct these compiler invariants.

[`IxIR2/PipelineSim.lean`](../Compilatrix/IxIR2/PipelineSim.lean) uses a
source-output-indexed CPS induction. A callee's returned store/value differs
from the eventual enclosing computation's result: ordinary calls install a
resume handler, while tail calls retain the enclosing handler. An
`ApplyMorePlan` composes residual applications through repeated over-saturation.
Constructor branches include their generated field-fetch prologue; Nat
branches derive the implicit predecessor and child state.

Target budgets are existential and may differ from source fuel. Recursive
release/drop contributes its local heap work additively; other steps replay at
the suffix budget. The public whole-main theorem derives initial ownership
and every recursive transition from the checked artifact.

[`PipelinePhysical.lean`](../Compilatrix/IxIR2/PipelinePhysical.lean) transports
the baseline through its checked credit-free inventory. The more general
[credit refinement](credit-refinement.md) relates logical and physical execution
of the same program under both policies, including all present reservations.
Its complete-reclamation result requires explicit logical `RootOwnership`.

### Reuse and suspended continuations

[`ReuseLiveSim.lean`](../Compilatrix/IxIR2/ReuseLiveSim.lean) relates the actual
baseline and rewritten program through checked decisions and positive finite
macros. Unchanged instructions advance in lockstep; accepted reset/reuse sites
may take different numbers of steps.

The relation observes future-live frame registers, pending `applyMore`
arguments, and credits. Dead append-only caller registers may retain stale
locations after ownership transfers to a callee, so whole-array non-aliasing
would reject valid reuse. Checked trace coverage and producer ownership derive
root support for precisely the observable suspended values.

Physical hot reuse removes the consumed live-location pair and adds the
reused/fresh result pair. Cold allocation extends the existing history.
Supported stacks, lender facts, reservation disjointness, and the checked
accepted-entry phase survive these changes. Guided successful execution and
prefix determinism supply macro witnesses; the public compiler endpoint has
no missing accepted-site callback.

Semantic history relations omit counters. Allocation/free comparison,
RC potential, peak-live bounds, and occupied-space capacity use their own
invariants. A v1 caller may suspend credits across non-tail direct calls;
the callee starts with none and cannot access the reserved slots.

## Public composition endpoints

| Entry or family | Contract reference |
| --- | --- |
| Validated source → owned IxIR₁ | [`PipelineSound.lean`](../Compilatrix/PipelineSound.lean): semantic, progress, memory-safety, and reclamation interfaces |
| Structured logical main | `Attached.successfulCanonicalMainSimulation` in [`PipelineSim.lean`](../Compilatrix/IxIR2/PipelineSim.lean) |
| Selected physical main | `OptimizedAttachment.physicalMainSimulation` and `selectedPhysicalMainSimulation` in [`ReuseLiveSim.lean`](../Compilatrix/IxIR2/ReuseLiveSim.lean), including baseline fallback |
| Recovered shared source | [Recursion recovery](source-recursion.md), with source/resource/allocation/RC/peak composition |
| Shared source maps | [Reuse across calls](source-call-reuse.md), with v1 reservations and original-source fallback |
| Consuming unique source | [Unique reversal](source-unique-reuse.md), with static reuse and full release |
| Borrowed source calls | [Closed certificates](source-borrow.md) and [structural runtime borrowing](source-borrow-runtime.md) |
| Native source families | [Closed unique](source-native-unique.md), [runtime unique](source-native-runtime.md), [unchanged upstream](source-native-upstream.md), and [runtime scalar](source-native-scalar.md) contracts |
| Encoded execution | [E1 instructions](x86-encoded-instructions.md) and [E2 streams/objects](x86-stream-objects.md); reference ISA and system linker/loader assumptions remain explicit |

## Proof maintenance

Reuse evaluator inversion, list/array relations, fuel framing, heap algebra,
and address transport. Keep recursor layout, partial application, and firing
lemmas separate so the main induction dispatches instead of repeating
segment arithmetic. Preserve public theorem names when extracting helpers.

Each new pass must compose a refinement with the exact selected artifact or
return independently checked evidence. Optional failure retains the last
validated program. The [development guide](development-plan.md) describes
axiom fences, negative cases, integration checks, and documentation updates.
