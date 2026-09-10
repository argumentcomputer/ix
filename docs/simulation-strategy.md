# Simulation scaling strategy

Proof architecture originating 2026-08-14, reviewed 2026-09-06. This document
explains the erasure and ownership relations and their proof decomposition.
The [roadmap](roadmap.md) owns completion state and current composition
packages; the [development guide](development-plan.md) records validation
practice.

The scoped IxIR₀→IxIR₁ compiler induction is complete and attached in
`PipelineSound.lean`. The separate `IxIR2/PipelineSim.lean` induction now
exposes `Attached.successfulCanonicalMainSimulation` into logical IxIR₂.
Dynamic reuse now exposes `OptimizedAttachment.physicalMainSimulation` for
the exact validated optimizer output. It derives compiler progress internally,
including constructor macros, returns after tail calls, and repeated residual
`applyMore` dispatch. `selectedPhysicalMainSimulation` also covers the checked
baseline fallback returned by `selectAttachment`. `PipelinePhysical.lean`
transports the baseline's exact logical execution to its physical interpretation;
`X86/PipelineSim.lean` composes validated source evaluation with the actual
selected scalar target. The detailed relation slices below describe the existing
foundations, not the immediate queue.

## Non-negotiable theorem boundaries

The two foundational simulations use different relations:

1. **Ixon → IxIR₀** relates a typed/table-indexed source evaluation to pure
   erased values. Its hard problem is which source arguments and environment
   slots disappear.
2. **IxIR₀ → IxIR₁** relates pure values to roots in an explicit heap. Its hard
   problem is ownership, aliasing, reclamation, and location renaming.

The downstream contracts are distinct as well: structured lowering relates
IxIR₁ to logical IxIR₂; reuse relates live heaps across changed allocation
histories; selection consumes physical IxIR₂ and relates it to the typed
target model. The [IxIR₂ specification](ixir2-spec.md) states the credit and
resource obligations. A local reduction lemma or fixture does not compose
these boundaries by itself.

The differential harnesses remain regression tests. A theorem may use the same
readback vocabulary, but “both executions happened to agree at one fuel” is not
a compiler-correctness proof.

## Scaling Ixon → IxIR₀

The theorem covers literals, definitions, configured quotient primitives,
constructors with complete or protected escaping dropped-parameter prefixes,
projections, and parameterized recursor ι with complete or protected escaping
source-only index segments, including rule-local indexed recursive self calls. The
ordinary recursor-pap relation keeps source and target lengths aligned through
the parameter/motive/minor segment; indexed spines are certified as one unit
through the later source-only segment.

### Segment-aware application relation

Recursor spines have source segments

```text
[params] [motives] [minors] [indices] [major]
```

and erased target segments

```text
[params: keep or ◻] [motives: ◻] [minors: keep] [major]
```

Indices disappear entirely. Constructor spines similarly drop their parameter
segment and retain fields. The relation is therefore driven by the
same `ArgPolicy` list as executable erasure:

- `keep`: consume one source and target argument and require `ValRel`;
- `ghost`: consume both positions; exact expression erasure emits target
  `erased`, while the runtime pap relation intentionally leaves the target
  value unconstrained so it is closed under generic related application;
- `drop`: consume only the source position; the target pap stutters.

`Compilatrix/Sim/Segment.lean` now supplies the generic policy-indexed list
relation. `PolicyPrefix` carries the unconsumed suffix as a cursor through
partial applications; its checked laws account separately for source and
target lengths, and its append lemmas implement keep, ghost, and drop steps.
`RuntimePolicyPrefix` is the runtime cursor used by recursor paps. `papRec`
uses its slot-preserving parameter/motive/minor prefix for index-free partial
applications. `RecEraseSpine` instead carries the complete policy, including
source-only `drop` steps. A complete indexed pre-major spine produces
`papRecI`. If a visible spine stops inside the index suffix,
`captureThenIgnoreN` first evaluates and let-captures the target pap, then
exposes one ignored continuation binder per remaining index. `PErase.recW` and
`ValRel.papRecIW` certify that wrapper through arbitrary variable- or let-headed
applications and transition to `papRecI` exactly when the last index is
consumed. The let prevents surrounding de Bruijn variables in the pre-major
pap from being captured by the new lambdas. `RecEraseSpine.selfHead` gives the
same treatment to a rule-local indexed `recur` head; it obtains `RecMember`
from `EnvRel.selfB` at simulation time instead of recursively requiring the
member while its rule body is being certified.
`ctorPolicy` plus `ctor_fields` extracts the retained field relation after the
dropped parameter prefix. Constructor pap/value cases carry this cursor,
including an explicit strict-under-saturation invariant. `CtorParamSpine`
tracks any visible parameter prefix. A partial prefix emits one ignored target
lambda per remaining parameter (`PErase.ctorW`); `ValRel.papCtorParams` relates
the source pap to that closure and remains closed under generic application,
even after the value escapes through a variable or let. The final wrapper
application exposes the field-arity constructor, after which ordinary
`papCtor`/`ctorV` application advances through related fields.

There is one coupling that the original ordering understated. The current
simulation is deliberately untyped. If a parameterized constructor value is
added to the global `ValRel` before recursor layouts are strengthened, an
untyped zero-parameter recursor can consume it: the source checks
`rec.params + rule.fields`, while the target sees only retained constructor
fields. Those checks need not agree. Consequently constructor-value
generalization and recursor-major parameter compatibility landed together:
source firing guards constructor-block identity and literal
parameterlessness, while `RecMember` records `BlockParams` for the finite
mutual table. Before the full parameter prefix, `papCtorParams` exposes only
an ignored closure, which cannot be mistaken for a recursor major. The final
wrapper application transitions to `papCtor` or `ctorV`, where those block and
layout guards apply.

Rule environments now retain a mask derived from the policy list:

```text
kept params ++ dropped motives ++ kept minors ++ kept fields
```

Indices are not rule binders and never enter that mask. `RecMember` stores the
finite block-layout witness, and `fireSim` converts the fully consumed runtime
cursor directly into the reversed rule environment rather than re-proving
segment arithmetic. For an indexed recursor, the full cursor is split at the
drop suffix only after every index has been consumed; `papRecI` then records
the source rule arguments and index arguments separately while exposing the
same ready-to-fire target pap. This boundary is essential: an intermediate raw
target pap is already one application from firing, while its source counterpart
still expects indices and a major, so only the protected `papRecIW`
continuation may enter global `ValRel`.

### Shares factor out before erasure

Do not add a recursive `.share` clause to `PErase`. Evaluator coherence is
proved once in `Compilatrix/Ixon/Sharing/Eval.lean`:

```text
eval frame-with-table e = ok v
  → eval frame-with-empty-table (inlineExpr table e)
      = ok (inlineSharing v)
```

under the decoder-enforced layer-1 invariant. `erasure_sim_inlineSharing` and
its closed corollary now compose that result with the share-free erasure
theorem. This keeps canonical-compressor policy completely
outside `Sim.lean`. The structural prerequisite is now discharged by
`shareFree_inlineExpr_of_layer1` and the constant-level
`inlineBodies_shareFree`. The public `eval_inlineSharing` theorem covers the
six mutually recursive evaluator functions through one induction, while
`evalClosed_inlineSharing` and `evalConst_inlineSharing` lift it to entry
points. `certifySharedProgram`, `certifySharedExpr`, and the closed-frame
wrapper run the real eraser on original shared input, then validate its exact
target against the inlined `PErase` source. `CertifiedSharedExpr.simulatesClosed`
connects that certificate directly to the composed theorem.

### Neutral eliminations, String literals, and the strict erasure boundary

Open evaluation and certified runtime evaluation deliberately use two modes.
With `EvalCtx.preserveNeutralElims = true`, projecting a neutral value produces
a `NeutralId.projection` pap whose first argument is the projected neutral;
later applications extend that same spine. A recursor pap is classified as
neutral only once it is saturated, and firing it on a neutral major preserves
the complete recursor application. Mutual-member neutrals use
`NeutralId.member block index`, so equal local indices in different blocks do
not collapse. `EvalCtx.inlineSharing` preserves the mode, and the sharing
coherence proof maps all of these values structurally.

Projection identity is checked before either reduction or neutral-spine
construction. The local `prj` type index must select a resolved `iPrj`; that
projection must resolve to the named inductive member; and a constructor value
must carry the same block and member index. Only then is the field selected
after the inductive parameter prefix. Missing, non-`iPrj`, wrong-member,
wrong-family, and out-of-range cases fail closed.

Certified erasure stays in the default strict mode. Its projection theorem
uses the fact that every successful source projection selected a real
constructor; admitting a successful neutral projection would invalidate that
constructor-only premise for the erased projection trace. Accordingly,
String recursor majors have a second opt-in source behavior.
`EvalCtx.stringLiteral` supplies the exact addresses of `Char`, `Char.ofNat`,
`String.ofList`, and `List.nil/cons`. A literal is rebuilt in Unicode-scalar
order as the upstream universe-zero `List Char` term, then all five heads and
the current String representation compute through the ordinary resolver and
application semantics. This deliberately avoids encoding a particular String
constructor layout in the evaluator. Sharing coherence follows every resolved
head and intermediate application.

IxIR₀ does not yet represent that constructor expansion, so certified erasure
must not claim those additional successful source runs. `EvalCtx.Strict`
therefore packages both `preserveNeutralElims = false` and
`stringLiteral = none`. `MemberCoverage.nil` carries the package, validated
program coverage rejects either open feature, and empty-member-scope
simulation and lowering theorems take it explicitly. Member-scoped theorems
recover it from their coverage certificate. This is a semantic boundary, not
merely a validator convention: the opt-in behaviors remain available to the
source evaluator, but those runs are not claimed by the current IxIR₀
simulation.

### Configured quotient compilation

Quotient computation is explicit closed-world configuration, not a name test.
`EvalCtx.quotientKind` must assign a resolved quotient address exactly the kind
stored in its constant. Unconfigured addresses retain the old neutral
behavior, while a mismatched configured kind is stuck. A configured `quotH`
uses the source arity of `Quot`, `Quot.mk`, `Quot.lift`, or `Quot.ind`.
Saturated `mk` produces a distinct `quotV` wrapper rather than an
over-applicable pap; `lift` and `ind` recover its representative and apply the
supplied function at smaller evaluator fuel.

Erasure emits fixed public lambda bodies (`quotientBody`). `ValRel.quotType`
maps the type primitive to `◻`; `papQuot` relates every strict source prefix to
the corresponding residual IxIR₀ closure; and `quotV` relates the wrapper
through its representative. The generic application proof reuses the main
simulation on a synthetic two-variable application for the eliminator call.
`Covered.quot` and `EraseValidator.validateCovered` additionally pin the
configured address/kind, exact emitted body, and source-telescope result
ownership. `SimInstance.quotientLiftSim` and `quotientIndSim` certify real
program and expression erasures and return the contentful representative
`37` on both sides. Full sharing coherence preserves the quotient
configuration and recursively inlines representatives inside `quotV`.

### Hard frontiers and landed relation slices

1. **Dropped-variable occurrences — landed fragment.** `EnvRel` intentionally
   leaves dropped slots unconstrained, so a clause mapping a direct read to
   `erased` remains false. The landed `UsageSound` theorem instead combines an
   accepted-lambda computed-zero witness with exact `PErase` and two source
   environments related to one target environment. Successful source runs
   then share a common erased observation, not necessarily equal raw values
   (closures can retain distinct irrelevant captures). The contentful fixture
   passes the changed dropped variable as a known definition's ghost argument;
   the checker zero-scales that occurrence, the eraser emits `◻`, and both
   `7̂`/`8̂` runs return `9̂`. Direct live reads are rejected. Typed
   higher-order heads and termination/error non-interference remain open.
2. **Externs — landed explicit oracle correspondence.** Configured opaque
   definitions and axioms have structural `Covered` cases that pin the source
   kind and configured arity to the exact same-arity target `Decl.extern`.
   `papExtern` relates every strict application prefix. At saturation,
   `OracleRelAt` requires related argument lists and turns each successful
   source-oracle result into a related target-oracle result. The validator can
   reconstruct the structural witness but cannot authorize semantics, so
   `OracleRel` stays an explicit theorem premise in the erasure relation.
   These reusable extern cases do not reopen the production certified
   pipeline, whose exact IxIR₀/IxIR₁ extern scans reject such declarations.
   The old general neutral-to-erased clause is
   restricted to resolved inductive-projection type heads. A contentful axiom
   fixture returns `42` on both sides; negative guards cover absent
   configuration, target-arity drift, and a configured source oracle miss.
3. **Split indexed recursion — landed protected continuation.** The executable
   eraser protects a pre-major target pap for exactly the remaining source-only
   indices. The validator reconstructs the wrapper structurally, and the
   theorem proves it closed under generic application after escape through a
   let. A contentful two-constructor family exercises both the projection head
   and a rule-local indexed self call, recursively reducing a step-wrapped base
   value to `73` on both evaluators.
4. **Mutual members — landed all emitted member kinds.**
   `Covered.defnProj` follows an unfoldable public `dPrj` through the exact
   synthetic member alias, checks result ownership once for both declarations,
   and validates the member body in the block frame. `PErase.recurI` ties a
   non-self runtime member slot to the same resolver-selected inductive whose
   emitted declaration is `◻`; `ValRel.inductiveMember` stays closed under
   arbitrary later application because both target reference and applications
   absorb to `◻`. One fixture returns `91` through `dPrj`; a mixed block
   evaluates an escaping inductive-member application and then returns `88`.
   `MemberScope.plan` names the finite definition/recursor member set, while
   `MemberCoverage` proves every body/rule set against the same holes rather
   than nesting acyclic `Covered` proofs. `PErase.recurD`/`recurR` and
   `RecEraseSpine.memberHead` consume that certificate, including through
   recursor firing and the call-aware projection-safe trace. Exact fixtures
   close a two-definition cycle returning `71` and alternating recursors
   returning `77`; an incomplete plan is rejected. For an opaque definition,
   source `.recur` and public `dPrj` evaluation now use the exact synthetic
   member address emitted as the target extern key. `PErase.recurO`,
   `MemberRel.externDefn`, and `Covered.externDefnProj` pin resolution,
   configuration, alias shape, and arity, while the existing same-address
   `OracleRel` supplies semantics. A wrapper call and direct public projection
   both return `83`; missing configuration and target-arity drift are rejected.

### Proof-engineering automation

- Keep one library of `Except.bind` inversion, list relation, array lookup,
  and fuel-monotonicity lemmas.
- Have `EraseValidator` synthesize syntax/program relation witnesses; semantic
  simulation continues to consume those witnesses rather than trusting the
  Boolean validator.
- Split recursor lemmas by layout/pap/fire. The main evaluator induction should
  dispatch to them and never repeat telescope arithmetic.
- Keep unsupported syntax explicit in the validator and the tracked roadmap.

The landed order is: share-eval coherence → generic policy relation →
constructor parameters → recursor parameters → complete visible recursor
indices → computed-erased successful-run non-interference → configured
quotient ι and compilation → configured opaque/axiom extern correspondence.
The constructor-wrapper lift, protected indexed-continuation/self-call lift,
definition-projection/non-self-inductive lift, and simultaneous cyclic-member
certificate follow that sequence, followed by opaque mutual-member identity.
The typed higher-order/broader dropped-occurrence frontier remains a possible
fragment extension. Production mutual-member identity is supplied by the
addressed erasure and scoped member certificates in `PipelineSound.lean`;
retiring synthetic member identities from the production path is no longer
an active work item here.

## IxIR₀ → IxIR₁ ownership relation

The memory theorem needs more than the current `Tree.agree` readback. Its
relation has three layers:

1. **Value realization:** scalar source values relate directly; a source
   constructor/pap relates to a live target location with matching node shape
   and recursively related fields/captures.
2. **Root ownership:** a multiset records every live environment/result root.
   Shared-node reference counts equal incoming shared edges plus root owners;
   unique nodes have exactly one incoming owner and cannot alias.
3. **Heap graph isomorphism:** locations are related modulo a finite renaming,
   not by numeric equality. Unreachable dead slots and cost counters are
   outside semantic equality.

This foundation is now executable Lean proof infrastructure in
`IxIR1/Sim.lean`. `ValueGraph`/`RootsGraph`, `RootOwnership`, and `HeapIso`
implement the three layers above. Heap isomorphism is reflexive (for closed
stores), symmetric, transitive, and extends across paired allocations; value
realization transports across it. Exact ownership is proved invariant under
allocation, `dup`, and every successful shared `drop`. The `rc = 1` proof
first removes the sole-owned parent and turns its outgoing edges into
temporary child roots; a mutual fuel induction over executable
`dropVal`/`dropMany` then covers arbitrary recursive reclamation. A concrete
fixture exercises two aliases of one child: the first release decrements it
and the second reclaims it. Its unique-world dual is now proved by mutual
induction over `dropUVal`/`dropManyU`; a two-node fixture deep-frees with zero
RC operations. `reuse_sound` then factors in-place overwrite into inverse
allocation plus allocation and constructs the explicit heap bijection to the
shallow-free-plus-append-allocation specification. The next boundary is the
remaining primitive interface. That boundary has now landed too: `free`
exposes unique child roots, while `fetch` is explicitly borrow-only and its
following retain step adds exactly one shared root and RC increment. Scalar
`pure`, allocation, and both drop operations are tied to the same ownership
API. Declaration result worlds have now landed end to end:
`IxIR0.Decl.defn` and `IxIR1.FnDef` carry `Owned`, erasure preserves the
innermost source-arrow result (with `.shared` for non-functions), and lowering
checks direct-call demands while keeping unknown `apply` shared-only. The
evaluator independently validates every function return, and
`invoke_fn_result_hasWorld` turns successful invocation into the simulation's
`HasWorld` fact. The exact control-flow layer has landed as well.
`rootsForWorlds` represents heterogeneous argument telescopes and
`FnOwnershipContract` is the semantic obligation the whole-program compiler
proof must construct. Under that contract, `invoke_fn_owned`,
`runOp_call_owned`, and `runOp_callSelf_owned` consume all argument roots,
produce exactly one declared result root, and preserve the continuation.
`ApplyOwnershipContract` is the corresponding whole-context obligation for
higher-order calls: successful `applyGo` consumes the shared function root
and all shared argument roots and returns one shared result root.
Constructor dispatch leaves the root invariant unchanged and exposes fields
only as borrows; Nat zero/successor peeling likewise preserves roots while
extending only the runtime environment.

The compiler induction in `IxIR1/LowerSim.lean` uses held `VEnv` entries
that realize exact roots through in-bounds absolute slots, and runtime
pushes preserve that realization. `EmitSound` presents the lowerer's
`Code → Code` difference lists as weakest-precondition transformers, making
emitter composition the sequencing rule. Evaluator interfaces have been
lifted to emitter rules for pure, allocation, retain, direct call, both drop
modes, shallow free, and borrow-only fetch; the call rule consumes a
`FnOwnershipContract`. `LowerResultSound` then ties input/output `VEnv`s and
the returned `AVal` to exact roots. Literal and erased executable equations
are verified, as is the first sequencing derivation
`let many x := literal; x`, including its closed emitted-code ownership
fixture. Final source-variable uses now move an arbitrary held root to the
result position (shared, affine, or linear), relying on the new permutation
invariance of `RootOwnership`; non-final `many` uses retain the shared root,
push the duplicate, and update the exact remaining-use descriptor. Both are
paired with the executable `lowerE` equations, and a non-head unique fixture
exercises root extraction rather than only the list head.

Argument sequencing is now landed too. `LowerResultSound` frames an arbitrary
list of protected absolute slots and proves stable returned descriptors
(`slotA`, literal, or erased), so an early argument can survive later pushes.
`LowerArgsSound` realizes worlds, descriptors, and runtime values in lockstep;
its cons rule protects the head while emitting the tail, realizes it again at
the final `VEnv.depth`, and permutes its owner into the exact
`rootsForWorlds` prefix expected by calls and allocations. Both executable
`lowerArgs` equations (nil and the generic recursive cons) are paired with
these proofs. A two-push fixture forces the first argument to change relative
index before both descriptors are realized.

The terminal `knownCall` consumers are now proved. `AValsRealize.resolveAtoms`
shows that the compiler's mapped atom array resolves to precisely the tracked
runtime values. `LowerArgsSound.call_owned` then feeds the heterogeneous
argument-root prefix to `FnOwnershipContract`, consuming every argument and
producing the declaration's single result root. Its constructor dual first
proves a homogeneous world telescope, then uses allocation to transfer all
field owners into the fresh node. Both rules are paired with the actual
non-overapplied `knownCall` branch, and two-push fixtures exercise call and
allocation after relative indices have shifted.

The non-erased higher-order path is landed as well. `runOp_apply_owned` lifts
`ApplyOwnershipContract` through the evaluator, and `emit_apply_owned` lifts
that rule through an emitted operation. `LowerArgsSound.apply_owned` protects
the already-produced function descriptor across every later argument push,
then consumes the function and homogeneous shared argument prefix together.
`LowerResultSound.applyArgs` composes the entire emitter. This is paired with
the actual successful `applyRest` branch and with the over-applied direct-call
branch of `knownCall`; a two-push fixture forces both function protection and
relative-index adjustment.

Erased application now has an exact dual. Stable argument descriptors remain
realized across the inert slots pushed by each release operation;
`releaseAll_sound` consumes precisely the shared argument-root prefix while
preserving the source environment and protected slots. The executable erased
`applyRest` branch is paired with that proof, and a two-push fixture pins both
drop operations and their changing relative indices. Executable
`lowerSpine` rules now cover application flattening, syntactic erased heads,
ordinary variable heads, exact saturated definitions and constructors, and
over-applied shared definitions.

Recursive and partial-call dispatch has since advanced. The evaluator's
`runOp_callSelf_owned` interface is lifted through `emit_callSelf_owned` and
`LowerArgsSound.callSelf_owned`; terminal and over-applied `knownCall` rules
then pair both successful `recSelf` shapes in `lowerSpine`. For under-
saturation, `runOp_papp_owned` proves that every shared capture root becomes
an edge of a fresh shared pap node, and the corresponding emitter and
`LowerArgsSound.papp_owned` rules reach partial definitions, recursors, and
externs. Exact saturated recursor dispatch is also paired with its direct
call contract. A two-push fixture exercises pap capture after relative-index
movement.

The successful `lowerSpine` dispatch matrix is now complete. The scalar-only
extern check is reflected by `callScalarOracle_ok`, scalar-root elimination,
and `runOp_extern_owned`, then lifted through terminal and over-applied extern
branches. Shared constructor and recursor over-application reuse the protected
`applyRest` rule. Dynamic lambda/let/projection/literal heads are classified
and paired with either erased or non-erased application, while under-applied
constructors compose the stateful `wrapperFor` result with `papp` and an
explicit generated-wrapper declaration premise. The reusable declaration
contract layer is now present: `FnEntryRealizes`/`FnBodySound` turn a closed
lowered body into `FnOwnershipContract`, while `AltOwnershipContract` records
valid branch layouts, exact input roots, borrowed fields, and an arbitrary
caller continuation. Its lowering constructor composes a retain/release
prefix with `LowerResultSound.close`, and constructor plus peeled-Nat dispatch
consume the resulting contract. `FnEntryRealizes.parameterEntries` now proves
the canonical layout for an arbitrary source telescope. `SlotDrop` records
both entry and absolute indices; `ReleasePlan` proves the actual
`releaseSlots` result and its shared/affine ownership transformer, and the
generic verified `lowerFnBody`/`.defn` rules compose it with recursive
expression proofs. Canonical `parameterEntries`/`parameterDrops` telescopes
now generate those plans automatically whenever every dead parameter is
shared or affine; the theorem is stable under the trailing entry frame used by
lambda lifting, and the generated `.defn` rule exposes only the corresponding
mode-admissibility premise. Executable fixtures cover a two-parameter dead
shared argument and a three-parameter shared/affine/shared release sequence.
For recursors, the concrete prefix fixtures are now subsumed by an
arbitrary-width proof. `FieldRetainPlan` follows the compiler-generated
borrowed-field fold while preserving every original slot and later borrow;
the generic major rule consumes the scrutinee; the framed `ReleasePlan` then
releases all dead pre-major parameters. `lowerRecursorRule` exposes this as a
per-rule compiler boundary, `lowerRecursorRule_generated_verified` closes an
RHS proof into `AltOwnershipContract`, and the state-threaded
`RecursorRulesPlan` collects the `mapM` result. Finally,
`lowerRecursor_generated_verified` feeds every selectable constructor or
peeled-Nat alternative to the case collector and produces the recursor's
`FnOwnershipContract`. The apparent recursive-contract cycle is now made
well-founded explicitly. `FnOwnershipContractBelow`, bounded alternative and
`applyGo` contracts, and evaluator bridges for direct calls, `callSelf`,
`apply`, and constructor/Nat dispatch expose the strict fuel decrease.
`SourceDeclContracts` records the source/target declaration layout and
contracts; `CompilerContracts` seals it jointly with higher-order application
by strong induction. A hereditary bounded Hoare layer preserves emitter
composition. On the recursor path, bounded retain/release plan semantics now
prove the generated call-free prefix internally; bounded RHS proofs produce
bounded alternatives, `RecursorRulesPlanBelow` threads their compiler state,
and `lowerRecursor_generated_verified_below` yields exact-fuel function
preservation. The bounded compiler induction has now crossed its spine seam:
successful `lowerArgs` and `applyRest` runs are derived from smaller-fuel
expression proofs; `knownCall_run_sound_below` factors every operation
builder; and `lowerSpine_run_sound_below` connects application flattening,
erased and dynamic heads, ordinary variables, `recSelf`, and the complete
definition/constructor/recursor/extern reference matrix. Stateful partial
constructors expose exactly the generated-wrapper declaration/arity premise,
and standalone `.ref` lowering reuses the empty-argument spine theorem.
Bounded `lowerBorrow` derives dynamic borrows from smaller-fuel expression
soundness while handling source variables directly. Projection composes that
interface with borrowed `fetch`, field retention, optional final-use target
release, erased absorption, and the vacuous scalar-stuck branch. The resulting
compiler induction now reaches the joint declaration/application seal.
Dynamic saturation resolves the PAP owner and consults its address-committed
`papSafe` bit; direct known calls do not. `PapSafeDeclContracts` therefore
requires a homogeneous shared boundary only for dynamically enterable
declarations, while source and generated declarations retain their own direct
contracts. Rewrite and readdress simulations preserve this policy, and the
mixed-mode model establishes that the resulting `SourcePapSafe` premise is
strictly weaker than a globally all-shared source environment.

The IxIR₁ runtime and unvalidated engineering pipeline retain a scalar-only
extern boundary: direct and declaration-mediated oracle calls reject heap
arguments and heap results, so no heap owner crosses that boundary. The
certified pipeline is stricter. It rejects extern rows on both the exact
addressed IxIR₀ input and the emitted IxIR₁ artifact graph, retains those
checks in `ValidatedCompilation`, and derives the semantic and termination
extern contracts vacuously. Reopening validated externs for heap values
requires an explicit consume/borrow/retain ABI.

Location renaming is load-bearing for `reuse_sound`: target `reuse` keeps one
location, whereas the specification “free old node, allocate new node” may
choose a different number. The proof updates the graph bijection while
preserving exact ownership and rooted observations. The landed fixture forces
the two result locations to be numerically different and separately records
the intentionally excluded allocation/free/reuse counter differences. IxIR₂
generalizes this exact split into logical free-plus-allocation and physical
credit-reuse semantics with terminal counter equations; see the
[IxIR₂ v0 specification](ixir2-spec.md).

Correctness is split into independently checkable theorems:

- **semantic forward simulation:** successful source evaluation has a target
  execution with a related result;
- **memory safety/ownership conservation:** well-moded lowering never produces
  `Err.mem`, and every step preserves the root/RC invariant;
- **reclamation:** releasing the final owned root leaves no reachable live
  nodes (and, for closed runs, `Store.live = 0`);
- **cost refinement:** alloc/reuse/free/RC counters satisfy separate equations
  and inequalities. Counter facts are not mixed into semantic equality.

Shrinking heap optimizations use a second semantic equality boundary.
`HeapHistoryIso` relates live heaps by a finite partial bijection, retains
dead/dead rows when recursive reclamation still needs their historical names,
permits unmatched dead allocation holes, and deliberately omits counters.
The IxIR₁ evaluator commutes with this relation across code, operations,
invocation, higher-order application, and all shared/unique drop entries. Local
PAP/application fusion is the first consumer: removing its transient PAP is
observable to literal stores but invisible through this history relation.

The completed dependency order is graph/root relations and primitive
ownership interfaces → declaration result worlds → call/case preservation
→ actual lowering derivation → whole-program declaration correspondence and
the generated-function/application seal. Lambda lifting and PAP ownership
participate in that seal. Further proof extensions should reuse these
interfaces rather than restart the induction or duplicate evaluator
inversions. The [general credit refinement](credit-refinement.md) now composes
logical/physical execution under both policies; the [roadmap](roadmap.md)
records the next source and native boundaries.

## Baseline physical and scalar target composition

`IxIR2/CreditFree.lean` inventories every instruction in main and all function
declarations. `lowerCheckedWithTrace` retains a proof that the baseline contains
no `allocWith`, `discardCredit`, `takeUnique`, or `resetShared`. This check sits
alongside ordinary validation and the existing lowering-trace audits.
`IxIR2/Interpretation.lean` transports successful steps through current and
suspended frames, calls, tail calls, returns, and residual application, preserving
the entire machine. `runMain_creditFree` therefore preserves the exact result,
store, counters, and both remaining budgets under either interpretation with
the same schemas and oracle. The inventory theorem itself permits extern rows;
the certified attachment separately retains its existing extern-closure checks.
`Attached.successfulPhysicalMainSimulation` composes this transport with the
logical lowering theorem and keeps its `OutcomeRel` unchanged. Programs that
produce or consume credits still require the general refinement theorem.

`IxIR2/EvalFuel.lean` proves successful result uniqueness across arbitrary
control and heap budgets. Heap-budget extension preserves successful machine
steps, allowing any two successful runs of the same program and interpretation
to be compared at one common budget. `X86.Select.Output.refinesSuccessfulRun`
uses this result to connect any successful physical run to the exact target
returned by selection. Recognition reflects equality with either the original
literal/alias graph or the complete `ScalarApply.program` graph, including its
two distinct addressed declarations. `ScalarApply.runs` proves the latter's
six-step execution uniformly in both addresses, the word, and interpretation.

`X86.Select.sourceRefines` derives addressed erasure, owned addressed IxIR₁
execution, physical baseline execution, and selected local x86 execution from
the actual checked attachment. Its source premises remain the configured
oracle relation, sharing well-formedness, and successful Ixon evaluation.
`sourceScalarRefines` specializes the result relation to a source Nat: the
selected word's `toNat` equals that Nat exactly, the typed machine halts with
the selected word, and `rsp` is preserved. Neither theorem adds a truncation
assumption or a caller-supplied intermediate execution.

The synthetic fixture in `X86/ValidatedScalar.lean` executes each intermediate
observation and carries the actual addressed IxIR₁ graph root into the ELF
note. Native differential checks supplement these typed-machine theorems.
[E2](x86-stream-objects.md) now supplies certified complete-stream and ELF
interpretation bridges; local ISA faithfulness and system linker/loader
behavior remain ledgered.

## Checked source recursion recovery

`IxIR0/Recursion.lean` separates an untrusted proposal from an exact checker
for the first eager immediate-tail `below` schema. A checked result fixes
the replacement recursor, verifies source and target lookup, and gives the
derived declaration its fresh canonical identity. Unrecognized inputs keep
the literal declarations and entry.

`IxIR0/RecursionSim.lean` proves the eager source tuple fold (`sourceTuple`)
and its projected function application, then the direct accumulator loop.
`recursorForwardSimulation` covers arbitrary finite lists of values and
accumulators in the actual evaluator. `Recovered.forwardSimulation` lifts
the result to the exact checked closed Nat-list entry, including its
erased-argument wrappers and optional retained alias.
`Selection.forwardSimulation` includes literal fallback.

`Recursion/Sim.lean` supplies `Compilation.sourceRefines`. It uses the
original validated source certificate and its actual member scope to derive
raw erasure execution, then applies the selected-IxIR₀ theorem. The existing
source sharing and oracle contracts and successful Ixon evaluation remain
explicit premises; the intermediate execution is derived internally.
The [D1 axiom fences](../Compilatrix/Fence.lean) retain the ordinary Lean
basis and, for the addressed wrappers, the existing BLAKE3 assumption.

`LoweredCompilation.lean` provides a common boundary for original and recovered
IxIR₀: the exact ownership/addressing trace, selected source rows, and closed
source/target extern checks. `Pipeline.LoweredCompilation.addressedOwnedMain`
derives compiler contracts, progress, ownership, and addressed execution from
that record and a call-aware source trace. `Recursion/Trace.lean` derives the
trace for the projection-free recovered program from successful evaluation.
The original source certificate supplies the trace for literal fallback.

`Recursion/PhysicalSim.lean` composes these results with the common checked
HPT/CFG attachment, baseline physical interpretation, and selected reuse.
`Compilation.sourceRefinesSelected` takes only the existing source premises
and concludes `SelectedExecution`: actual selected physical IxIR₂ for recovered
outcomes, or original owned addressed IxIR₁ on outer fallback. No intermediate
execution or compiler invariant is a caller premise. Seven D2 fences preserve
the existing axiom basis.

R2 keeps that semantic relation unchanged. `IxIR2/HeapAccounting.lean` proves
heap-operation and linear-credit balances; `IxIR2/Resources.lean` carries
`live + frees + presentCredits = allocs` across actual physical steps, including
continuations and returns. Fresh execution establishes it, and halt yields
`live + frees = allocs`. `IxIR2/ReuseResources.lean` transports shared release
and an empty resulting heap through the existing stable heap relation.
`IxIR2/PipelineResources.lean` derives the required owned baseline release
from the common compiler record and applies it to both selection branches.
Releasing the selected result leaves `live = 0` and `allocs = frees`.

`Recursion/Resources.lean` composes these guarantees with D2's exact source
premises and value relation, retaining original owned IxIR₁ reclamation on
literal fallback. Allocation accounting is independent of result world;
selected reclamation currently covers shared results. Nine further fences
retain the same trust basis. The [source cases](source-recursion.md) check
terminal and reclaimed allocation balances.

R3 adds `IxIR2/AllocationEvents.lean`: ordinary heap operations preserve
`allocs + reuses`, while fresh allocation and reuse each add one. Related
unchanged instructions and returns have equal event increments, including
dynamic partial application and `applyMore`. Accepted hot/cold macros each
add one event on both sides. `AllocationDelta` composes these increments in
the existing compiler synchronization proof; it is a separate component of
the compiler invariant, leaving the semantic machine, heap, and value
relations unchanged.

`IxIR2/ReuseCost.lean` derives equal live-node counts from heap history;
`IxIR2/ReuseAllocation.lean` combines this with event equality and terminal accounting.
`IxIR2/PipelineAllocation.lean` derives zero baseline reuse from the actual
owned execution and compiler trace. For the checked shared-main domain,
both selection branches satisfy `baseline.allocs = selected.allocs + selected.reuses`
and `baseline.frees = selected.frees + selected.reuses`, including arbitrary
independent sufficient fuel. The free equation also holds after both actual
shared releases complete. `Recursion/Allocation.lean` composes these laws
using the original source premises and projects back to the unchanged R2
endpoint. Twelve new fences retain the existing trust basis.

R4 extracts the existing IxIR₁ shared-reference potential into
`IxIR1/RcPotential.lean`, retaining its public names and original cost proofs.
`IxIR2/CostObservations.lean` proves actual heap-operation RC charges and peaks:
deep release conserves `rcops + pendingRC`, while each retained heap reference
adds two. Heap history preserves pending references, so the charge equation
gives equal raw RC increments for ordinary corresponding steps. The hot macro
performs no selected RC work; the cold macro retains the same fields and
decrements the same owner as the baseline. `CostDelta` attaches these facts
independently to the existing compiler macros and their whole-run invariant.

`IxIR2/CostSteps.lean` proves the exact peak update for every successful step,
including internal application heap work. Recorded peaks and RC counters never
decrease. `runMachine_prefix_costs` bounds every intermediate state of an actual
successful execution. `IxIR2/PipelineCosts.lean` compares every selected prefix
with the actual physical baseline, covering RC counts, recorded peaks, and live
nodes inside synchronization macros. Both selection branches and independent
sufficient control and heap budgets are included.

`Recursion/Costs.lean` adds `selected.rcops ≤ baseline.rcops` and
`selected.peakLiveNodes ≤ baseline.peakLiveNodes` to the same source premises,
value relation, and shared-result domain. The same actual reclamations retain
these bounds, empty balanced heaps, and R3's free equation. Its projection
recovers R3's unchanged source endpoint. Seventeen new fences retain the
existing trust basis; no additional rewrite-shape or compiler-state premise
narrows the domain. The bounded static unique endpoint is described below,
and [native unique reversal](source-native-unique.md) carries its Word subset
through byte-memory execution. [General credit refinement](credit-refinement.md)
now supplies a separate full-language execution bridge; wider native heap
selection remains a separate obligation.

## Reuse through suspended direct calls

R5 introduces explicit `call-local/0` and `suspended-direct-calls/1` policies.
The original runner remains exactly v0. V1 saves caller credits in the return
continuation through direct `call`/`callSelf`; the callee starts with no credits.
`ReservationOwnership` ranges over the active frame and every continuation,
proving unique locations and exclusion from live heap slots. Primitive heap
operations, ordinary steps, and call suspension preserve it. Actual execution
prefixes derive ownership and the account
`live + frees + presentReservations = allocs` from the empty initial machine.

The checked `CallReuse` pass replaces the exact shared consuming prefix and
allocation around a nonempty direct-call sequence. Its simulation is organized
into heap correspondence/order/shape, control and continuation correspondence,
ordinary operation/call/return proofs, accepted prefix inversion, and whole
finite execution. A growing location map relates fresh baseline allocations
to reused target slots. Ownership of reservations is derived from actual
target steps at each synchronization point. Heap transitions independently
carry allocation-event equality and RC/peak cost deltas.

`CallReuse.Sim.simulate_to_halt` follows the actual successful baseline trace,
including nested calls, allocations, PAP application, and residual dispatch.
The initial compiler ownership and closure facts are derived by the common
lowering interface. `Selection.mainSimulation` and `PipelineCallReuse.lean`
therefore preserve the established heap/value relation, shared reclamation,
R3/R4 counter laws, and all-prefix bounds for the actual selected program,
including v0 fallback and independent sufficient budgets.

The [source-map endpoint](source-call-reuse.md) checks the literal erasure of a
valid generic Ixon list recursor and specializes its closed Nat-map schema.
`MapRecoverySim.lean` proves eager and direct evaluation for all finite input
lists in that schema. `MapCompilation.sourceRefinesWithCostLaws` composes this
with ordinary ownership lowering and the selected physical backend under only
the original source sharing/oracle/success premises. Outer fallback retains
the literal owned source result and its reclamation. Comparative costs use the
specialized program's checked physical baseline. Twenty-five new fences retain
the existing trust basis; neither the source theorem nor the generic compiler
simulation is established by executing the finite fixture matrix.

## Static unique source reversal

[`UniqueReuse.compile`](../Compilatrix/UniqueReuse/Pipeline.lean) checks an
explicit closed Ixon entry using `recursor-modes/1`. The extension checks
saturated rule telescopes and source usage; mode evidence connects the actual
source binders and constructor fields to canonical recursor-instance bytes.
The recognizer checks the complete erased source schema before specializing
its known builder. `UniqueReverseSim.lean` proves literal and direct results
for every finite Nat list accepted by this schema.

`LoweredSim.lean` derives execution and exact ownership of the consuming IxIR₁
artifact. `UniqueLower.Translation` is indexed by that artifact and retains
full target validation. `Translation.forwardSimulation` covers any successful
indexed input execution and either target interpretation, relating both to
the same pure value graph. Static selection checks liveness, layout, and the
complete rewritten program. Credits are consumed within each loop iteration,
so the existing `call-local/0` semantics suffices.

The target proof is split into heap operations, exact machine steps, arbitrary
accumulator loops, input construction, full-main execution, and resources.
`Target.mainSteps` establishes the actual generated CFG from the empty heap.
`Target.prefixResources` derives distinct reservation ownership, empty-slot
exclusion, allocation balance, zero RC, and live/peak bounds for every physical
prefix. The final list view proves full release even when in-place reversal
introduces links toward later allocations. Control and heap budgets are
independent; main execution needs no heap fuel, and release uses `2n + 1`.

`Compilation.sourceRefinesWithCostLaws` composes these results using only the
established source oracle, sharing, and successful-evaluation premises.
It includes consuming IxIR₁ execution and release in every branch, plus actual
baseline/selected target execution and exact comparative costs when translation
succeeds. Optional reuse failure selects the checked baseline; target failure
retains the consuming artifact. Twenty-four theorem fences preserve the
existing trust basis. The [source unique record](source-unique-reuse.md)
specifies the source domain, counter equations, and independent artifact gate.

## Acceptance gates

The [bounded native reversal](source-native-unique.md) extends the actual unique
selection through a permissioned byte-memory arena. Straight-line effects are
propositions about the existing x86 evaluator; explicit block lookup and
terminator lemmas assemble the complete main and release loops. Descending
input and ascending accumulator intervals prove finite disjoint ownership.
The source theorem relates its actual returned native graph to the same
schema-indexed source value, and native counters agree with the selected
physical IxIR₂ result. Both calls terminate without any trapped prefix and
preserve saved registers and bytes outside the arena. Nine new axiom fences
retain the existing trust boundary. [E2](x86-stream-objects.md) now certifies
production text and ELF interpretation and composes the parameterized N2
source endpoint through actual object execution. ISA and system linker/loader
assumptions remain separate.

A simulation stage is complete only when:

- the executable pass output is connected to its relational premise by a
  proof-producing validator or a direct compiler theorem;
- every admitted source constructor has a semantic proof case;
- unsupported cases are rejected before execution, not silently related;
- theorem axiom audits and the complete Nix check surface remain green;
- the roadmap names the next missing relation invariant precisely.

## Closed borrowed-call translation validation

The [B1 attachment](source-borrow.md) checks the exact unary shared
caller/callee rewrite and preserves owned dynamic-entry wrappers. Its new
semantic boundary is finite closed-program translation validation: the
checker itself executes the original Ixon source and the actual baseline and
selected physical IxIR₂ programs. It packages producer equations, equal Nat
results, complete reclamation, strict actual RC improvement, and the declared
peak-live-node bound. `IxIR2.Borrow.Execution.steps` turns each successful
runner equation into its complete finite small-step execution.

`Borrow.Improved.sourcePreservation` and `resources` expose those facts for
the compiled source attachment; `Borrow.Selection.valid` and `fallbackExact`
retain the last checked artifact on optional failure. No simulation callback
is supplied by a caller. The source family covers both branches of a shared
constructor reader and zero through eight acyclic forwarding functions.
This finite certificate retains its closed scope. The B2 extension below
supplies an open-family proof; recursive SCC summary soundness remains outside
both. The existing baseline, credit-refinement, and native unique-input
theorems keep their current scope.

## Structural runtime borrowing

[B2](source-borrow-runtime.md) recognizes the actual erased source graph and
every inferred baseline/borrowed reader, forwarding body, repeated read, and
owned wrapper. Inductive shape witnesses carry every callee lookup and derive
source application and target small-step execution. The selector consumes
neither runtime arguments nor a function-simulation callback.

`Open.Entry.steps` handles arbitrary caller/resume continuations. Borrowed
paths use `StableSteps`, whose prefix theorem preserves the entire store,
including aliased lender refcounts, constructor views, and later reset facts.
The owned wrapper releases its argument only after the borrowed result returns.
Heap-worker retain/release cancellation isolates exactly two baseline RC
ticks. `Entry.total` obtains deep-release fuel from the existing root-ownership
and allocation-order reclamation theorem, yielding equal final stores modulo
those ticks, complete reclamation, and unchanged saved peak. `runFunctions`
exposes the corresponding actual evaluator equations.

`Runtime.Certified.sourceToRuntime` projects the validated compiler's erasure
certificate and composes `Sim.apply_sim_inlineSharing` with checked source
shape induction and both target runners. The original successful source
application, sharing well-formedness, oracle relation, and represented argument
remain explicit premises. The target heap relation needs the observed outer
tag/arity and whole-heap input ownership; the ignored payload can be arbitrary.
The theorem covers every admitted input, beyond the finite direct/PAP and
aliased-lender regression matrix. Fifteen fences expose the unchanged logical
and addressed-source hash basis.
