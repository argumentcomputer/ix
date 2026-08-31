# Simulation scaling strategy

Decision record, 2026-08-14. This is the proof architecture for growing the
Ixon→IxIR₀ erasure theorem and for starting the distinct IxIR₀→IxIR₁ memory
simulation. It exists to keep new syntax cases from doubling
`Compilatrix/Sim.lean` through copied evaluator inversions.

## Non-negotiable theorem boundaries

There are two simulations, with different relations:

1. **Ixon → IxIR₀** relates a typed/table-indexed source evaluation to pure
   erased values. Its hard problem is which source arguments and environment
   slots disappear.
2. **IxIR₀ → IxIR₁** relates pure values to roots in an explicit heap. Its hard
   problem is ownership, aliasing, reclamation, and location renaming.

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
   `OracleRel` stays an explicit theorem premise and is threaded through the
   IxIR₁ progress composition. The old general neutral-to-erased clause is
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
Remaining relation work is the typed higher-order/broader dropped-occurrence
frontier; separately, real IR content addressing must retire `memberAddr`.

## Starting IxIR₀ → IxIR₁

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

The compiler induction has now begun in `IxIR1/LowerSim.lean`. Held `VEnv`
entries realize exact roots through in-bounds absolute slots, and runtime
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
the intentionally excluded allocation/free/reuse counter differences.

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

Implementation order: graph/root relations and all primitive ownership
interfaces through reuse/fetch (landed) → result `Owned` in declarations and
the first call-result contract (landed) → exact call/case preservation
(landed) → induction over the actual lowering derivation (active) → whole-program
declaration correspondence.
Lambda lifting and paps activate only after constructor data and direct calls
are proved.

## Acceptance gates

A simulation stage is complete only when:

- the executable pass output is connected to its relational premise by a
  proof-producing validator or a direct compiler theorem;
- every admitted source constructor has a semantic proof case;
- unsupported cases are rejected before execution, not silently related;
- theorem axiom audits and the complete Nix check surface remain green;
- the roadmap names the next missing relation invariant precisely.
