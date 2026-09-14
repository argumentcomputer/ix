# Kernel verification

`Ix.Kernel` is the production Lean checker. `Ix.Kernel.Verify` contains its
implementation proofs; `Ix.Compile.Verify` contains the Lean-to-Ixon compiler
proofs. Their named specification and reference implementation lemmas are local
under `Ix.Theory.Named`. Building or checking them requires no external
formalization repository.

Certified acceptance has model-construction and relative consistency theorems,
with a concrete set-model construction in the separate Mathlib package. A
direct theorem also connects a fragment of production `checkEnvAnon` to that
semantics. Extending this connection to all paths of the ordinary Lean checker
requires the remaining production-refinement proofs described below.

The [recursion audit](kernel-recursion.md) explains the production call graph
and fuel bounds. The [context-digest guide](tc-context-digest-collision-boundary.md)
details the collision and suffix-transport assumptions for cache soundness.

## Connection to the consistency model

The named specification and the set model share `Ix.Theory.VLevel`. The
[model foundation](theory.md) and its audit are independent of the named
development. The separate [Mathlib package](../Models/SetTheory/README.md)
constructs `Ix.Theory.Model.SetTheory` on `ZFSet` from a countable strictly
increasing sequence of strongly inaccessible cardinals.

`Ix.Kernel.Verify.Consistency` proves the following direct connections:

- Production universe equality and ordering agree with model evaluation,
  under the existing finite address-faithfulness and arithmetic bounds.
- A structural reader maps kernel expressions to model syntax, resolves
  addresses to explicit store references, preserves projections and natural
  literals, substitutes let values, and expands strings through the canonical
  character and list primitives. This closed reader excludes free
  variables and unresolved addresses. The binder reader
  `readScopedExpr?` maps registered free variables to model context indices;
  unknown locals and loose legacy variables fail that reader. Its let and
  string readings commute with binder opening, abstraction, term substitution
  and universe substitution, including nested occurrences.
- `StringExpansion.read_of_run` proves that production string expansion returns
  the literal's model reading and preserves intern-table coherence. All
  intermediate allocations are derived from the string: eight fixed nodes
  and four per character. One collision condition covers this explicit list
  and the initial table. The primitive table must be canonical and its
  references resolvable; semantic admission of those primitives is separate.
- Hash equality and intern-table reuse preserve that reading under their
  stated address/key collision assumptions. Metadata cannot change it.
- `inferUncached_sort_sound` interprets an actual successful execution of the
  production sort-inference branch. It proves the model typing postcondition
  for the returned type, including intern-table reuse.
  `infer_sort_cached_sound` derives the same typing when the eligible cached
  value is the canonical successor sort.
- `instantiateUnivParams_readAnnotated` connects the actual memoized universe
  substitution walker to model substitution for every readable expression.
  Simplifying `max` and `imax` may change the returned syntax; the proof
  preserves both interpretation and hereditary validity, including beneath
  binders and through let substitution. The empty-argument shortcut is
  justified by the source type's universe scope.
- `instantiateUnivParams_readAnnotated_scoped` also proves scope and reference
  preservation for the actual returned type. Scope comes from the successful
  substitution and scoped arguments; semantic level equivalence alone would
  not exclude an out-of-range parameter in a simplified expression.
- `inferUncached_const_sound` and `infer_const_sound` derive model typing for
  polymorphic constant references with arbitrary readable declaration types.
  Production success supplies the universe-arity check. The premises retain
  a well-formed model interface, agreement with the actual lazy-loaded
  declaration, finite interning and level-substitution resources, and (for
  `infer`) misses in every eligible cache partition at the computed key.
  Full mode imposes no condition on the ignored inference-only partition.
- `ModelTyping.no_false` rules out a closed model-typed kernel expression at
  primitive False when its environment has been admitted by the certified
  interface and the set-theory assumption has an instance.
- `BinderInference.sound` follows finite production inference trees for sorts,
  locals, polymorphic constants, applications, dependent functions, and
  full-mode lambdas. `LocalContextReading.push`
  and `openBinder_sound` connect actual declaration lookup and fresh-variable
  opening to the model's dependent context. Singleton abstraction closes the
  resulting function type, and the simplifying `imax` constructor preserves
  its universe interpretation.
- `BinderInference.synthesis` derives full typing for application spines
  headed by a local or an admitted constant. The function's type
  supplies hereditary validity of its domain, so arguments may be checked
  lambdas. Faithful hash conversion identifies the argument's inferred type
  with that domain, with matching occurrence annotations.
  `subst_readScopedExpr?` connects the actual memoized and interned codomain
  substitution to model substitution, including active locals and nested binders.
- `instantiateUnivParams_readScopedAnnotated` brings the actual substituted
  declaration type into any active local context, preserving its closed term
  scope and occurrence annotations. `infer_const_scoped_annotated` uses this
  result for polymorphic references in binder trees. A pure substitution and
  syntax-reading check fixes the tree's result annotation; the admitted model
  and actual execution establish typing. Runtime success supplies arity, while
  scoped arguments also give scope of the returned type.
- `FVarInferenceSupport.sound` handles both local-variable cache partitions
  when a cached answer equals the current declaration's concrete type. These
  are structural cache checks, with no assumed semantic typing of cached data.
- `CachedConstantInferenceSupport.sound` brings monomorphic and polymorphic
  constant hits into binder trees. The selected cached value equals pure
  universe substitution of the current loaded declaration, whose type agrees
  with the admitted entry. Pure substitution establishes semantic congruence,
  including simplifying levels, without mutable interning resources.
  `InferenceCacheHit.run` proves the exact cache selection and returned state;
  full results take priority, and inference-only results require that policy.
  `infer_const_cache_write` establishes substitution agreement for a successful
  miss's insertion.
- `InferenceCacheAgreement` records the expected concrete value in both
  partitions at one key. Sort inference and inference of an already-loaded
  constant preserve this agreement at their own key and leave other keys and
  loaded declarations unchanged. The miss proofs use the actual interning or
  universe-substitution operation and its final cache write.
  `PreservesInferenceCache` composes structural preservation through key
  computation, interning, binder opening, unrelated writes, and scope/policy
  cleanup, including errors. Cache clearing establishes empty-cache agreement.
  `CachedConstantInferenceSupport.transport` reuses a closed constant witness
  after such a frame; `BinderInference.sortOfAgreement` constructs a sort leaf
  from maintained agreement. Initial agreement and finite execution resources
  remain premises. General preservation through lazy loading, environment
  extension, and all recursive paths remains open.
- `InferenceCacheTrace.frame` carries preservation through finite recursive
  application, forall, and full-mode lambda trees. The trace computes the keys
  written by misses, including recursive calls and the final outer insertion;
  hits contribute no writes. Entries outside this footprint, loaded declarations,
  and checking policy survive the entire successful call. The proof accounts
  for lambda domain validation, binder cleanup, and hash conversion's optional
  statistics update. `CachedConstantInferenceSupport.afterInference` transports
  a closed constant witness through that call, and `BinderInference.sortAfterInference`
  constructs a later sort leaf from preserved agreement. Neither needs another
  cache-hit observation after the call. The operational tree and exclusion of
  the protected key from its writes remain explicit inputs.
- `checkEnvAnon_atomic_preserves_model` connects a supported production
  environment run to model extension. `checkEnvAnon_atomic_no_false` excludes
  a declaration at an axiom type interpreted as empty, including False.
- `LocalContextValues` includes the stored values of let-bound free variables.
  Its reader recovers the existing scoped reader when all locals are ordinary
  variables. Actual binder and let opening preserve the reading, complete
  local lookup, the bound on allocated identifiers, and intern-table coherence.
  A let leaves the model context unchanged; a regular binder lifts older
  readings into the extended context. The production free-variable inference
  branch is typed by this invariant, and its zeta-reduction step preserves the
  model value. The memoized abstraction-and-substitution sequence closes a
  let body's inferred type with exactly its original model reading and
  preserves intern-table coherence. The residual abstraction is derived from
  that reading, including nested lets and other local values. General
  inference must still supply the let value's typing; cheap beta, general
  reduction, legacy local frames, and semantic cache preservation remain
  separate obligations.
- `LetInferenceTrace.of_success` extracts the complete production let trace
  in either validation mode, including computed sort exposure, conversion,
  opening, recursive body inference, the deterministic closing sequence, and
  final scope cleanup. It requires no precomputed execution tree. Under the
  local-state and finite walker invariants, the trace transports the recursive
  body's typing to the original let and its substituted type before cheap beta.
- Local scope restoration preserves the ordered declarations and every index
  lookup without requiring equal hash-map representations. Fresh extensions
  compose, and actual scope cleanup restores the caller's context on success
  and failure. The let trace recovers `LocalContextValues` after validation;
  the inference cache shell preserves caller contexts whenever its uncached
  body does. `LocalStateInvariant` derives freshness from the live identifier
  bound, and `infer_framesLocalState_of_whnf` preserves it for all constructors and
  both policies, including hits, writes and failure states. Recursive
  inference, reduction and conversion remain contracts of the mutual execution
  proof. Projection inference's parameter/field loops, Prop checks and lookups
  derive their state effects from the same recursive inference and reduction
  contracts. `TcM.InternOnly.instantiateUnivParams`
  proves the actual universe walker's exact intern-table-only effect without
  collision assumptions; the named inference-policy proof shares this result.
  These structural frames do not establish computed-type or cache semantics.
- `IngressM.FramesState.ingressAnonAddrShallow` proves that the actual anonymous
  loader changes only declarations, block membership and intern tables on
  either outcome. Conversion, lazy lookup and block publication preserve every
  checker-owned field, including the fresh-variable counter and all caches.
  `LocalStateInvariant.newLazyAnon` consequently establishes the structural
  invariant for the concrete driver without assuming its loader's effect.
  Lean's expression and universe converters now use finite range loops whose
  work counts come from the source syntax. An active sharing set rejects
  cycles; the Rust converter checks the reachable sharing graph before its
  traversal. Forward references and unused cyclic entries remain accepted.
  Regressions cover cycles, partial-failure state, repeated/forward sharing,
  deep inputs and universe simplification. The state proof does not establish
  conversion's semantic reading or prove that the computed bound suffices for
  every acyclic input; those remain distinct refinement obligations.
- `InferenceCacheInvariant` covers every entry in both production maps, with
  separate full-checking and inference-only meanings. Hits obtain stored facts
  directly; each insertion establishes its own fact and preserves all other
  entries. Key computation, interning, local scopes, policy changes and reset
  preserve the invariant. The actual lazy driver starts with empty caches;
  failed declaration checks restore the incoming maps, and periodic clearing
  preserves validity. The remaining successful-body preservation obligation is
  explicit. These structural laws have a parameterized cache meaning; the
  general mutual semantic proof must instantiate it and discharge that obligation.
- Safe definitions cannot cite themselves in their types or values. Definition
  blocks compute a dependency order for their safe members before checking any
  member. `DefinitionOrder.block_wellFounded` and `block_no_cycle` derive the
  absence of every internal safe-definition cycle from actual block success.
  The order includes every safe declaration loaded at a member key; callers
  supply no order or rank certificate. Acyclic references between block members
  remain supported. This closes the host acceptance of hash-verified circular
  definitions, theorems, and opaque definitions. The guest already rejects safe
  `recur` references at ingress, including acyclic peer references; that policy
  difference remains explicit. External dependency ordering, cache provenance,
  and general model preservation remain separate obligations.

`ModelTyping.no_false` assumes semantic typing; the production fragment below
derives it for its supported paths. Full checker refinement still requires the
remaining inference and conversion cases, cache invariants, address-to-store
resolution, and declaration admission. The named-calculus proofs provide
support for these obligations.

## Production environment fragment

The axiom policy is relative: **every model of the source axioms extends to a
model of the checked environment, preserving the axiom interpretations**.
The initial interface contains exactly the source axioms, retaining their
declared universe arities. Their types have no free term variables, use only
their declared universe parameters, and refer only to that interface.
A `Realizes` witness supplies a model of
these axioms. The hypothesis is model existence; a theorem connecting
arbitrary syntactic consistency to model existence is outside this result.

The fragment covers monomorphic standalone definitions, theorems,
and opaque definitions whose values are closed universe terms, references to
preceding interface entries, monomorphic specializations of polymorphic
constants, or closed function bodies in the binder fragment. Referenced types may contain
dependent functions and other readable expression forms. Examples include:

```lean
axiom P : Prop
axiom p : P
def q : P := p
theorem r : P := q
def typeAlias : Type := Prop
axiom ident.{u} : (α : Sort u) → α → α
def propIdent : (α : Prop) → α → α := ident.{0}
def idProp (P : Prop) (p : P) : P := p
def useId (P : Prop) (p : P) : P := idProp P p
def applyProp (P Q : Prop) (f : P → Q) (p : P) : Q := f p
def usePoly (P : Prop) (p : P) : P := ident.{0} P p
def chooseLeft (P Q : Prop) (p : P) (q : Q) : P := p
axiom T.{u} : Sort u
axiom f.{u} : T.{u} → T.{u}
def useF (x : T.{1}) : T.{1} := f.{1} x
```

`AtomicEnvironmentFragment` records the precise execution boundary:

- Every source key occurs in the `buildAnonWork` result, and every work item
  represents an axiom or a definition. Lookup, routing, and reset witnesses
  identify the checked `KConst`.
- Application, forall, and lambda nodes in the inference witnesses miss every
  eligible cache partition. Full mode may have a populated inference-only
  partition. Sort nodes use a miss or a hit equal to the canonical successor
  sort; a maintained agreement can construct that leaf's cache observation.
  Local-variable hits must match the current production declaration type.
  Constant nodes use either the existing miss rule or a selected cache hit.
  A hit checks the loaded declaration, universe arity, finite level resources,
  and equality of the cached value with pure substitution of its type.
  Its arity agreement is explicit because no runtime arity guard executes.
  A miss's lookup agrees with an already admitted type and universe count. A specialization supplies
  closed universe arguments and finite interning/substitution resources at
  the actual post-lookup state. The occurrence annotations on the declared
  type agree with the substituted entry's annotations. These are structural
  data checks; successful inference derives typing, scope, and references.
  Ordinary aliases retain the simpler empty-substitution path. Sort misses
  retain finite interning coherence and address-faithfulness premises.
- Cache agreement covers both partitions so it survives policy changes.
  Closed constant witnesses can be transported through composed frames that
  preserve their key's entries and the loaded-constant map. Actual sort and
  already-loaded constant inference provide frames for other keys. These
  results reduce repeated witnesses; they do not yet derive initial agreement
  or preservation through lazy loading or environment extension.
  A separate `InferenceCacheTrace` derives a frame for an entire supported
  recursive call at any key outside its computed writes. It shares the existing
  application and binder execution traces and additionally follows lambda-domain
  inference. Constant misses require already-loaded declarations and finite
  universe-walker resources; applications use full mode and hash conversion.
  The operational trace can frame any selected cache hit, while semantic typing
  of composite hits remains outside `BinderInference`.
- Binder definitions supply finite inference trees for both the value and its
  separately checked declared type, exact source readings, closed annotated
  syntax, and references to the preceding interface. Recursive calls use the actual
  smaller method table. Binder-opening and abstraction resources cover fresh
  ids, context preservation during domain inference, intern-table coherence,
  finite collision freedom, and bounds preventing index overflow. Sort
  exposures are syntactic; lambdas use full mode and the unchanged cheap-beta
  path. `CheckingClaim` derives body validity and membership once declared-type
  inference establishes hereditary validity. No codomain-typing premise is
  added to the production proof.
- Applications use full mode, syntactic Pi exposure, an ordinary argument
  without an eager-reduction marker, and the hash-equality conversion path.
  Their witnesses retain the actual recursive calls, context preservation
  during function inference, and finite substitution resources. Function
  spines start with locals or admitted constants. Polymorphic constants supply
  lazy-lookup agreement on misses or loaded-declaration agreement on hits, a
  closed scoped reading of the selected entry's type, and finite
  universe-substitution resources. Their result type is fixed
  by a pure `readInstantiatedType?` check with the substituted occurrence
  annotations, including when levels simplify. Monomorphic references retain
  their simpler empty-substitution rule. Applying a lambda directly and
  reduction to expose a Pi require further refinement.
- Conversion takes the initial hash-equality path, with faithfulness of the
  compared expressions. General reduction and conversion caches are outside
  this fragment.
- Definitions are added in dependency order with fresh references. Their
  observations use the states reached in the original serial work order,
  including cache clearing. `AtomicDefinitionRun.no_self_alias`
  proves that a fresh definition cannot justify its own type by referring to
  itself.
- `checkEnvAnon` returns `.ok results` **and every result row has no error**.
  The outer `.ok` alone does not mean that the declarations passed.

Callers must establish these operational and representation witnesses for
the run. They supply no typing or checker-soundness premise. The proof
extracts the validation, type-inference, theorem-guard, value-inference, and
conversion steps from public success, then derives body typing to extend
the preceding model. General automatic witness construction, broader application and
lambda paths, lets, inductives, coordinated blocks, and other
conversion paths remain outside the fragment. Polymorphic constant inference is composed into declaration
admission and model extension for the monomorphic specializations described
above. Definitions with their own universe parameters remain outside this
environment fragment.

`checkEnvAnon_atomic_represents_source` ties every source address to an
interface with the type and body reached by production lookup. The independent
serialized-Ixon reader refinement remains a separate boundary.

The no-False corollary assumes the designated false type is empty in the
initial axiom model. Extension preserves that value, so no resulting
declaration can inhabit it. No axiom-name restriction is needed.

## Trust checks

The audits traverse checked declaration types and bodies, including inductive
constructors. They compare exact axiom sets and record direct origins of
`sorryAx`. Full traversal includes implementation assumptions and unfinished
metatheory. The named-specification audit checks 441 assertions against exact
dependency manifests.

The same traversal covers 2,034 kernel manifest roots. Direct dependency
lookups are cached within a fixed environment, while each root's reachable
declarations, axioms, and proof-hole origins are computed separately.

`Ix.Kernel.Frontier.Pending` quarantines the remaining explicit metatheory
axioms. Completed roots cannot depend on that namespace. Named-specification
proof holes and implementation bridge axioms are tracked separately from
Lean's logical axioms and generated native proofs. No direct consistency root
permits a proof hole or a metatheory/implementation bridge axiom. The context
hash and content-address hash use kernel-checked proofs of their 32-byte output
bounds on both platform sizes.

Run the complete local certification gate:

```sh
lake run check-kernel --with-model
```

It combines the following checks. Omit `--with-model` to skip the separate
Mathlib package. Ordinary PR CI covers the root checks in its build, theory,
and test jobs. The model has a separate workflow triggered by changes to the
package, interface, or configuration; the merge queue adds the expensive
parity corpus.

```sh
lake build IxKernelVerify IxCompileVerify
lake build --wfail IxKernelConsistency
lake run check-theory
lake run check-certified
lake test --wfail -- tc-unit
lake -d Models/SetTheory build --wfail
```

The consistency target checks 177 exact theorem boundaries. The production
environment roots retain four existing generated output-length proofs,
reached through expression/universe construction, names, and the full
production method table. They introduce no new native proofs. The model
extension lemma and `ModelTyping.no_false` use only `propext`,
`Classical.choice`, and `Quot.sound`, with set theory as a hypothesis.
The production roots additionally forbid the abstract
`CheckSuccessSound`/`SupportedCheckFragment` interfaces and the independent
certificate validator in their dependency closures.

The polymorphic inference, substitution, and binder inference roots retain only the two existing
expression/universe output-length proofs, alongside the standard Lean axioms.
Their model-side level congruence introduces no native proof dependency.
Semantic checking against a formed type also uses only standard Lean axioms.
Kernel unit regressions cover lazy loading, both inference policies, interning
reuse, dependent function types, shared references, lets, `imax` simplification,
argument order, and rejection of wrong arities and out-of-range parameters.
Environment regressions additionally check Prop/Type specializations,
transitive aliases, nested references, simplified declaration types, cache
clearing, and admission failures for wrong arities, open parameters, and a
mismatched declared specialization.
Function-body regressions cover calls to earlier Prop/Type identities,
transitive theorem calls, local functions with distinct domains and codomains,
dependent result families, lambda arguments, exact local results through cache
reuse and scope cleanup, and rejected argument/function types.
Polymorphic-call regressions include Prop/Type instances in real function
bodies, `max`/`imax` simplification inside Pi domains, closed nested references
under active locals, separate cache keys for different universe instances,
and rejected universe arities and argument types.
Constant-cache regressions cover repeated carrier references within declared
types and bodies, including per-item cache clearing; full and inference-only
reuse across fresh local scopes; monomorphic and simplifying substitutions;
partition priority; and alternating universe instances. Deliberately different
values in an ineligible partition make the selection tests observable.
Cache-preservation regressions add repeated sort domains, sort reuse and
partition priority, preservation through intervening sort and loaded-constant
inference, successful and failed scope cleanup, policy restoration, and
fresh inference after clearing both partitions.
Recursive preservation regressions retain warm sort and constant entries
through dependent types in both policies, nested lambda applications, and
applications with lambda arguments. They also check reuse of the whole cached
result, statistics updates during hash conversion, an existing outer local
scope, and nested polymorphic declarations with persistent or cleared caches.

## Certified host adapters

The certified source and claim adapters are maintained under
`Ix.Certified`, with explicit certified entry points in `Ix.Kernel`.
`ClaimCommand.run_meaning` connects successful source validation to the exact
versioned envelope and its semantic meaning. A closed logical receipt
constructs its model and excludes a checked subject of the profile's false
type under the set-theory hypothesis.

Run `lake run check-certified` for the exact 86-root foundation audit and
native/CLI regressions against the locally preserved adapter evidence. The audit
permits only the three standard Lean axioms in these roots and inventories
the separate BLAKE3 and native execution boundaries. See
[the command interface, theorem contracts and evidence](certified-checking.md).

Aiur execution of the host validator remains a separate proof obligation.
The VM pilot is preserved in the frozen archive and excluded from the host gate.

## Review entry points

| Area | Entry point |
| --- | --- |
| Certified checker contracts | [`Ix/Kernel/Certified.lean`](../Ix/Kernel/Certified.lean), [`CertifiedClaims.lean`](../Ix/Kernel/CertifiedClaims.lean) |
| Direct production refinement and its audit | [`Ix/Kernel/Verify/Consistency.lean`](../Ix/Kernel/Verify/Consistency.lean) |
| Polymorphic inference and universe substitution | [`Consistency/Constant.lean`](../Ix/Kernel/Verify/Consistency/Constant.lean), [`InstUniv.lean`](../Ix/Kernel/Verify/Consistency/InstUniv.lean), [`Model/LevelCongruence.lean`](../Ix/Theory/Model/LevelCongruence.lean) |
| Polymorphic calls inside binders | [`Consistency/ScopedConstant.lean`](../Ix/Kernel/Verify/Consistency/ScopedConstant.lean), [`ScopedInstUniv.lean`](../Ix/Kernel/Verify/Consistency/ScopedInstUniv.lean) |
| Constant cache selection, writes, and typing | [`Consistency/ConstantCache.lean`](../Ix/Kernel/Verify/Consistency/ConstantCache.lean) |
| Cache invariants and sort cache typing | [`Consistency/InferenceCache.lean`](../Ix/Kernel/Verify/Consistency/InferenceCache.lean), [`SortCache.lean`](../Ix/Kernel/Verify/Consistency/SortCache.lean) |
| Recursive cache preservation and witness reuse | [`Consistency/RecursiveCache.lean`](../Ix/Kernel/Verify/Consistency/RecursiveCache.lean) |
| Complete inference-cache maps and driver lifecycle | [`Consistency/CacheInvariant.lean`](../Ix/Kernel/Verify/Consistency/CacheInvariant.lean), [`CacheLifecycle.lean`](../Ix/Kernel/Verify/Consistency/CacheLifecycle.lean) |
| Finite intern support and production string expansion | [`Consistency/InternInvariant.lean`](../Ix/Kernel/Verify/Consistency/InternInvariant.lean), [`StringExpansion.lean`](../Ix/Kernel/Verify/Consistency/StringExpansion.lean), [`StringReading.lean`](../Ix/Kernel/Verify/Consistency/StringReading.lean) |
| Dependent binders and function bodies | [`Consistency/BinderInference.lean`](../Ix/Kernel/Verify/Consistency/BinderInference.lean), [`Application.lean`](../Ix/Kernel/Verify/Consistency/Application.lean), [`BinderOpening.lean`](../Ix/Kernel/Verify/Consistency/BinderOpening.lean), [`Context.lean`](../Ix/Kernel/Verify/Consistency/Context.lean), [`Model/Checking.lean`](../Ix/Theory/Model/Checking.lean) |
| Let-bound values, local allocation and shared context coherence | [`Consistency/LocalValues.lean`](../Ix/Kernel/Verify/Consistency/LocalValues.lean), [`LocalOpening.lean`](../Ix/Kernel/Verify/Consistency/LocalOpening.lean), [`Verify/LocalContext.lean`](../Ix/Kernel/Verify/LocalContext.lean), [`Model/ContextTransport.lean`](../Ix/Theory/Model/ContextTransport.lean) |
| Local substitution, let-inference traces and closing inferred types | [`Consistency/LocalSubstitution.lean`](../Ix/Kernel/Verify/Consistency/LocalSubstitution.lean), [`LetInference.lean`](../Ix/Kernel/Verify/Consistency/LetInference.lean) |
| Observable local-context restoration and inference frames | [`Verify/LocalScope.lean`](../Ix/Kernel/Verify/LocalScope.lean), [`Consistency/LocalScope.lean`](../Ix/Kernel/Verify/Consistency/LocalScope.lean) |
| Production environment fragment and relative axiom policy | [`Consistency/Environment.lean`](../Ix/Kernel/Verify/Consistency/Environment.lean), [`Production.lean`](../Ix/Kernel/Verify/Consistency/Production.lean) |
| Safe definition self-reference and block dependency order | [`DefinitionOrder.lean`](../Ix/Kernel/DefinitionOrder.lean), [`Consistency/DefinitionOrder.lean`](../Ix/Kernel/Verify/Consistency/DefinitionOrder.lean) |
| Foundation assumptions, theorem contracts, and provenance | [Consistency model guide](theory.md) |
| Host commands, receipts, and frozen regression evidence | [Certified checking guide](certified-checking.md) |
| Concrete set-theory instance | [Separate model package](../Models/SetTheory/README.md) |

## Source inventory

The named development retains 104 source modules, including the inductive
fixtures used by the existing proofs. Source hashes and attribution are in
[`Ix/Theory/Named/NOTICE`](../Ix/Theory/Named/NOTICE) and
[`Tests/Theory/NamedManifest.lean`](../Tests/Theory/NamedManifest.lean); the
Apache license is preserved alongside the sources. The axiom-audit helper
and direct production-fragment proofs are authored in Ix.
`Model/LevelCongruence.lean` and `Model/Checking.lean` are Ix-authored mathematical
additions, listed
separately from the imported files in the theory provenance manifest.
