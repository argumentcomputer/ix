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
  literals, and substitutes let values. This closed reader excludes free
  variables, unresolved addresses, and string literals. The binder reader
  `readScopedExpr?` maps registered free variables to model context indices;
  unknown locals, loose legacy variables, lets, and strings fail that reader.
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
- `DefinitionBodyTrace.scopes` derives source scope from the type and value
  validation executed by the same production member check. It combines finite
  validation coverage and collision freedom with the closed scoped reading;
  `ConditionsScoped` checks only the auxiliary binder annotations.
  `DefinitionBodyTrace.binderSupport` uses the actual type and value inference
  calls to construct admission support, including a definition's own universe
  parameters. No semantic typing or whole-expression model scope is assumed
  by this constructor.
- `BinderInference.synthesis` derives full typing for application spines
  headed by a local or an admitted constant. The function's type
  supplies hereditary validity of its domain, so arguments may be checked
  lambdas. Faithful hash conversion identifies the argument's inferred type
  with that domain, with matching occurrence annotations.
  `subst_readScopedExpr?` connects the actual memoized and interned codomain
  substitution to model substitution, including active locals and nested binders.
- `SynthesisInference.closed_sound` derives full typing and a universe bound
  for the generated type, including direct lambda applications and applications
  returning functions. Binder bounds come from actual domain inference;
  `SynthesisTypeCheck` retains earlier executed declaration type checks across
  interface growth and universe instantiation. An inhabited dependent product
  bounds every fibre, so application preserves formation without another
  codomain inference call. The bound preserves the exact Prop condition while
  permitting a larger positive universe. `DefinitionBodyTrace.synthesisSupport`
  connects this result to ordinary declaration admission.
  `AxiomObservation.synthesisTypeCheck` extracts an axiom's type check from
  successful `checkEnvAnon` rows; `StandalonePrefix.definitionTypeCheck` extracts
  a definition's check from public declaration success.
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
  remain premises. Frames allow new declarations while retaining every
  previously loaded declaration.
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
- `getConst_standalone_cache` proves preservation for the installed production
  loader with verification enabled. Conversion accesses only intern tables;
  the initial lookup miss makes its single-entry registration fresh. Both
  inference maps, old declarations, the fresh-id counter, and all checker
  fields except the environment and fault history are retained. The proof
  includes absent sources, integrity/parse errors, partial conversion failures,
  the reserved-address guard, and fault deduplication.
- `getConst_verified_cache` extends that result to mutual-block loading.
  Block preparation accesses only intern tables, including conversion of
  inductives, constructors, and recursor rules. Publication follows the actual
  insertion fold and preserves old declarations when each converted entry
  agrees with any old declaration at its key. Fresh entries and exact repeats
  satisfy this condition; duplicate fresh keys need no uniqueness premise.
  The proof includes parent lookup failures, block deduplication, partial
  preparation failures, and lookup errors after successful publication.
  `InferenceCacheTrace.lazyConst` composes this result with universe substitution
  at the actual post-lookup state. `CachedConstantInferenceSupport.afterVerifiedInference`
  reuses an earlier witness after a constant call loads another dependency;
  recursive transport also covers loads inside application and binder trees.
  This general interface retains overlap agreement as a data premise, including
  for externally partially loaded states. Source admission and other recursive
  paths still need proofs.
- `getConst_coherent` derives intern-table key coherence through the actual
  loader on success and error. Universe and expression conversion now use
  finite step bounds computed from source syntax; their counting passes and
  conversion loops use worklists to handle deep inputs. Exhausted cyclic
  sharing returns an error with coherent partial state. The proof follows every
  conversion form, publication, and fault dispatch without collision or
  declaration-overlap premises.
  `UniverseInstantiationSupport.afterVerifiedGetConst` builds the walker's
  coherence field from the pre-load invariant. `infer_verifiedConst_coherent`
  carries it through key computation, loading, substitution, and the final
  cache write. `CachedConstantInferenceSupport.afterCoherentInference` reuses
  the earlier witness with coherence required only before the call. Finite
  collision and level resources and source agreement remain explicit.
- `getConst_owned` derives overlap compatibility from a reusable block
  invariant. `sourceOwnershipCheck` compares finite key inventories from
  verified source headers; `SourceOwnership.ofCheck` proves that acceptance
  separates different block owners and standalone/projection keys. Repeated
  keys within one block are allowed. Actual conversion emits only those
  projection keys, including constructors, and publication records their owner.
  The invariant that loaded projections have recorded blocks starts empty;
  an unrecorded block's entries are therefore fresh. It survives lookup on
  success and error, including errors after publication.
  `OwnedLazySupport.afterConstInference` retains it through key computation,
  substitution, and cache writes. `CachedConstantInferenceSupport.afterOwnedInference`
  reuses an earlier witness without per-block overlap comparisons. The source
  check is an optional proof preflight; it does not change loader admission.
  Corrupt headers are excluded because verified loading rejects them. Semantic
  source agreement, finite substitution resources, and preservation through
  other checker paths remain obligations.
- `OwnedInferenceTrace.preserves` carries ownership and intern coherence through
  a whole supported recursive call. `InferenceStateInvariant.ofCheckedSource`
  initializes both from the finite source check and the empty production state.
  Application substitution, binder opening, and lambda abstraction take finite
  collision, construction, and size data; their initial coherence is derived
  from the preceding recursive calls. Constant leaves derive their loader and
  post-lookup coherence from the same invariant. The trace recovers the existing
  cache frame outside its computed writes, transports earlier constant witnesses,
  supplies coherence for later sort leaves, and returns the state resource for
  another constant call that loads a new block. Recursive traces and finite
  walker data remain explicit. The result covers successful inference in the
  supported fragment; the general checker-state proof remains open.
- `ConversionRecipe.run_predict` connects source-only prediction to actual
  intern operations on success and failure. The recipe preserves source
  resolution, sharing caches, universe normalization, every expression form,
  and all four standalone declaration converters. Its finite candidate lists
  supply collision domains together with the initial intern table; no global
  hash-injectivity assumption is required. Correspondence proofs equate each
  recipe with the bounded production converter. `predictStandalone?` verifies
  the source and selects standalone declarations, retaining conversion errors.
  It is an optional prediction interface and changes no production loading.
- `SourceStateInvariant` adds standalone source agreement to ownership and
  intern coherence. It starts empty after the finite source check and survives
  actual lookup on both outcomes. Block loads preserve the catalog because
  ownership separates their emitted keys. `OwnedInferenceTrace.preservesSource`
  carries the combined invariant through supported recursive calls, with finite
  conversion data at constant misses. `StandaloneModelBinding` reads a predicted
  declaration's type in an already admitted model entry. Its actual lookup
  derives the type reading, arity, and post-load coherence;
  `ScopedConstantInferenceSupport.ofSource` and `infer_const_source_sound` use
  these derived facts. Static source/model bindings, finite collision and level
  data, and operational traces remain explicit. This catalog does not interpret
  mutual members or prove declaration admission.
- `SourceCacheHistory.invariant` establishes cache agreement from the actual
  empty lazy state for a finite catalog of closed sorts and standalone constant
  instances. Each populated slot has its predicted type and retains the source
  declaration that produced it. `OwnedInferenceTrace.preservesCache` follows
  recursive writes at every catalog key, using finite input collision domains
  to exclude writes by other syntax forms. Both cache partitions remain valid
  across policy changes, binder scopes, block loading, lookup errors, and cache
  clearing. `BinderInference.constFromSourceCache` and `sortFromSourceCache`
  observe the real selection and derive the existing hit/miss interfaces.
  `infer_const_history_sound` derives model typing after such a history without
  initial cache agreement, a separate cache-hit type witness, or a new lookup
  reading. The catalog, static source/model bindings, finite collision/level
  data, and recursive execution traces remain explicit. General composite and
  local cache typing, other checker operations, and declaration admission are
  still outside this result.
- `checkEnvAnon_atomic_preserves_model` connects a supported production
  environment run to model extension. `checkEnvAnon_atomic_no_false` excludes
  a declaration at an axiom type interpreted as empty, including False.

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

The fragment covers standalone definitions, theorems,
and opaque definitions, including their own universe parameters, whose values
are universe terms, references to preceding interface entries, instances of
polymorphic constants, or closed function bodies in the binder fragment. Referenced types may contain
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
def idSort.{u} (A : Sort u) (a : A) : A := a
def aliasSort.{u,v} : (A : Sort (max u v)) → A → A := idSort.{max u v}
def useSort.{u} (A : Sort u) (a : A) : A := idSort.{u} A a
def callLambda.{u} (A : Sort u) (a : A) : A := (fun x : A => x) a
def callReturned.{u} (A : Sort u) (a : A) : A := ((fun x : A => fun y : A => x) a) a
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
  A miss's lookup agrees with an already admitted type and universe count.
  For a standalone, a static `StandaloneModelBinding` and the maintained source
  invariant derive this lookup agreement from the source prediction.
  A specialization supplies
  closed universe arguments and finite interning/substitution resources at
  the actual post-lookup state. The occurrence annotations on the declared
  type agree with the substituted entry's annotations. These are structural
  data checks; successful inference derives typing, scope, and references.
  Ordinary aliases retain the simpler empty-substitution path. Sort misses
  retain finite interning coherence and address-faithfulness premises.
- Cache agreement covers both partitions so it survives policy changes.
  Closed constant witnesses can be transported through composed frames that
  preserve their key's entries and each previously loaded declaration. Actual
  sort and already-loaded constant inference provide frames for other keys. These
  frame results reduce repeated witnesses. The source-cache history additionally
  establishes agreement and loaded-declaration coverage for a finite catalog
  from empty caches, then preserves it at the catalog's written keys.
  Verified lookup supplies an extension frame on every outcome, retaining
  partial intern progress on error. The installed callback must be the actual
  verified loader. Standalone registration uses freshness from the lookup miss;
  block publication requires pointwise agreement between its prepared entries
  and any already loaded declarations at their keys. This admits partially
  loaded blocks without assuming a cache frame or a final-state invariant.
  A separate `InferenceCacheTrace` derives a frame for an entire supported
  recursive call at any key outside its computed writes. It shares the existing
  application and binder execution traces and additionally follows lambda-domain
  inference. Constant misses use already-loaded declarations or verified
  standalone/block loading, with finite universe-walker resources after lookup;
  applications use full mode and hash conversion. The general interface keeps
  dependency agreement explicit; the standalone source interface derives its
  mutable lookup facts from a static binding and finite conversion data.
  `OwnedLazySupport` derives block compatibility from a source ownership check
  and an invariant established at initialization and retained by lookup and
  supported successful recursive calls. Arbitrary partially loaded states can
  use the general pointwise overlap condition. Intern coherence follows through actual
  loading from the pre-load invariant. `OwnedInferenceTrace` returns ownership
  and coherence after applications, foralls, and full-mode lambdas, using one
  initial state resource and finite data for their actual walkers. It also
  reconstructs the cache-frame trace without per-leaf invariant premises.
  `SourceStateInvariant` additionally retains agreement with source-only
  standalone predictions through these calls and subsequent block loads.
  Initial coherence holds for `TcState.newLazyAnon`. Preservation by every
  checker operation and automatic trace construction remain open.
  Catalog constant and sort entries are preserved even when written by these
  recursive calls. General semantic cache invariants remain open.
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
  Alternatively, `SynthesisInference` derives formation of the generated type
  together with body typing. It follows the actual domain check at each lambda
  and keeps a universe bound for each local declaration. Reused closed type
  checks retain their source, states, successful run, and inference tree;
  interface extension preserves their entries exactly. These are execution
  resources, not semantic formation assumptions. The type checks can themselves
  contain direct lambda applications. The `lamBeta` rule retains a reduction
  origin from actual checks when cheap beta changes the body's inferred type.
  Its source and reduced syntax move together through interface extension, weakening,
  universe instantiation, and structural level congruence. Earlier local
  contexts are reconstructed from actual binder-domain checks. The reader
  follows the selected plan through substitution and interning, and lambda
  abstraction uses that reduction's output table. No new check of the
  generated result is assumed.
  Retained codomain checks now also cross dependent term substitution.
  `SynthesisTypeCheck.forallBody` extracts the actual codomain call from the
  earlier function-type tree. `SynthesisCheckedOrigin.applicationArgument`
  retains the executed function and argument checks and their hash comparison;
  the mutual soundness proof derives the argument's membership in that domain.
  `ApplicationInferenceTrace.substituteTypeOriginAt` then transports the
  original beta prefix beneath any remaining dependent parameters, updating
  their domains with the same substitution. This transport is consumed by
  `lamBeta`. No separate inference of the substituted type or semantic
  argument-typing premise is required.
  Variable-headed codomains also retain their actual argument checks.
  `SynthesisScopedTypeCheck.forallBody` follows nested codomain calls and
  their executed domain checks; `variableSpine` extracts the local head's
  exact type and the argument calls in order. Earlier parameter substitutions
  preserve that head's lookup and update its dependent type and arguments.
  `ApplicationInferenceTrace.exposedTypeOriginAt` then uses the substituted
  argument's own checked lambda domains to justify a newly exposed prefix.
  `substituteReductionOriginAt` carries that reduction through later
  arguments. The mutual `SynthesisReductionOrigin.sound` proof supplies the
  same conversion and reduced-type formation consumed by `lamBeta`.
  A supplied argument may already apply some of its lambda head's parameters.
  `SynthesisCheckedOrigin.soundWithSpine` retains those checks as well as
  the head's domains. `exposedApplicationOriginAt` joins them, in order, to
  the original codomain's argument checks. For example, substituting
  `(fun X : Sort u => fun Y : Sort u => X) A` for `F` in `F B` gives the
  checked spine `[A, B]`. Its existing arguments are lifted beneath retained
  parameters, and the codomain arguments receive the same substitution as
  their dependent types. The selected prefix can consume both lists.
- Applications use full mode, syntactic Pi exposure, an ordinary argument
  without an eager-reduction marker, and the hash-equality conversion path.
  Their witnesses retain the actual recursive calls, context preservation
  during function inference, and finite substitution resources. Function
  spines can start with locals or admitted constants, or use the synthesis
  rules for direct lambdas and returned functions. Polymorphic constants supply
  lazy-lookup agreement on misses (derived from source for bound standalones)
  or loaded-declaration agreement on hits, a
  closed scoped reading of the selected entry's type, and finite
  universe-substitution resources. Their result type is fixed
  by a pure `readInstantiatedType?` check with the substituted occurrence
  annotations, including when levels simplify. Monomorphic references retain
  their simpler empty-substitution rule. Reduction to expose a Pi, eager
  arguments, and automatic checking origins for arbitrary generated types
  require further refinement.
- `DefinitionCheckSupport` permits the existing initial hash-equality path,
  with faithfulness of the compared expressions, or a beta-reducible declared
  type. For the beta case, the declaration's own type-inference tree and run
  derive equality with the model substitution. The value's inference returns
  that substituted type. No additional inference on a generated type is
  assumed. This case covers `(fun X : Sort u => X) A` and a returned Pi such
  as `(fun X : Sort u => X → X) A`. The successful production comparison is
  retained in the declaration trace; its endpoints are justified by the
  executed checks. General reduction and conversion caches remain open.
- Definitions are added in dependency order with fresh references. Their
  observations use the states reached in the original serial work order,
  including cache clearing. `AtomicDefinitionRun.no_self_alias`
  proves that a fresh definition cannot justify its own type by referring to
  itself.
- Safe definition admission now checks the reachable definition graph in both
  Lean and Rust. Without this guard, the content-addressed source loader and
  checker accepted `theorem loop : P := loop` with only `P : Prop` as an axiom,
  including through a one-member mutual block. The new traversal follows type
  and value references under applications, binders, and lets, and includes
  projection heads. It rejects cycles and exhaustion of its shared one-million
  step bound. Axioms, inductives, constructors, and recursors are leaves with
  separate admission rules; partial and unsafe definitions retain their safety
  policy. Acyclic mutual definitions remain supported.
- `DefinitionDependencies.order_sound` derives a concrete dependency order from
  the production walk. Every entry is fresh and its collected dependencies
  precede it; `Ordered.wellFounded` derives a decreasing natural-number rank.
  The certificate covers the requested roots and can retain a lookup agreement
  relation. `DefinitionReferences.definitionRefs_complete` proves that memoization
  cannot omit a syntax reference, under finite-run collision freedom.
  `DefinitionBodyTrace.dependencyOrder` extracts the actual walk from successful
  safe validation, and `.referencesIn` connects that order to the references of
  the model's reading. Admission of every entry in that order still needs the
  broader body-typing and model-extension proofs.
- `checkEnvAnon` returns `.ok results` **and every result row has no error**.
  The outer `.ok` alone does not mean that the declarations passed.

Callers must establish these operational and representation witnesses for
the run. They supply no typing or checker-soundness premise. The proof
extracts the validation, type-inference, theorem-guard, value-inference, and
conversion steps from public success, then derives body typing to extend
the preceding model. General automatic witness construction, broader application and
lambda paths, lets, inductives, coordinated blocks, and other
conversion paths remain outside the fragment. The declaration's exact universe
arity is carried from production lookup into its model entry. Model extension
interprets the checked body at every universe instance, retaining old
interpretations at every instance as well. Specializations may use the new
definition's own parameters, including expressions such as `max u v`.

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

The same traversal covers 2,037 kernel manifest roots. Direct dependency
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

The consistency target checks 615 exact theorem boundaries. The production
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
Semantic checking against a formed type and the new product-fibre universe
bound also use only standard Lean axioms. The substitution rules for model
typing, checking, and equality introduce no additional assumptions.
Their general `instAt` forms use `ContextSubstitution` to remove an outer
parameter and update every retained dependent domain. The beta-prefix
commutation theorem covers any cutoff while bounding reduction by the
original lambda prefix. For a checked variable-headed application, a
substituted lambda's actual argument check supplies a new prefix origin.
`SynthesisInference.beta_peel_sound` derives beta-prefix equality and result
typing from actual lambda and dependent argument inference. Its domain-shape
proof retains information lost when proof values are identified. The original
lambda prefix is instantiated simultaneously, and the remaining arguments
retain their order. `beta_many_step` connects this to the production WHNF
step, with finite construction, size, and collision resources for the actual
walker and interned suffix. It derives the lambda-head callback from the real
recursive method table and returns intern coherence. Bounds concern the
original body and argument trees rather than generated substitution trees.
`cheapBeta_plan_sound` also connects selected closed-body and variable plans
to this meaning when an actual source check is available.
`DefinitionCheckSupport.betaDeclaredSpine` uses the declaration's own type
check to justify conversion through such a prefix and suffix, and therefore
reaches the environment model-extension and no-False roots.
`SynthesisInference.soundWithSpine` retains checked lambda domains in the
same recursion that proves typing and type formation. Its `lamBeta` case
uses retained executed checks, transported to the generated type's current
context, to justify the changed cheap-beta result. The actual source
reading determines the raw head and arguments; `CheapBetaSupport.reading`
connects the selected prefix to the reduced syntax and final intern table.
`SynthesisContext.sound` derives earlier contexts from their domain checks,
so the origin can precede additional binders. `SynthesisTypeTransport.sound`
and `SynthesisTypingOrigin.sound` are proved in that same recursion and carry
these checks through argument substitution, including later dependent
domains and the original context's universe instantiation. The public
inference and environment results include this case. `SynthesisCheckedOrigin`
additionally retains each actual argument's syntactic lambda domains, while
`SynthesisArgumentSpineOrigin` keeps the checks of the original variable
application's arguments. `SynthesisReductionOrigin.sound` combines them when
substitution exposes a lambda head. It proves the changed result's typing
and equality in the same mutual recursion, including earlier and later
dependent substitutions. These additions use the same two existing native
output-length proofs; their model lemmas use only standard Lean axioms.
The stronger checked-origin result also retains an argument's existing
lambda-headed application spine. `LambdaSpineTyping.substituteHead` combines
it with the original variable application's spine under the retained context,
so a selected reduction can cross from one argument list into the other.
`lambdaBodyVariableSpine` additionally extracts the actual argument checks
of a lambda body that applies its parameter. Their original result type can
differ from the lambda's codomain after cheap beta. `betaResultOrigin`
retains typing of the first substitution result at the current codomain;
`betaNextOrigin` combines it with the supplied lambda's checked prefix.
`beta_twice_sound` consequently composes two successive prefixes with
different lambda origins. `SynthesisReductionOrigin.beta_many_step` connects
the retained origin to the actual WHNF step on the intermediate type.
`DefinitionCheckSupport.betaDeclaredTwice` uses this conversion at the
existing declaration and environment admission boundary. Neither connector
requires inference of the intermediate term. The model's lambda-body and
term-conversion lemmas use only standard Lean axioms, and these production
roots retain the same two existing native output-length proofs.
`SynthesisBetaTrace` now composes any number of retained prefixes. A result
supplies a later function or argument origin, and composition preserves the
original type even when adjacent steps retain different types. Traces also
transport through application suffixes and dependent substitutions. Actual
source inference extracts the head and every argument check of its spine;
no intermediate inference call or semantic typing field is added.
`SynthesisBetaWhnfTrace.uncached_sound` connects finite paths to the real
structural-WHNF loop. Every beta step computes its raw result and next intern
table using production substitution and suffix interning. Reading and intern
coherence follow from the initial table and finite walker resources. The fuel
bound includes the final unchanged `.done` iteration. The same trace supplies
`DefinitionBodyTrace.betaDeclaredWhnfSupport` for declaration admission.
These boundaries retain the same two existing native output-length proofs.
`SynthesisInference.betaTyping` now derives the complete head-beta typing
structure from every currently supported source-inference constructor.
`SynthesisBetaTyping` keeps each lambda body and both application children.
Its substitution operation rebuilds this structure beneath dependent binders,
using a proved context insertion to lift the supplied argument. Forward beta
type conversions preserve a lambda's exact Pi domain, including when cheap
beta changes its body's inferred type. `betaStep` computes both the next
typing derivation and conversion, so `betaSteps` handles any finite number
of contractions without additional intermediate checks or semantic origins.
`BetaStepPlan` contains only raw execution, reading, and finite representation
resources. `BetaWhnfTrace.annotate` derives every step's meaning from the
original typing derivation, and `SynthesisInference.beta_whnf_sound` proves
the actual uncached result's conversion, typing at the original type, reading,
and intern coherence. `DefinitionBodyTrace.betaDeclaredStepsSupport` and
`betaDeclaredWhnfPathSupport` carry these automatic origins into declaration
admission. The 28 additional audited boundaries introduce no axioms or native
proofs. This closes automatic semantic origins for finite head-beta paths of
the supported source-inference fragment. Initial inference trees, operational
paths, and representation resources remain explicit; deriving them for all
accepted programs and covering the remaining WHNF/conversion paths remain open.
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
Direct lambda regressions cover Prop, Type, universe parameters, returned
functions, higher-order arguments, dependent proof/data families, and earlier
declaration types containing lambda calls. Negative cases reject invalid
domains, wrong arguments, and a universe term claimed at its own sort.
Beta regressions cover declared-type conversion in Prop, Type, and at a
universe parameter; substitution through returned function types; unequal
initial hashes and repeated conversion; fresh caches; capture avoidance
beneath returned lambdas; and rejection of a proposition used as its own proof.
Multi-argument cases check dependent domains, distinct carrier arguments,
partial lambda prefixes, capture avoidance through remaining binders, and
suffix rebuilding after substitution exposes a new lambda. They exercise
both cheap-beta fast paths and check that reduction preserves the local
context and fresh-variable counter. Declaration cases cover universe
parameters, cache clearing, a remaining family application, and rejection of
a witness belonging to the other carrier.
Lambda cheap-beta regressions observe different original and reduced body
types, local checking origins beneath further binders, dependent prefixes,
both application positions, and reused declaration types in Prop, Type, and
at universe parameters. They also check cache clearing, scope cleanup, and
rejection of a carrier returned in place of its witness.
Application-type beta regressions check an earlier function's substituted
codomain in Prop, Type, and at universe parameters. Two-argument cases use
`(x : A) → (y : B x) → ((fun T : Sort u => T) (C x y))`: they observe the
updated second domain, different original and reduced result hashes, and the
exact final lambda type. They cover cache clearing, reuse, scope cleanup, and
rejection of a carrier or first argument used in the wrong dependent domain.
Exposed-lambda regressions start with checked variable-headed codomains
`F A`, `F A B`, and `F x`. They observe the new head, argument order, beta
count, and exact reduced result after supplying a lambda. The dependent
identity example `f A x F y` also checks that earlier arguments specialize
the later family's domain before its lambda creates the redex. Cases cover
Prop, Type, universe parameters, captured carriers, cache clearing/reuse,
scope cleanup, and rejected function types and dependent witnesses.
Composition cases supply partial lambda applications. They check the exact
combined argument order and two- or three-lambda reduction counts for both
cheap-beta plans, including dependent initial arguments and caller locals.
They cover Prop, Type, universe parameters, cache clearing/reuse, and failures
for an ill-typed initial argument or a different selected carrier.
Successive-beta cases observe two actual WHNF steps with distinct lambda
heads and require the second result to equal the value's inferred type.
They include captured carriers, partial applications, dependent initial and
body arguments, a remaining family-application suffix, universe parameters,
and cache clearing. One case changes the first lambda body's inferred type
from a beta redex to a sort, then consumes the supplied lambda's two-argument
prefix. Negative cases reject a wrong function domain, a different selected
carrier, and invalid dependent arguments from either origin.
Finite-trace cases cover three and twelve successive prefixes, retained
dependent final arguments, declaration universe parameters, and cleared
caches. Both WHNF policies compare individual production steps with the
bounded driver and uncached entry point. A budget equal to the number of
reductions exhausts before `.done`; one additional iteration returns the exact
inferred value type. Negative cases reject a different carrier and an invalid
dependent argument after several returned-function prefixes.
Hereditary-beta cases substitute a supplied function beneath two dependent
binders before consuming both retained arguments. They cover up to twelve
later prefixes, reductions of types and ordinary terms, and WHNF stopping at
a returned lambda that still contains the supplied function. Further chains
retain a lambda body's changed cheap-beta type. Prop, Type, declaration
parameters, cleared caches, both WHNF policies, exact consumed-argument
counts, and rejected dependent substitutions are checked.
These execution tests do not construct the general finite inference resources.
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
Standalone lazy-loading regressions warm one witness, load another declaration
directly or inside a lambda/application, and reuse the original witness.
They cover all four standalone conversion forms, both inference policies,
missing and corrupt sources, definition and recursor failures with retained
intern progress, and deduplicated retries.
Block-loading regressions populate both cache partitions and retain them through
fresh and partially loaded mutual blocks, recursive function bodies, and all
four projection forms. They check cached sibling preservation, block-level
deduplication, missing or corrupt parents, preparation failures after earlier
members converted, and an unknown block-root lookup that retains completed
publication. These exercise loading and cache preservation; they do not establish
semantic admission of inductives or recursors.
Intern-coherence regressions include 4,096-deep universe, application, and
binder trees; forward and backward sharing chains; repeated sharing; and
unexpanded cyclic entries. Cyclic standalone and block loads must return a
bounded diagnostic, preserve both warm cache partitions and coherent partial
intern state, and deduplicate retries without publishing declarations.
Source ownership regressions cover conflicting block owners, standalone/projection
overlap, duplicate keys within one block, exact mixed-member and constructor
inventories, corrupt source exclusion, and detection of partial external loads.
Mixed loading sequences preserve the block invariant and both warm cache slots
in full and inference-only modes, including errors before and after publication.
Recursive-state regressions check ownership and intern keys after application,
forall, and lambda inference that loads one block, followed by a constant call
that loads another. They retain both warm partitions, outer local scopes, and
the actual statistics updates; replaying the recursive cache hit changes
neither intern tables nor fresh-local allocation.
Source-prediction regressions compare complete anonymous declarations through
cold conversion, warm conversion, and actual lazy publication. They cover
expression annotations, universe trees and normalization, every expression
form, literal blobs, reducibility hints, recursor fields and rules, invalid
indices, cyclic sharing, and catalog selection. Deliberately conflicting intern
entries with equal hashes demonstrate why finite collision freedom is needed.
Recursive source-agreement cases retain the catalog through applications and
binders, a mixed block load, another standalone load, and cache replay under
an outer scope.
Source-cache histories start empty, populate both policies at the same key,
and check complete results and declaration coverage through recursive calls,
mixed block loads, partial lookup failures, distinct universe instances, scopes,
replay, clearing, and repopulation. Negative cases detect a correct cached type
with no loaded declaration and a forged application writing a constant's key.
Polymorphic admission regressions check parameterized definitions and opaque
values, aliases with changed universe arguments, applications under binders,
later Prop/Type instances, exact loaded arities, and unused parameters. They
reject undeclared parameters, out-of-range value parameters, different
in-range parameters in place of the declared type, non-Prop theorem types,
and missing arguments for unused parameters.
Definition-cycle regressions use content-addressed standalone and mutual
declarations, including a self-justifying theorem, a two-member cycle, type
cycles, lets, shared syntax, and binders. They check repeated member failures,
acyclic forward references, cache clearing, and the partial/unsafe policy.
The unit suite contains 686 checks. The anonymous differential additionally
serializes eight cycle-policy fixtures and checks exact target sets, verdicts,
failure counts, and cycle diagnostics in both implementations.

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
| Ownership and intern coherence through recursive inference | [`Consistency/RecursiveState.lean`](../Ix/Kernel/Verify/Consistency/RecursiveState.lean) |
| Exact source conversion and finite candidate inventories | [`SourceConversion.lean`](../Ix/Kernel/SourceConversion.lean), [`Consistency/ConversionRecipe.lean`](../Ix/Kernel/Verify/Consistency/ConversionRecipe.lean) |
| Standalone source/model agreement through lookup and inference | [`Consistency/SourceAgreement.lean`](../Ix/Kernel/Verify/Consistency/SourceAgreement.lean) |
| Source cache agreement from empty-state execution histories | [`Consistency/SourceCache.lean`](../Ix/Kernel/Verify/Consistency/SourceCache.lean) |
| Verified standalone lazy loading and cache frames | [`Consistency/LazyCache.lean`](../Ix/Kernel/Verify/Consistency/LazyCache.lean) |
| Mutual-block publication and verified lookup frames | [`Consistency/BlockCache.lean`](../Ix/Kernel/Verify/Consistency/BlockCache.lean) |
| Intern coherence through conversion and lazy loading | [`Consistency/IngressCoherence.lean`](../Ix/Kernel/Verify/Consistency/IngressCoherence.lean) |
| Source ownership, block registration, and finite preflight | [`Consistency/BlockOwnership.lean`](../Ix/Kernel/Verify/Consistency/BlockOwnership.lean), [`Consistency/SourceOwnershipCheck.lean`](../Ix/Kernel/Verify/Consistency/SourceOwnershipCheck.lean), [`SourceOwnership.lean`](../Ix/Kernel/SourceOwnership.lean) |
| Dependent binders and function bodies | [`Consistency/BinderInference.lean`](../Ix/Kernel/Verify/Consistency/BinderInference.lean), [`Application.lean`](../Ix/Kernel/Verify/Consistency/Application.lean), [`BinderOpening.lean`](../Ix/Kernel/Verify/Consistency/BinderOpening.lean), [`Context.lean`](../Ix/Kernel/Verify/Consistency/Context.lean), [`Model/Checking.lean`](../Ix/Theory/Model/Checking.lean) |
| Inferred type formation and direct lambda applications | [`Consistency/SynthesisInference.lean`](../Ix/Kernel/Verify/Consistency/SynthesisInference.lean), [`Formation.lean`](../Ix/Kernel/Verify/Consistency/Formation.lean), [`Model/UniverseBounds.lean`](../Ix/Theory/Model/UniverseBounds.lean) |
| Retained type checks and changed cheap beta in lambda inference | [`Consistency/SynthesisInference.lean`](../Ix/Kernel/Verify/Consistency/SynthesisInference.lean), [`CheapBetaReading.lean`](../Ix/Kernel/Verify/Consistency/CheapBetaReading.lean), [`Formation.lean`](../Ix/Kernel/Verify/Consistency/Formation.lean) |
| Source beta reduction and declaration conversion | [`Consistency/BetaSpine.lean`](../Ix/Kernel/Verify/Consistency/BetaSpine.lean), [`Simultaneous.lean`](../Ix/Kernel/Verify/Consistency/Simultaneous.lean), [`SpineReading.lean`](../Ix/Kernel/Verify/Consistency/SpineReading.lean), [`CheapBeta.lean`](../Ix/Kernel/Verify/Consistency/CheapBeta.lean), [`Model/BetaSpine.lean`](../Ix/Theory/Model/BetaSpine.lean) |
| Production environment fragment and relative axiom policy | [`Consistency/Environment.lean`](../Ix/Kernel/Verify/Consistency/Environment.lean), [`Production.lean`](../Ix/Kernel/Verify/Consistency/Production.lean) |
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
`Model/LevelCongruence.lean`, `Model/Checking.lean`, `Model/UniverseBounds.lean`,
`Model/Substitution.lean`, `Model/BetaSubstitution.lean`, and
`Model/BetaSpine.lean` are Ix-authored mathematical additions, listed separately
from the imported files in the theory provenance manifest.
