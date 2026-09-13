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
  `infer`) misses in both cache partitions at the computed key.
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
  miss's insertion. General preservation of that agreement remains open.
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
axiom T.{u} : Sort u
axiom f.{u} : T.{u} → T.{u}
def useF (x : T.{1}) : T.{1} := f.{1} x
```

`AtomicEnvironmentFragment` records the precise execution boundary:

- Every source key occurs in the `buildAnonWork` result, and every work item
  represents an axiom or a definition. Lookup, routing, and reset witnesses
  identify the checked `KConst`.
- Sort, application, forall, and lambda nodes in the inference witnesses miss both cache partitions.
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
  Ordinary aliases retain the simpler empty-substitution path. Sort inference
  retains finite interning coherence and address-faithfulness premises.
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
the preceding model. Automatic witness construction, broader application and
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

The consistency target checks 127 exact theorem boundaries. The production
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
| Dependent binders and function bodies | [`Consistency/BinderInference.lean`](../Ix/Kernel/Verify/Consistency/BinderInference.lean), [`Application.lean`](../Ix/Kernel/Verify/Consistency/Application.lean), [`BinderOpening.lean`](../Ix/Kernel/Verify/Consistency/BinderOpening.lean), [`Context.lean`](../Ix/Kernel/Verify/Consistency/Context.lean), [`Model/Checking.lean`](../Ix/Theory/Model/Checking.lean) |
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
`Model/LevelCongruence.lean` and `Model/Checking.lean` are Ix-authored mathematical
additions, listed
separately from the imported files in the theory provenance manifest.
