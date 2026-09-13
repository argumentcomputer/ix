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
  literals, and substitutes let values. Free variables, unresolved addresses,
  and string literals are outside the current reader's domain.
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
and opaque definitions whose values are either closed universe terms or
references to preceding interface entries, including monomorphic
specializations of polymorphic constants. Referenced types may contain
dependent functions and other readable expression forms. Examples include:

```lean
axiom P : Prop
axiom p : P
def q : P := p
theorem r : P := q
def typeAlias : Type := Prop
axiom ident.{u} : (α : Sort u) → α → α
def propIdent : (α : Prop) → α → α := ident.{0}
```

`AtomicEnvironmentFragment` records the precise execution boundary:

- Every source key occurs in the `buildAnonWork` result, and every work item
  represents an axiom or a definition. Lookup, routing, and reset witnesses
  identify the checked `KConst`.
- Value inference misses both cache partitions. Constant lookup agrees with
  an already admitted type and universe count. A specialization supplies
  closed universe arguments and finite interning/substitution resources at
  the actual post-lookup state. The occurrence annotations on the declared
  type agree with the substituted entry's annotations. These are structural
  data checks; successful inference derives typing, scope, and references.
  Ordinary aliases retain the simpler empty-substitution path. Sort inference
  retains finite interning coherence and address-faithfulness premises.
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
the preceding model. Automatic witness construction, lambdas, applications,
inductives, coordinated blocks, and other conversion paths remain outside the
fragment. Polymorphic constant inference is composed into declaration
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

The consistency target checks 66 exact theorem boundaries. The production
environment roots retain four existing generated output-length proofs,
reached through expression/universe construction, names, and the full
production method table. They introduce no new native proofs. The model
extension lemma and `ModelTyping.no_false` use only `propext`,
`Classical.choice`, and `Quot.sound`, with set theory as a hypothesis.
The production roots additionally forbid the abstract
`CheckSuccessSound`/`SupportedCheckFragment` interfaces and the independent
certificate validator in their dependency closures.

The polymorphic inference and substitution roots retain only the two existing
expression/universe output-length proofs, alongside the standard Lean axioms.
Their model-side level congruence introduces no native proof dependency.
Kernel unit regressions cover lazy loading, both inference policies, interning
reuse, dependent function types, shared references, lets, `imax` simplification,
argument order, and rejection of wrong arities and out-of-range parameters.
Environment regressions additionally check Prop/Type specializations,
transitive aliases, nested references, simplified declaration types, cache
clearing, and admission failures for wrong arities, open parameters, and a
mismatched declared specialization.

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
`Model/LevelCongruence.lean` is an Ix-authored mathematical addition, listed
separately from the imported files in the theory provenance manifest.
