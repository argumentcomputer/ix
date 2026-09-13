# Kernel verification

`Ix.Kernel` is the production Lean checker. `Ix.Kernel.Verify` contains its
implementation proofs; `Ix.Compile.Verify` contains the Lean-to-Ixon compiler
proofs. Their named specification and reference implementation lemmas are local
under `Ix.Theory.Named`. Building or checking them requires no external
formalization repository.

The named development retains the 104 source modules needed by the existing
proof dependency graph, including the inductive fixtures consumed by Ix.
Standalone applications, benchmarks, and unrelated tests are excluded. Its
original source hashes and attribution are recorded in `Ix/Theory/Named/NOTICE`
and `Tests/Theory/NamedManifest.lean`; the Apache license is preserved alongside
the sources. The added axiom-audit helper is authored in Ix.

## Connection to the consistency model

The name-indexed specification and the set model use the same
`Ix.Theory.VLevel`. The set model and its foundational audit remain independent
of the named development. Mathlib is confined to the separate
[set-theory model package](../Models/SetTheory/README.md).

That package's `IxSetTheoryModel.setTheoryOfCarneiro` constructs the exact
`Ix.Theory.Model.SetTheory` interface on Mathlib's `ZFSet`. It takes an explicit
`OmegaInaccessibles` hypothesis: a strictly increasing countable sequence of
strongly inaccessible cardinals. The universe chain is `V_ (κ n).ord`.
`carneiro_implies_ix` proves model existence under this hypothesis, with a full
dependency audit restricted to Lean's three standard axioms.

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
- `ModelTyping.no_false` rules out a closed model-typed kernel expression at
  primitive False when its environment has been admitted by the certified
  interface and the set-theory assumption has an instance.
- `checkEnvAnon_atomic_preserves_model` connects a supported production
  environment run to model extension. `checkEnvAnon_atomic_no_false` excludes
  a declaration at an axiom type interpreted as empty, including False.

`ModelTyping.no_false` assumes semantic typing. The production fragment below
constructs that typing from its supported inference and conversion paths.
A complete checker consistency theorem
still requires the remaining inference/conversion cases, cache invariants,
address-to-store resolution, and declaration admission to establish that
postcondition for `checkEnvAnon`. The existing named-calculus proofs are retained
to support this refinement, rather than being treated as a set-model proof.

## Production environment fragment

The axiom policy is relative: **every model of the source axioms extends to a
model of the checked environment, preserving the axiom interpretations**.
The axiom interface starts empty and contains exactly the listed source
axioms. Its types must be closed and refer only to that interface. A concrete
`Realizes` witness supplies their interpretation; checking an axiom's type
does not manufacture an inhabitant. This model-existence hypothesis is not
identified with syntactic consistency of an arbitrary axiom theory.

The initial fragment covers monomorphic standalone definitions, theorems,
and opaque definitions whose values are either closed universe terms or
references to preceding interface entries. Examples include:

```lean
axiom P : Prop
axiom p : P
def q : P := p
theorem r : P := q
def typeAlias : Type := Prop
```

`AtomicEnvironmentFragment` records the precise execution boundary:

- Every source key occurs in the exact `buildAnonWork` result, and every work
  item is represented by an axiom or a definition. Standalone lookup, routing,
  and reset witnesses identify the actual checked `KConst`.
- Value inference misses both cache partitions. Constant lookup agrees with
  an already admitted monomorphic type; empty level substitution preserves
  that type. Sort inference retains the finite interning coherence and
  address-faithfulness premises.
- Conversion takes the initial hash-equality path, with faithfulness of the
  compared expressions. General reduction and conversion caches are outside
  this fragment.
- Definitions are added in a dependency order with fresh references. Their
  runtime observations still use the states reached in the original serial
  work order, including cache clearing. `AtomicDefinitionRun.no_self_alias`
  proves that a fresh definition cannot justify its own type by referring to
  itself.
- `checkEnvAnon` returns `.ok results` **and every result row has no error**.
  The outer `.ok` alone does not mean that the declarations passed.

These are operational and representation witnesses, not a checker-soundness
callback or a supplied typing proof. A caller must establish them for a run;
this change does not automatically derive them from arbitrary Ixon syntax.
The proof follows the public checker through validation, type inference,
the theorem guard, value inference, and conversion. Successful value
inference constructs the body typing used to extend the preceding model.
Lambdas, applications, polymorphic instantiation, inductives, coordinated
blocks, and other conversion paths remain outside this slice.

`checkEnvAnon_atomic_represents_source` assigns every source address an
interface whose type reads the exact declaration reached by production
lookup. Definition interfaces also retain their checked bodies. This is a
statement about the production ingress/lookup result; the independent
serialized-Ixon reader refinement remains a separate boundary.

The no-False corollary takes a model of the initial axiom interface in which
the designated false type is empty. Model extension preserves that value,
so no resulting declaration can inhabit it. It does not blacklist axiom
names or merely exclude declarations literally written with type `False`.

## Trust checks

The audits traverse checked declaration types and bodies, including inductive
constructors. They compare exact axiom sets and record direct origins of
`sorryAx`; they do not rely on cached imported axiom summaries. During the
migration, full traversal of the original sources exposed two wrapper reports
that listed 3 axioms but depended on 30. Their boundaries now include the
existing implementation assumptions and unfinished metatheory. All 441 retained
named-specification assertions use the original full dependency graphs as their
migration baseline.

The same traversal covers 2,034 kernel manifest roots. Thirteen entries omitted
logical or native dependencies through constructor fields; their corrected
boundaries were checked against freshly compiled pre-migration sources. Direct
dependency lookups are cached within a fixed environment, while each root's
reachable declarations, axioms, and proof-hole origins are computed separately.

`Ix.Kernel.Frontier.Pending` quarantines the remaining explicit metatheory
axioms. Completed roots cannot depend on that namespace. Named-specification
proof holes and implementation bridge axioms are tracked separately from
Lean's logical axioms and generated native proofs. No direct consistency root
permits a proof hole or a metatheory/implementation bridge axiom. Both the
context hash and content-address hash now use kernel-checked proofs of their
32-byte output bounds on both platform sizes. Their former generated native
assumptions have been removed from the affected exact audits.

Run the complete local kernel-certification gate:

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

The consistency target checks 36 exact theorem boundaries. The production
environment roots retain four existing generated output-length proofs,
reached through expression/universe construction, names, and the full
production method table. They introduce no new native proofs. The model
extension lemma and `ModelTyping.no_false` use only `propext`,
`Classical.choice`, and `Quot.sound`, with set theory as a hypothesis.
The new production roots additionally forbid the earlier abstract
`CheckSuccessSound`/`SupportedCheckFragment` interfaces and the independent
certificate validator in their dependency closures.

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

These host results do not cover the full production inference dispatcher or
prove that an Aiur public verifier executes the host validator. The VM pilot
remains in the frozen archive for a later change; its build target and execution
tests are outside the host gate.

## Review entry points

| Area | Entry point |
| --- | --- |
| Certified checker contracts | [`Ix/Kernel/Certified.lean`](../Ix/Kernel/Certified.lean), [`CertifiedClaims.lean`](../Ix/Kernel/CertifiedClaims.lean) |
| Direct production refinement and its audit | [`Ix/Kernel/Verify/Consistency.lean`](../Ix/Kernel/Verify/Consistency.lean) |
| Production environment fragment and relative axiom policy | [`Consistency/Environment.lean`](../Ix/Kernel/Verify/Consistency/Environment.lean), [`Production.lean`](../Ix/Kernel/Verify/Consistency/Production.lean) |
| Foundation assumptions, theorem contracts, and provenance | [Consistency model guide](theory.md) |
| Host commands, receipts, and frozen regression evidence | [Certified checking guide](certified-checking.md) |
| Concrete set-theory instance | [Separate model package](../Models/SetTheory/README.md) |

## Change scope

The kernel, theory and certified host scaffolding is extracted from
`jcb/monorepo` at `7b06b754` in a single change. Existing callers move from
`Ix.Tc` to `Ix.Kernel`. Existing `Ix.Compile.Verify` proofs receive the
necessary named-specification imports and exact hash-axiom audit updates.
The new compiler development, circuit changes and certificate VM pilot
are deferred. The external `lean4lean` dependency and its benchmark/test
targets are removed; all verification dependencies are local to Ix.

The subsequent production-fragment change adds direct inference, declaration,
and serial-environment proofs on top of that extraction. It changes no
production checker behavior and adds regression cases to the existing kernel
unit gate.
