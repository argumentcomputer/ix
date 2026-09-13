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

The last theorem assumes semantic typing; it does not assume or prove that
arbitrary checker success supplies it. A complete checker consistency theorem
still requires the remaining inference/conversion cases, cache invariants,
address-to-store resolution, and declaration admission to establish that
postcondition for `checkEnvAnon`. The existing named-calculus proofs are retained
to support this refinement, rather than being treated as a set-model proof.

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

The consistency target checks 18 exact theorem boundaries. Its remaining
native assumptions are explicitly named proofs reached through production
smart-constructor code; the model's no-False theorem itself uses only
`propext`, `Classical.choice`, and `Quot.sound`, with set theory as a hypothesis.

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
