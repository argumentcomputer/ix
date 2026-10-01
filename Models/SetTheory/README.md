# Set-theory model

This separate Lake package constructs the certified checker's set-theory
interface on Mathlib's `ZFSet`, assuming a strictly increasing countable
sequence of strongly inaccessible cardinals. Its universe chain is
`V_ (κ n).ord`.

From port step L5 (plan v4) the checker's theorems are stated over
con-leche's class `ConLeche.SetTheory`. `IxSetTheoryModel.conLecheSetTheoryOfChain`
assembles that instance from a given chain, `conLecheSetTheoryOfCarneiro`
selects a chain from `OmegaInaccessibles`, and `carneiro_implies_conleche`
proves:

```lean
OmegaInaccessibles.{u} →
  Nonempty (Σ V : Type (u + 1), ConLeche.SetTheory V)
```

`IxSetTheoryModel/Consistency.lean` instantiates the certified Ixon entry's
theorems there: `checkBytes_has_ZFSet_model` (every input the entry accepts
has a model in `ZFSet`) and `checkBytes_no_proof_of_False`.

Until L6 the same construction also provided Ix's own class
`Ix.Kernel.Model.SetTheory`, the interface of the intrinsic reference
kernel (`setTheoryOfChain`, `setTheoryOfCarneiro`, `carneiro_implies_ix`).
L6 retired that kernel, its copy of the class and that instance; the
lemmas are now stated over con-leche's `IsTGUniverse` and `Equinumerous`.

The construction includes the interface's Lean-level replacement scheme:
Mathlib's `Classical.allZFSetDefinable` supplies images of arbitrary functions
`ZFSet → ZFSet`. The audit traverses the checked types, bodies, and
constructor fields of each of the three theorems above and permits exactly
`propext`, `Classical.choice`, and `Quot.sound`. Inaccessible cardinals
remain an explicit theorem hypothesis.

The package imports the actual interfaces by a path dependency on the
`IxKernel` package, which builds `Ix.Kernel`, the `ConLeche` subtree and the
certified Ixon entry from the repository sources with no other dependencies. Mathlib is confined to this package; ordinary Ix and
`Ix.Kernel` builds do not depend on it. This construction supplies the
set-theoretic assumption used by the [certified kernel roadmap](../../plans/ix-certified-roadmap.md).
A converse from the interface to inaccessible cardinals is a separate proof
obligation.

## Build

From `Models/SetTheory`:

```sh
lake exe cache get Mathlib.SetTheory.Cardinal.Regular Mathlib.SetTheory.ZFC.VonNeumann Mathlib.SetTheory.ZFC.Cardinal
lake build --wfail
```

Lean and Mathlib use release `v4.34.0`; `lake-manifest.json` pins all resolved
dependencies. The cache command retrieves the three imported Mathlib modules
and their dependencies. The build checks the axiom guard. The separate
`set-theory-model.yml` workflow runs these commands when the model, its interface,
or package configuration changes.

From the repository root, `lake run check-kernel --with-model` includes this
build alongside the kernel proofs, foundation audits, and host regressions.

## Provenance

`IxSetTheoryModel/Carneiro.lean` is copied from con-leche revision
`86cd20a65660d757cedc81561a44579099b565d0`. The original path and source
SHA-256 are recorded in [NOTICE](NOTICE).
Namespaces, imports, and documentation are adapted for Ix; the mathematical
construction is retained. Con-leche's Apache-2.0 license is preserved in
`LICENSE-CON-LECHE`.
