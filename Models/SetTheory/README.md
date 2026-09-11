# Set-theory model

This separate Lake package constructs `Ix.Theory.Model.SetTheory` on Mathlib's
`ZFSet`, assuming a strictly increasing countable sequence of strongly
inaccessible cardinals. Its universe chain is `V_ (κ n).ord`.

`IxSetTheoryModel.setTheoryOfChain` assembles the instance from a given chain.
`setTheoryOfCarneiro` selects a chain from `OmegaInaccessibles`, and
`carneiro_implies_ix` proves:

```lean
OmegaInaccessibles.{u} →
  Nonempty (Σ V : Type (u + 1), Ix.Theory.Model.SetTheory V)
```

The construction includes the interface's Lean-level replacement scheme:
Mathlib's `Classical.allZFSetDefinable` supplies images of arbitrary functions
`ZFSet → ZFSet`. The audit traverses the theorem's checked types, bodies, and
constructor fields and permits exactly `propext`, `Classical.choice`, and
`Quot.sound`. Inaccessible cardinals remain an explicit
hypothesis, rather than an added Lean axiom.

The package imports the actual Ix interface by a path dependency on the
repository root. Mathlib is confined to this package; ordinary Ix and
`Ix.Theory` builds do not depend on it. This construction supplies the
set-theoretic assumption used by the [consistency model](../../docs/theory.md).
The connection from the production checker to the certified interface is a
separate proof obligation. A converse from the interface to inaccessible
cardinals is not proved here.

## Build

From `Models/SetTheory`:

```sh
lake exe cache get Mathlib.SetTheory.Cardinal.Regular Mathlib.SetTheory.ZFC.VonNeumann Mathlib.SetTheory.ZFC.Cardinal
lake build --wfail
```

Lean and Mathlib use release `v4.33.1`; `lake-manifest.json` pins all resolved
dependencies. The cache command retrieves the three imported Mathlib modules
and their dependencies. The build checks the axiom guard. The separate
`set-theory-model.yml` workflow runs these commands when the model, its interface,
or package configuration changes.

## Provenance

`IxSetTheoryModel/Carneiro.lean` is copied from con-leche revision
`86cd20a65660d757cedc81561a44579099b565d0`. The original path and source
SHA-256 are recorded in [NOTICE](NOTICE).
Namespaces, imports, and documentation are adapted for Ix; the mathematical
construction is retained. Con-leche's Apache-2.0 license is preserved in
`LICENSE-CON-LECHE`.
