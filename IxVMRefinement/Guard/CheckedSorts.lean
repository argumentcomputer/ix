import IxVMRefinement.Guard.Certificate
import IxVMRefinement.Guard.CheckedFields

/-! # What the checked field loop has to be read as, for the sorts it checked

`Core.CheckedFieldsReading` (`Guard/Certificate.lean`) states the reading of the installing run's
field loop with the field sorts existential. A native install runs IxC's table stage at the
sorts the loop checked (`GuardData.CheckedFieldsAt`, handed through the install's output), so the
reading it needs is for those sorts.

* `Core.CheckedSortsRunReading`: under the run data of the loop at a constructor
  (`CheckedFieldsAt`), either the run hashed a collision of the context's store, or the sorts
  have the zero-sets of the classifier's signatures of the constructor's raw telescope read from
  that store. Its last three conjuncts are the hypotheses of
  `Guard.projGuardCert_of_checkNativeTable`. The alternative is the run's own, so a run's
  goodness refutes it; no internal collision of the store is asked to be absent.
-/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)

set_option linter.unusedVariables false

/-- **The reading of the checked field loop, for the sorts it checked** (module docstring). It
is stated at the loop's own context: any role table, any limit, any keying. -/
def CheckedSortsRunReading : Prop :=
  ∀ (c : ScopedCtx) (hc : ScopedCoreFacts c) {calls : List (Call F)} {b : Bytes.Address} {i : F}
    {nP nF : Nat} {cty : KExpr} {u : KLevel} {sorts : List KLevel},
    GuardData.CheckedFieldsAt c calls b i nP nF cty u sorts →
    View.HashedCollision { env := c.E } [] calls ∨
    ∃ (sigs : List KLevel) (fuel : Nat) (raw : KExpr),
      Guard.ctorRaw c.E (ixAddr b) (ZMod.val i) 0 = some raw ∧
      Ix.Kernel.GuardClassifier.fieldSignatures (GuardRaw.ofStore c.E) fuel nP nF [] raw =
        some sigs ∧
      ∀ j, j < nF → ∀ φ : Ix.Kernel.LevelParam → Nat,
        Ix.Kernel.Level.eval φ (sorts.getD j .zero) = 0 ↔
          Ix.Kernel.Level.eval φ (sigs.getD j .zero) = 0

end IxVM.Refinement.Core
