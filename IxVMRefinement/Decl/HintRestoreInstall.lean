import IxVMRefinement.Decl.HintRestore
import Ix.IxVM.Consistency.Statement

/-! # Final hint selection and exact reader storage -/

namespace IxVM.Refinement.Decl.HintRestore

open Ix.Kernel
open IxVM.Consistency (StoredAs ValStored)

variable (chosen : Key .anon → Option ReducibilityHint)

/-- Applying the same hint selection to a stored entry and its declaration preserves storage. -/
theorem storedAs {ci raw : ConstantInfo .anon} (stored : StoredAs ci raw) :
    StoredAs (info chosen ci) (info chosen raw) := by
  cases ci with
  | defnInfo cv value hint =>
    cases raw with
    | defnInfo cv₀ value₀ hint₀ =>
      obtain ⟨hcv, hvalue, rfl⟩ := stored
      have name : cv.name = cv₀.name := hcv.1
      refine ⟨hcv, hvalue, ?_⟩
      rw [name]
    | _ => exact stored.2.elim
  | _ => cases raw <;> exact stored

/-- The actual reader hint replaces the old hint while retaining the checked type and value. -/
theorem storedDefinition {ci : ConstantInfo .anon} {cv : ConstantVal .anon} {value : Expr .anon}
    {oldHint readerHint : ReducibilityHint}
    (selected : chosen cv.name = some readerHint)
    (stored : StoredAs ci (.defnInfo cv value oldHint)) :
    StoredAs (info chosen ci) (.defnInfo cv value readerHint) := by
  simpa only [info, selected, Option.getD_some] using storedAs chosen stored

/-- The selected definition remains at its original name with the exact reader hint. -/
theorem stored_lookup {env : Env .anon} {name : Key .anon} {ci raw : ConstantInfo .anon}
    (found : env.find? name = some ci) (stored : StoredAs ci raw) :
    (setHints chosen env).find? name = some (info chosen ci) ∧
      StoredAs (info chosen ci) (info chosen raw) :=
  ⟨by rw [find, found]; rfl, storedAs chosen stored⟩

end IxVM.Refinement.Decl.HintRestore
