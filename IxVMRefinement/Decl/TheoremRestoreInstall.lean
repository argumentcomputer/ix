import IxVMRefinement.Decl.TheoremRestore
import Ix.IxVM.Consistency.Statement

/-! # Storage correspondence through theorem restoration

Restoration keeps the checked type and value annotations. This connects the restored model's
constants to the reader's theorem entries without changing their names or list membership.
-/

namespace IxVM.Refinement.Decl.TheoremRestore

open Ix.Kernel
open IxVM.Consistency (StoredAs ValStored)

/-- The same name-based restoration preserves each declaration's checked storage relation. -/
theorem storedAs (selected : Key .anon → Bool) {ci raw : ConstantInfo .anon}
    (stored : StoredAs ci raw) : StoredAs (info selected ci) (info selected raw) := by
  cases ci with
  | defnInfo cv value hint =>
    cases raw with
    | defnInfo cv₀ value₀ hint₀ =>
      obtain ⟨hcv, hvalue, rfl⟩ := stored
      cases hint with
      | «opaque» =>
        simp only [info]
        have name : cv.name = cv₀.name := hcv.1
        rw [name]
        split
        · exact ⟨hcv, hvalue⟩
        · exact ⟨hcv, hvalue, rfl⟩
      | «abbrev» | regular => exact ⟨hcv, hvalue, rfl⟩
    | _ => exact stored.2.elim
  | _ => cases raw <;> first | exact stored | exact stored.2.elim

/-- A selected reference theorem's opaque definition stores the original theorem after restoration. -/
theorem storedTheorem (selected : Key .anon → Bool) {ci : ConstantInfo .anon}
    {cv : ConstantVal .anon} {value : Expr .anon}
    (chosen : selected cv.name = true)
    (stored : StoredAs ci (.defnInfo cv value .opaque)) :
    StoredAs (info selected ci) (.thmInfo cv value) := by
  simpa only [info, chosen, ↓reduceIte] using storedAs selected stored

/-- Restoring kinds leaves distinct-name and chunk-order bookkeeping unchanged. -/
theorem names (selected : Key md → Bool) (entries : List (ConstantInfo md)) :
    ((entries.map (info selected)).map (·.name)) = entries.map (·.name) := by
  simp only [List.map_map, Function.comp_def, info_name]

/-- A final stored entry remains available at the same name, in its restored kind. -/
theorem stored_lookup (selected : Key .anon → Bool) {env : Env .anon} {name : Key .anon}
    {ci raw : ConstantInfo .anon} (found : env.find? name = some ci) (stored : StoredAs ci raw) :
    (environment selected env).find? name = some (info selected ci) ∧
      StoredAs (info selected ci) (info selected raw) :=
  ⟨by rw [find, found]; rfl, storedAs selected stored⟩

end IxVM.Refinement.Decl.TheoremRestore
