import IxVMRefinement.Decl.NativeFormerRestore
import IxVMRefinement.Decl.TheoremRestoreInstall

/-! # Reader storage after restoring a declared alias former

The original name and universe parameters stay exact. A constant alias node needs no new
annotation, so the restored former has the reader's required storage shape.
-/

namespace IxVM.Refinement.Decl.NativeFormerRestore

open Ix.Kernel
open IxVM.Consistency (StoredAs)

/-- Restoring the declared alias type recovers the original reader-shaped inductive entry. -/
theorem storedAlias {checked raw : ConstantVal .anon} {caps rawCaps : IndCaps .anon}
    {alias : Key .anon} {levels : List Level}
    (name : checked.name = raw.name) (params : checked.levelParams = raw.levelParams)
    (declared : raw.type = .const alias levels) :
    StoredAs (.indInfo { checked with type := .const alias levels } caps) (.indInfo raw rawCaps) := by
  refine ⟨⟨name, params, ?_⟩, trivial⟩
  rw [declared]
  exact .const

/-- A restored former's lookup and its reader storage witness remain connected. -/
theorem restored_lookup {env : Env .anon} {checked raw : ConstantVal .anon}
    {caps rawCaps : IndCaps .anon} {alias : Key .anon} {levels : List Level}
    (found : env.find? checked.name = some (.indInfo checked caps))
    (name : checked.name = raw.name) (params : checked.levelParams = raw.levelParams)
    (declared : raw.type = .const alias levels) :
    (environment checked caps (.const alias levels) env).find? raw.name =
        some (.indInfo { checked with type := .const alias levels } caps) ∧
      StoredAs (.indInfo { checked with type := .const alias levels } caps) (.indInfo raw rawCaps) := by
  refine ⟨?_, storedAlias name params declared⟩
  rw [← name, find, found]
  simp only [Option.map_some, info, ↓reduceIte]

end IxVM.Refinement.Decl.NativeFormerRestore
