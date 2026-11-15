import IxVMRefinement.Decl.NativeFormerDelta
import IxVMRefinement.Decl.NativeFormerRestoreInstall
import IxVMRefinement.Decl.RoleAnnot
import IxVMRefinement.Decl.NativeTelescopeNormalization

/-! # Checked declarations after native former restoration

The first constant check supplies the annotation of the original reader type. Restoring that
type through an actual definition unfolding preserves the model and recovers the original
reader storage relation, including the exact name and universe-parameter list.
-/

namespace IxVM.Refinement.Decl.NativeFormerRestore

open Ix.Kernel Ix.Kernel.Semantics
open IxVM.Consistency (StoredAs ValStored)

universe u

/-- The initial constant check supplies the public annotation relation directly. -/
theorem initiallyStored {fuel : Nat} {env : Env .anon} {raw initial : ConstantVal .anon}
    (run : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial) :
    ValStored initial raw := by
  obtain ⟨_, _, _, _, bounded, closed, type, _, _, annotated, _, _, _, _, rfl⟩ :=
    checkConstantVal_inv run
  exact ⟨rfl, rfl, annotateCore_to_annotates annotated closed bounded⟩

/-- Native telescope rebuilding retains the initial name and universe parameters. -/
theorem telescope_signature {fuel count : Nat} {env : Env .anon}
    {raw initial checked : ConstantVal .anon} {sort : Level}
    (first : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial)
    (tele : checkSumTele (fueledOps .verified fuel) env raw count initial = .ok (checked, sort)) :
    checked.name = initial.name ∧ checked.levelParams = initial.levelParams := by
  rcases checkSumTele_origin tele with ⟨rfl, _⟩ | ⟨bs, _, rechecked⟩
  · exact ⟨rfl, rfl⟩
  · have original := constantValCheckJ_of_run first
    have normalized := constantValCheckJ_of_run rechecked
    exact ⟨normalized.name_eq.trans original.name_eq.symm,
      normalized.levelParams_eq.trans original.levelParams_eq.symm⟩

/-- Restoring the first checked annotation recovers the reader's storage shape. -/
theorem storedInitial {raw initial checked : ConstantVal .anon} {caps rawCaps : IndCaps .anon}
    (initialStored : ValStored initial raw)
    (signature : checked.name = initial.name ∧ checked.levelParams = initial.levelParams) :
    StoredAs (.indInfo { checked with type := initial.type } caps) (.indInfo raw rawCaps) := by
  exact ⟨⟨signature.1.trans initialStored.1, signature.2.trans initialStored.2.1,
    initialStored.2.2⟩, trivial⟩

/-- The two actual checks and the actual unfolding produce both the restored model and storage. -/
theorem checkedUnfolding {V : Type u} [SetTheory V] {before final : Env .anon}
    {raw initial checked : ConstantVal .anon} {caps rawCaps : IndCaps .anon}
    {fuel count : Nat} {sort : Level}
    (first : checkConstantVal (fueledOps .verified fuel) before raw = .ok initial)
    (tele : checkSumTele (fueledOps .verified fuel) before raw count initial = .ok (checked, sort))
    (M : Model V final) (found : final.find? checked.name = some (.indInfo checked caps))
    (notEta : caps.eta = false) (notUnit : caps.unitlike = false)
    (noTable : ∀ i, final.findProj? checked.name i = none)
    (unfolded : unfoldDefinition final initial.type = some checked.type) :
    ∃ restored : Model V (environment checked caps initial.type final),
      restored.cval = M.cval ∧
      (environment checked caps initial.type final).find? raw.name =
        some (.indInfo { checked with type := initial.type } caps) ∧
      StoredAs (.indInfo { checked with type := initial.type } caps) (.indInfo raw rawCaps) := by
  have signature := telescope_signature first tele
  have originalStored := initiallyStored first
  refine ⟨unfoldingModel checked caps initial.type M (List.mem_of_find?_eq_some found)
    notEta notUnit noTable unfolded, rfl, ?_, storedInitial originalStored signature⟩
  have name : checked.name = raw.name := signature.1.trans originalStored.1
  rw [← name, find, found]
  simp only [Option.map_some, info, ↓reduceIte]

end IxVM.Refinement.Decl.NativeFormerRestore
