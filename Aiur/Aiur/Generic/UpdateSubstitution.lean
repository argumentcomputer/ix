import Aiur.Generic.Update
import Aiur.Generic.TypeFacts

namespace Aiur.Generic.Update

@[simp] theorem position_subst (step : UpdateStep) : (step.subst types).position = step.position := by
  cases step <;> rfl
@[simp] theorem width_subst (step : UpdateStep) : (step.subst types).width = step.width := by
  cases step <;> rfl
@[simp] theorem owner_subst (step : UpdateStep) :
    (step.subst types).owner = step.owner.map (Ty.subst types) := by
  cases step with
  | member field => cases h : field.owner <;> simp [h, UpdateStep.subst, UpdateStep.owner, FieldRef.subst, Ty.subst]
  | project | index => rfl

@[simp] theorem pack_subst (step : UpdateStep) (values : List (SourceValue F)) :
    pack [] (step.subst types) values = pack types step values := by
  simp only [pack, owner_subst]
  cases step.owner <;> simp [nominalName]

@[simp] theorem unpack_subst (step : UpdateStep) (value : SourceValue F) :
    unpack [] (step.subst types) value = unpack types step value := by
  simp only [unpack, owner_subst, width_subst]
  cases step.owner <;> cases value <;> simp [nominalName]

@[simp] theorem replace_subst (path : UpdatePath) (base replacement : SourceValue F) :
    replace [] (path.map (UpdateStep.subst types)) base replacement = replace types path base replacement := by
  induction path generalizing base with
  | nil => rfl
  | cons step path ih => simp only [List.map_cons, replace, unpack_subst, position_subst, ih, pack_subst]

@[simp] theorem apply_subst (paths : List UpdatePath) (base : SourceValue F) (replacements : List (SourceValue F)) :
    apply [] (paths.map (List.map (UpdateStep.subst types))) base replacements = apply types paths base replacements := by
  induction paths generalizing base replacements with
  | nil => cases replacements <;> rfl
  | cons path paths ih => cases replacements <;> simp only [List.map_cons, apply, replace_subst, ih]

@[simp] theorem value_subst (paths : List UpdatePath) (values : List (SourceValue F)) :
    value [] (paths.map (List.map (UpdateStep.subst types))) values = value types paths values := by
  cases values <;> simp only [value, apply_subst]

end Aiur.Generic.Update
