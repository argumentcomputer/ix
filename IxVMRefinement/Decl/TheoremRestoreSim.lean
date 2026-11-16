import IxVMRefinement.Decl.ReferenceFrameAt

/-! # Local theorem rows in a fixed restored final store -/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open IxVM.Refinement.Assembly (ThmSimAt ThmValueTyped)

/-- Select exactly the public theorem names in the original prepared declaration array. -/
def selectedTheorems (declarations : List (Declaration .anon)) (name : Key .anon) : Bool :=
  declarations.any fun d => match d with
    | .thmDecl cv _ => !cv.name.isAux && cv.name == name
    | _ => false

theorem selectedTheorems_iff {declarations : List (Declaration .anon)} {name : Key .anon} :
    selectedTheorems declarations name = true ↔
      ∃ cv value, Declaration.thmDecl cv value ∈ declarations ∧ cv.name.isAux = false ∧ cv.name = name := by
  simp only [selectedTheorems, List.any_eq_true]
  constructor
  · rintro ⟨d, member, selected⟩
    cases d with
    | thmDecl cv value =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at selected
      exact ⟨cv, value, member, selected⟩
    | _ => cases selected
  · rintro ⟨cv, value, member, publicName, rfl⟩
    exact ⟨.thmDecl cv value, member, by simp only [publicName, Bool.not_false, beq_self_eq_true]⟩

theorem thmToOpaqueDefn_of_public {cv : ConstantVal .anon} {value : Expr .anon}
    (publicName : cv.name.isAux = false) :
    IxVM.Refinement.thmToOpaqueDefn (.thmDecl cv value) = .defnDecl cv value .opaque := by
  cases name : cv.name with
  | id _ | role _ => simp only [IxVM.Refinement.thmToOpaqueDefn, name]
  | aux _ _ => rw [name] at publicName; cases publicName

namespace TheoremRestore

theorem info_unselected (selected : Key .anon → Bool) {ci : ConstantInfo .anon}
    (notSelected : selected ci.name = false) : info selected ci = ci := by
  cases ci with
  | defnInfo cv value hint =>
    cases hint with
    | «opaque» => simp only [info, show selected cv.name = false from notSelected, Bool.false_eq_true, ↓reduceIte]
    | «abbrev» | regular => rfl
  | _ => rfl

theorem find_unselected (selected : Key .anon → Bool) (env : Env .anon) {name : Key .anon}
    (notSelected : selected name = false) : (environment selected env).find? name = env.find? name := by
  rw [find]
  cases found : env.find? name with
  | none => rfl
  | some ci =>
    rw [Option.map_some, info_unselected selected (by rw [Env.find?_name found]; exact notSelected)]

/-- Typed rows already known at the fixed final target suffice for the whole current prefix. -/
theorem simulation_of_rows (selected : Key .anon → Bool) {before final : Env .anon}
    (extension : EnvExt before final)
    (allowed : ∀ name, selected name = true → ThmKind.AllowedKey name)
    (rows : ∀ name cv value, before.find? name = some (.defnInfo cv value .opaque) →
      selected name = true → ThmValueTyped (environment selected final) cv value) :
    ThmSimAt before (environment selected final) := by
  constructor
  · intro name cv value original restored
    by_cases chosen : selected name = true
    · exact rows name cv value original chosen
    · have sameName : cv.name = name := Env.find?_name original
      rw [find, extension.find original] at restored
      simp only [Option.map_some, info, sameName, ite_eq_right chosen] at restored
      cases restored
  · intro name ci original
    have finalFound := extension.find original
    have sameName := Env.find?_name original
    cases ci with
    | defnInfo cv value hint =>
      cases hint with
      | «opaque» =>
        change cv.name = name at sameName
        by_cases chosen : selected cv.name = true
        · have nameAllowed := allowed name (by rw [← sameName]; exact chosen)
          refine .inr ⟨cv, value, rfl, nameAllowed.1, nameAllowed.2.1,
            nameAllowed.2.2.1, nameAllowed.2.2.2, ?_⟩
          rw [find, finalFound, Option.map_some]
          simp only [info, ite_eq_left chosen]
        · exact .inl (by rw [find, finalFound, Option.map_some]; simp only [info, ite_eq_right chosen])
      | «abbrev» | regular => exact .inl (by rw [find, finalFound]; rfl)
    | _ => exact .inl (by rw [find, finalFound]; rfl)
  · intro T cv caps found
    have notSelected : selected (projTableName T) = false := by
      cases chosen : selected (projTableName T) with
      | false => rfl
      | true =>
        have noProjection := (allowed _ chosen).2.1
        rw [Ix.Kernel.Semantics.projTableName_isProjFnShape] at noProjection
        cases noProjection
    rw [find_unselected selected final notSelected]
    exact extension.tables found

private theorem typed_transfer {before after : Env .anon} (simulation : ThmSimAt before after)
    {cv : ConstantVal .anon} {value : Expr .anon} (typed : ThmValueTyped before cv value) :
    ThmValueTyped after cv value := by
  obtain ⟨closed, bounded, vt, st, u, hv, hd, ht, hs, hz⟩ := typed
  exact ⟨closed, bounded, vt, st, u, simulation.infer hv, simulation.defEq hd,
    simulation.infer ht, simulation.red hs, hz⟩

/-- Existing theorem rows and the actually changed rows together type the restored store. -/
theorem thmTyped (selected : Key .anon → Bool) {env : Env .anon}
    (simulation : ThmSimAt env (environment selected env)) (typed : ThmTyped env) :
    ThmTyped (environment selected env) := by
  intro name cv value found
  obtain ⟨original, originalFound, changed⟩ := found_original selected found
  cases original with
  | thmInfo oldCv oldValue =>
    obtain ⟨rfl, rfl⟩ := ConstantInfo.thmInfo.inj changed
    exact typed_transfer simulation (typed _ _ _ originalFound)
  | defnInfo oldCv oldValue hint =>
    cases hint with
    | «opaque» =>
      simp only [info] at changed
      split at changed
      · obtain ⟨rfl, rfl⟩ := ConstantInfo.thmInfo.inj changed
        exact simulation.thmTyped _ _ _ originalFound found
      · cases changed
    | «abbrev» | regular => cases changed
  | _ => cases changed

end TheoremRestore
end IxVM.Refinement.Decl
