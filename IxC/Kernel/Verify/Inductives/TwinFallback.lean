module

public import IxC.Kernel.Verify.Inductives.TwinRun
public import IxC.Kernel.Verify.Extend.Modeled
public import IxC.Kernel.Verify.ExceptBind

public section

/-! # Existing modeled acceptance is outside the stored-twin dispatch -/

namespace Ix.Kernel.NativeTwin

open Ix.Kernel.Semantics

private theorem member_model {mode : CheckMode} {fuel : Nat} {env : Env md}
    {names : List (Key md)} {raw checked : ConstantVal md}
    (h : checkMemberVal (fueledOps mode fuel) names env raw = .ok checked) :
    ∃ cv value hint, env.find? (auxKey raw.name .model) = some (.defnInfo cv value hint) := by
  obtain ⟨hcheck, _, cv, value, hint, hmodel, _, _⟩ := checkMemberVal_inv h
  have hname := (constantValCheckJ_of_run hcheck).name_eq
  rw [hname] at hmodel
  exact ⟨cv, value, hint, hmodel⟩

private theorem defn_lookup_of_rec_cons {env : Env md} {recursor : ConstantVal md} {mI rP : Nat}
    {rules : List (RecRule md)} {name : Key md} {cv : ConstantVal md} {value : Expr md}
    {hint : ReducibilityHint}
    (h : (⟨.recInfo recursor mI rP rules :: env.consts⟩ : Env md).find? name =
      some (.defnInfo cv value hint)) : env.find? name = some (.defnInfo cv value hint) := by
  rw [Env.find?_cons] at h
  split at h
  · cases h
  · exact h

private theorem provision_models {mode : CheckMode} {fuel : Nat} (names : List (Key md)) :
    ∀ (env : Env md) (block : List (ConstantInfo md))
      {result : Env md × List (ConstantVal md × Nat × Nat × List (RecRule md))},
      provisionRecs (fueledOps mode fuel) names env block = .ok result →
      ∀ ci ∈ block, ∃ cv value hint, env.find? (auxKey ci.name .model) = some (.defnInfo cv value hint)
  | _, [], _, _, _, hci => by cases hci
  | env, ci :: block, result, h, found, hfound => by
    cases ci with
    | recInfo raw mI rP rules =>
      rw [provisionRecs] at h
      obtain ⟨checked, hmember, h⟩ := exceptBind_ok h
      obtain ⟨next, hrest, _⟩ := exceptBind_ok h
      rcases List.mem_cons.mp hfound with rfl | hfound
      · exact member_model hmember
      · obtain ⟨cv, value, hint, hmodel⟩ := provision_models names _ block hrest found hfound
        exact ⟨cv, value, hint, defn_lookup_of_rec_cons hmodel⟩
    | _ => cases h

private theorem indRecs_models {mode : CheckMode} {fuel : Nat} {env output : Env md}
    {names : List (Key md)} {block : List (ConstantInfo md)}
    (h : checkIndRecs mode (fueledOps mode fuel) names env block = .ok output) :
    ∀ ci ∈ block, ∃ cv value hint, env.find? (auxKey ci.name .model) = some (.defnInfo cv value hint) := by
  by_cases hempty : block.isEmpty = true
  · have hnil := List.isEmpty_iff.mp hempty
    subst block
    intro ci hci
    cases hci
  · unfold checkIndRecs at h
    simp only [hempty] at h
    by_cases heq : env.find? eqName = some eqA
    · simp only [if_pos heq, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨result, hprovision, _⟩ := exceptBind_ok h
      exact provision_models names env block hprovision
    · simp [heq, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- A successful old modeled run has every own model companion required by a recursor-only
block. It therefore remains on the modeled side of the structural twin dispatch. -/
theorem modeled_not_usesStoredRecursors {mode : CheckMode} {fuel : Nat} {env output : Env md}
    {block : List (ConstantInfo md)}
    (h : checkModeled mode (fueledOps mode fuel) env block = .ok output) :
    usesStoredRecursors env.find? block = false := by
  unfold usesStoredRecursors
  by_cases hempty : block.isEmpty = true
  · simp only [hempty, Bool.not_true, Bool.false_and]
  · by_cases hall : block.all (fun | .recInfo .. => true | _ => false) = true
    · have recs : block.filter (fun | .recInfo .. => true | _ => false) = block :=
        List.filter_eq_self.mpr (List.all_eq_true.mp hall)
      have nonrecs : block.filter (fun | .recInfo .. => false | _ => true) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro ci hci
        have hc := List.all_eq_true.mp hall ci hci
        cases ci <;> simp_all
      have inductives : block.filter (fun | .indInfo .. => true | _ => false) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro ci hci
        have hc := List.all_eq_true.mp hall ci hci
        cases ci <;> simp_all
      have constructors : block.filter (fun | .ctorInfo .. => true | _ => false) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro ci hci
        have hc := List.all_eq_true.mp hall ci hci
        cases ci <;> simp_all
      have hsuffix : @decide _ (blockRecSuffixDec block) = true := by
        simp only [decide_eq_true_eq]
        rw [nonrecs, recs]
        rfl
      unfold checkModeled at h
      simp only [hsuffix, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
      rw [inductives, constructors] at h
      simp only [nonrecs, recs, List.foldlM_nil, bind, Except.bind, pure, Except.pure] at h
      have models := indRecs_models h
      have present : block.all (fun ci => match env.find? (auxKey ci.name .model) with
          | some (.defnInfo ..) => true | _ => false) = true := by
        apply List.all_eq_true.mpr
        intro ci hci
        obtain ⟨cv, value, hint, hmodel⟩ := models ci hci
        rw [hmodel]
      simp only [present, Bool.not_true, Bool.and_false]
    · have hfalse : block.all (fun | .recInfo .. => true | _ => false) = false :=
        Bool.eq_false_iff.mpr hall
      simp only [hfalse, Bool.and_false, Bool.false_and]

end Ix.Kernel.NativeTwin
