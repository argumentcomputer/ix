import IxVMRefinement.Decl.NativeNormalization

/-! # The actual native former telescope normalization

Every weak-head reduction is retained in a conversion derivation. Closing the opened
binders preserves the original variable annotations, scope, and dependency leaves.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel
open Ix.Kernel.Rules (DefEq)

/-- The former's normalization is a conversion of its initially checked declared type. -/
theorem whnfTelescope_sound {md : Mode} {env : Env md} (wellFormed : EnvWF env)
    {fuel d count : Nat} {e : Expr md} {binders : List (Expr md × BinderMeta)} {sort : Level}
    (run : whnfTelescope (fueledOps .verified fuel) env d count e = .ok (binders, sort))
    (scope : Expr.WScoped d e) (bounded : e.looseBVarsBounded 0 = true) :
    binders.length = count ∧
      Expr.WScoped d (closeTelescope binders d (.sort sort)) ∧
      (closeTelescope binders d (.sort sort)).looseBVarsBounded 0 = true ∧
      (∀ leaf ∈ (closeTelescope binders d (.sort sort)).fvarLeaves, leaf ∈ e.fvarLeaves) ∧
      DefEq env d e (closeTelescope binders d (.sort sort)) := by
  induction count generalizing d e binders sort with
  | zero =>
    simp only [whnfTelescope] at run
    obtain ⟨w, reduced, rest⟩ := exceptBind_ok run
    change Ix.Kernel.whnf .verified env fuel d e = .ok w at reduced
    cases w with
    | sort s =>
      have same := Except.ok.inj rest
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      refine ⟨rfl, by simp only [closeTelescope, Expr.WScoped], rfl, ?_, .redL (Ix.Kernel.Rules.whnf_bridge reduced) .refl⟩
      intro leaf present
      simp only [closeTelescope, Expr.fvarLeaves, List.not_mem_nil] at present
    | _ => cases rest
  | succ count ih =>
    simp only [whnfTelescope] at run
    obtain ⟨w, reduced, rest⟩ := exceptBind_ok run
    change Ix.Kernel.whnf .verified env fuel d e = .ok w at reduced
    have wScope := whnf_WScoped wellFormed fuel reduced scope
    have wBounded := (whnfPres_looseBVars wellFormed fuel).2 reduced bounded
    have wLeaves := (whnfPres_fvarLeaves wellFormed fuel).2 reduced
    have red := Ix.Kernel.Rules.whnf_bridge reduced
    cases w with
    | forallE dom body bm =>
      obtain ⟨pair, recursive, result⟩ := exceptBind_ok rest
      obtain ⟨tail, outSort⟩ := pair
      have same := Except.ok.inj result
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      simp only [Expr.WScoped] at wScope
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at wBounded
      obtain ⟨length, outScope, outBounded, outLeaves, outEq⟩ := ih recursive
        (wScope.1.instantiate1 0 wScope.2) (looseBVarsBounded_instantiate1 _ 0 wBounded.2)
      have leafCondition : Expr.LeafCond d dom (body.instantiate1 (.fvar d dom)) := by
        intro leaf present sameIndex
        rcases Expr.fvarLeaves_instantiate1 body 0 present with inBody | inVar
        · have lt := Expr.fvarLeaves_lt_of_wscoped wScope.2 leaf inBody
          omega
        · simp only [Expr.fvarLeaves, List.mem_cons] at inVar
          rcases inVar with rfl | inDom
          · rfl
          · have lt := Expr.fvarLeaves_lt_of_wscoped wScope.1 leaf inDom
            omega
      have consistent := Expr.fvarConsistent_of_leafCond (closeTelescope tail (d + 1) (.sort outSort))
        (fun leaf present => leafCondition leaf (outLeaves leaf present))
      have roundTrip := abstract1_instantiate1 _ 0 consistent outBounded
      refine ⟨by simp only [List.length_cons, length], ?_, ?_, ?_, .redL red (.forallE .refl ?_ rfl)⟩
      · simp only [closeTelescope, Expr.WScoped]
        exact ⟨wScope.1, WScoped.abstract1 0 outScope⟩
      · simp only [closeTelescope, Expr.looseBVarsBounded, Bool.and_eq_true]
        exact ⟨wBounded.1, looseBVarsBounded_abstract1 _ 0 outBounded⟩
      · intro leaf present
        simp only [closeTelescope, Expr.fvarLeaves, List.mem_append] at present
        apply wLeaves leaf
        simp only [Expr.fvarLeaves, List.mem_append]
        rcases present with inDom | inBody
        · exact Or.inl inDom
        · obtain ⟨inOutput, notFresh⟩ := Expr.fvarLeaves_abstract1_ne _ 0 outScope leaf inBody
          rcases Expr.fvarLeaves_instantiate1 body 0 (outLeaves leaf inOutput) with inRaw | inVar
          · exact Or.inr inRaw
          · simp only [Expr.fvarLeaves, List.mem_cons] at inVar
            rcases inVar with same | inDom
            · subst leaf
              exact (notFresh rfl).elim
            · exact Or.inl inDom
      · rw [roundTrip]
        exact outEq
    | _ => cases rest

/-- The telescope check keeps the exact normalization run before rechecking its output. -/
theorem checkSumTele_origin {md : Mode} {env : Env md} {cv original checked : ConstantVal md}
    {fuel count : Nat} {sort : Level}
    (run : checkSumTele (fueledOps .verified fuel) env cv count original = .ok (checked, sort)) :
    (checked = original ∧ ∃ bs, original.type.stripPis count = some (bs, .sort sort)) ∨
      ∃ bs, whnfTelescope (fueledOps .verified fuel) env 0 count original.type = .ok (bs, sort) ∧
        checkConstantVal (fueledOps .verified fuel) env
          { cv with type := closeTelescope bs 0 (.sort sort) } = .ok checked := by
  unfold checkSumTele at run
  split at run
  · next bs s found =>
    have same := Except.ok.inj run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact Or.inl ⟨rfl, bs, found⟩
  · obtain ⟨pair, normalized, rest⟩ := exceptBind_ok run
    obtain ⟨bs, s⟩ := pair
    obtain ⟨out, rechecked, result⟩ := exceptBind_ok rest
    have same := Except.ok.inj result
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact Or.inr ⟨bs, normalized, rechecked⟩

end IxVM.Refinement.Decl
