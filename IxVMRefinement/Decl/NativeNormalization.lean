import IxC.Kernel.Inductives.SumInstall
import IxC.Kernel.Verify.InferLeaves
import IxC.Kernel.Verify.Rules.Bridge
import IxC.Kernel.Verify.Inductives.SumInv

/-! # Soundness of native constructor-domain normalization

The positivity walk changes a domain by actual weak-head reductions and congruence under
binders. Its opened variables are closed back without changing their annotations.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel
open Ix.Kernel.Rules (DefEq)

/-- The actual positivity normalization preserves the input's scope and is definitionally equal to it. -/
theorem normPosDom_sound {md : Mode} {env : Env md} (wellFormed : EnvWF env)
    {fuel : Nat} {T : Key md} {d steps : Nat} {e out : Expr md}
    (run : normPosDom (fueledOps .verified fuel) env T d steps e = .ok out)
    (scope : Expr.WScoped d e) (bounded : e.looseBVarsBounded 0 = true) :
    Expr.WScoped d out ∧ out.looseBVarsBounded 0 = true ∧
      (∀ leaf ∈ out.fvarLeaves, leaf ∈ e.fvarLeaves) ∧ DefEq env d e out := by
  induction steps generalizing d e out with
  | zero => cases run
  | succ steps ih =>
    simp only [normPosDom, Bool.not_eq_true] at run
    split at run
    · have resultEq := Except.ok.inj run
      subst out
      exact ⟨scope, bounded, fun _ present => present, .refl⟩
    · obtain ⟨w, reduced, rest⟩ := exceptBind_ok run
      change Ix.Kernel.whnf .verified env fuel d e = .ok w at reduced
      have wScope := whnf_WScoped wellFormed fuel reduced scope
      have wBounded := (whnfPres_looseBVars wellFormed fuel).2 reduced bounded
      have wLeaves := (whnfPres_fvarLeaves wellFormed fuel).2 reduced
      have red := Ix.Kernel.Rules.whnf_bridge reduced
      simp only [Bool.not_eq_true] at rest
      split at rest
      · have resultEq := Except.ok.inj rest
        subst out
        exact ⟨wScope, wBounded, wLeaves, .redL red .refl⟩
      · cases w with
        | forallE dom body bm =>
          dsimp only at rest wScope wBounded wLeaves red
          split at rest
          · cases rest
          · obtain ⟨bodyOut, recursive, resultEq⟩ := exceptBind_ok rest
            have resultEq := Except.ok.inj resultEq
            subst out
            have openScope := wScope.1.instantiate1 0 wScope.2
            have openBounded : (body.instantiate1 (.fvar d dom)).looseBVarsBounded 0 = true :=
              looseBVarsBounded_instantiate1 _ 0 wBounded.2
            obtain ⟨outScope, outBounded, outLeaves, outEq⟩ := ih recursive openScope openBounded
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
            have consistent := Expr.fvarConsistent_of_leafCond bodyOut
              (fun leaf present => leafCondition leaf (outLeaves leaf present))
            have roundTrip := abstract1_instantiate1 bodyOut 0 consistent outBounded
            refine ⟨⟨wScope.1, WScoped.abstract1 0 outScope⟩,
              ?_, ?_, .redL red (.forallE .refl ?_ rfl)⟩
            · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
              exact ⟨wBounded.1, looseBVarsBounded_abstract1 bodyOut 0 outBounded⟩
            · intro leaf present
              simp only [Expr.fvarLeaves, List.mem_append] at present
              apply wLeaves leaf
              simp only [Expr.fvarLeaves, List.mem_append]
              rcases present with inDom | inBody
              · exact Or.inl inDom
              · obtain ⟨inOutput, notFresh⟩ := Expr.fvarLeaves_abstract1_ne bodyOut 0 outScope leaf inBody
                rcases Expr.fvarLeaves_instantiate1 body 0 (outLeaves leaf inOutput) with inRaw | inVar
                · exact Or.inr inRaw
                · simp only [Expr.fvarLeaves, List.mem_cons] at inVar
                  rcases inVar with same | inDom
                  · subst leaf
                    exact (notFresh rfl).elim
                  · exact Or.inl inDom
            · rw [roundTrip]
              exact outEq
        | _ =>
          have resultEq := Except.ok.inj rest
          subst out
          exact ⟨wScope, wBounded, wLeaves, .redL red .refl⟩

end IxVM.Refinement.Decl
