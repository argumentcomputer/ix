import IxVMRefinement.Decl.RoleAnnot
import IxVMRefinement.Decl.AnnotationIdempotent

/-! # Reference support of the input to a successful annotation

Resolved outputs retain every input constant reference. A let's erased type and value are
covered by the inference calls that the annotation pass actually performs before erasure.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel
open IxVM.Refinement.Core

private theorem fvar_resolves_iff {env : Env .anon} (e : KExpr) :
    FvarConstsResolve env e ↔ ∀ leaf ∈ e.fvarLeaves, leaf.2.constsResolve env = true := by
  induction e <;> simp_all [FvarConstsResolve, Expr.fvarLeaves, or_imp, forall_and]

private theorem fvar_resolves_of_resolved {env : Env .anon} {e : KExpr}
    (resolved : e.constsResolve env = true) : FvarConstsResolve env e := by
  induction e <;> simp_all [Expr.constsResolve, FvarConstsResolve, Bool.and_eq_true]

private theorem fvar_resolves_instantiate {env : Env .anon} {e value : KExpr}
    (body : FvarConstsResolve env e) (argument : FvarConstsResolve env value) (cut : Nat) :
    FvarConstsResolve env (e.instantiate1 value cut) := by
  apply (fvar_resolves_iff _).mpr
  intro leaf present
  rcases Expr.fvarLeaves_instantiate1 e cut present with inBody | inValue
  · exact (fvar_resolves_iff _).mp body leaf inBody
  · exact (fvar_resolves_iff _).mp argument leaf inValue

private theorem fvar_resolves_annotated {env : Env .anon} {fuel d : Nat} {e out : KExpr}
    (run : annotateCore .verified env fuel d e = .ok out)
    (scope : Expr.WScoped d e) (bounded : e.looseBVarsBounded 0 = true)
    (resolvedVars : FvarConstsResolve env e) : FvarConstsResolve env out := by
  apply (fvar_resolves_iff _).mpr
  intro leaf present
  exact (fvar_resolves_iff _).mp resolvedVars leaf (annotateCore_leaves_sub fuel e run scope bounded leaf present)

private theorem resolved_before_instantiate {env : Env .anon} {value : KExpr} :
    ∀ (e : KExpr) (cut : Nat), (e.instantiate1 value cut).constsResolve env = true →
      e.constsResolve env = true := by
  intro e
  induction e with
  | bvar _ => intro _ _; rfl
  | sort _ | const _ _ | lit _ | fvar _ _ _ => intro _ resolved; exact resolved
  | app f a ihf iha =>
    intro cut resolved
    simp only [Expr.instantiate1, Expr.constsResolve, Bool.and_eq_true] at resolved ⊢
    exact ⟨ihf cut resolved.1, iha cut resolved.2⟩
  | lam ty body bm iht ihb | forallE ty body bm iht ihb =>
    intro cut resolved
    simp only [Expr.instantiate1, Expr.constsResolve, Bool.and_eq_true] at resolved ⊢
    exact ⟨iht cut resolved.1, ihb (cut + 1) resolved.2⟩
  | letE ty val body bm iht ihv ihb =>
    intro cut resolved
    simp only [Expr.instantiate1, Expr.constsResolve, Bool.and_eq_true] at resolved ⊢
    exact ⟨⟨iht cut resolved.1.1, ihv cut resolved.1.2⟩, ihb (cut + 1) resolved.2⟩
  | proj name i inner ih =>
    intro cut resolved
    simp only [Expr.instantiate1, Expr.constsResolve, Bool.and_eq_true] at resolved ⊢
    exact ⟨resolved.1, ih cut resolved.2⟩

/-- A successful annotation with resolved output has a resolved original input. -/
theorem annotateCore_input_resolves {env : Env .anon} (store : Ix.Kernel.Open.StoreInv env)
    {fuel d : Nat} {e out : KExpr}
    (run : annotateCore .verified env fuel d e = .ok out)
    (scope : Expr.WScoped d e) (bounded : e.looseBVarsBounded 0 = true)
    (resolvedVars : FvarConstsResolve env e) (resolved : out.constsResolve env = true) :
    e.constsResolve env = true := by
  induction fuel generalizing d e out with
  | zero => cases run
  | succ fuel ih =>
    cases e with
    | bvar _ | sort _ => rfl
    | fvar _ _ => exact resolvedVars.1
    | const name levels =>
      rw [annotateCore_succ] at run
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at run
      subst out
      exact resolved
    | lit literal =>
      rw [annotateCore_succ] at run
      cases literal <;> dsimp only [annotateBody] at run
      all_goals
        split at run
        · have same := Except.ok.inj run
          subst out
          exact resolved
        · cases run
    | app f a =>
      obtain ⟨f', a', hf, ha, rfl⟩ := annotateCore_app_inv run
      simp only [Expr.WScoped] at scope
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
      simp only [FvarConstsResolve] at resolvedVars
      simp only [Expr.constsResolve, Bool.and_eq_true] at resolved ⊢
      exact ⟨ih hf scope.1 bounded.1 resolvedVars.1 resolved.1,
        ih ha scope.2 bounded.2 resolvedVars.2 resolved.2⟩
    | forallE ty body binderMeta =>
      obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_forallE_inv run
      simp only [Expr.WScoped] at scope
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
      simp only [FvarConstsResolve] at resolvedVars
      simp only [Expr.constsResolve, Bool.and_eq_true] at resolved ⊢
      have tyScope := annotateCore_WScoped fuel ty hty scope.1
      have reopen := annotateCore_reclose tyScope scope.2 bounded.2 hbody
      have bodyResolved : body'.constsResolve env = true := by
        have opened := Expr.constsResolve_instantiate1_gen
          (show (.fvar d ty' : KExpr).constsResolve env = true from resolved.1) 0 resolved.2
        rwa [reopen] at opened
      have bodyVariables := fvar_resolves_instantiate resolvedVars.2
        (show FvarConstsResolve env (.fvar d ty') from
          ⟨resolved.1, fvar_resolves_of_resolved resolved.1⟩) 0
      have bodyInput := ih hbody (tyScope.instantiate1 0 scope.2)
        (looseBVarsBounded_instantiate1 _ 0 bounded.2) bodyVariables bodyResolved
      exact ⟨ih hty scope.1 bounded.1 resolvedVars.1 resolved.1,
        resolved_before_instantiate body 0 bodyInput⟩
    | lam ty body binderMeta =>
      obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_lam_inv run
      simp only [Expr.WScoped] at scope
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
      simp only [FvarConstsResolve] at resolvedVars
      simp only [Expr.constsResolve, Bool.and_eq_true] at resolved ⊢
      have tyScope := annotateCore_WScoped fuel ty hty scope.1
      have reopen := annotateCore_reclose tyScope scope.2 bounded.2 hbody
      have bodyResolved : body'.constsResolve env = true := by
        have opened := Expr.constsResolve_instantiate1_gen
          (show (.fvar d ty' : KExpr).constsResolve env = true from resolved.1) 0 resolved.2
        rwa [reopen] at opened
      have bodyVariables := fvar_resolves_instantiate resolvedVars.2
        (show FvarConstsResolve env (.fvar d ty') from
          ⟨resolved.1, fvar_resolves_of_resolved resolved.1⟩) 0
      have bodyInput := ih hbody (tyScope.instantiate1 0 scope.2)
        (looseBVarsBounded_instantiate1 _ 0 bounded.2) bodyVariables bodyResolved
      exact ⟨ih hty scope.1 bounded.1 resolvedVars.1 resolved.1,
        resolved_before_instantiate body 0 bodyInput⟩
    | letE ty value body binderMeta =>
      obtain ⟨ty', value', hty, hvalue, hbody, _, _, _, typeInferred, _, valueInferred, _⟩ :=
        annotateCore_letE_inv run
      simp only [Expr.WScoped] at scope
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
      simp only [FvarConstsResolve] at resolvedVars
      have typeResolved := infer_constsResolve_open (Rules.inferTypeCore_bridge typeInferred) rfl store
        (fvar_resolves_annotated hty scope.1 bounded.1.1 resolvedVars.1)
      have valueResolved := infer_constsResolve_open (Rules.inferTypeCore_bridge valueInferred) rfl store
        (fvar_resolves_annotated hvalue scope.2.1 bounded.1.2 resolvedVars.2.1)
      have bodyInput := ih hbody (Expr.WScoped.instantiate1_gen scope.2.1 0 scope.2.2)
        (Expr.looseBVarsBounded_instantiate1_gen bounded.1.2 bounded.2)
        (fvar_resolves_instantiate resolvedVars.2.2 resolvedVars.2.1 0) resolved
      simp only [Expr.constsResolve, Bool.and_eq_true]
      exact ⟨⟨ih hty scope.1 bounded.1.1 resolvedVars.1 typeResolved,
        ih hvalue scope.2.1 bounded.1.2 resolvedVars.2.1 valueResolved⟩,
        resolved_before_instantiate body 0 bodyInput⟩
    | proj name i inner =>
      obtain ⟨inner', checked, rfl⟩ := annotateCore_project_shape run
      simp only [Expr.WScoped] at scope
      simp only [Expr.looseBVarsBounded] at bounded
      simp only [FvarConstsResolve] at resolvedVars
      simp only [Expr.constsResolve, Bool.and_eq_true] at resolved ⊢
      exact ⟨resolved.1, ih checked scope bounded resolvedVars resolved.2⟩

/-- The constant front's real checks establish support of its raw reader type, including erased lets. -/
theorem constantValRun_input_resolves {env : Env .anon} (store : Ix.Kernel.Open.StoreInv env)
    {fuel : Nat} {cv : ConstantVal .anon} {type : KExpr}
    (run : Ix.Kernel.Semantics.ConstantValRun .verified fuel env cv type) :
    cv.type.constsResolve env = true := by
  obtain ⟨_, _, _, _, bounded, closed, annotated, _, resolved, _⟩ := run
  exact annotateCore_input_resolves store annotated (Expr.WScoped.of_not_hasFvar closed) bounded
    (fvarConstsResolve_of_hasFvar_false closed) resolved

end IxVM.Refinement.Decl
