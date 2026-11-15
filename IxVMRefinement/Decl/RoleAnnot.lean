import IxVMRefinement.Decl.ModeledAux
import IxVMRefinement.Infer.Close
import IxC.Kernel.Verify.Abstract

/-! # Reader-shape correspondence for checked kernel annotations

The actual annotation pass preserves projection names after checking them, writes arbitrary
validated binder metadata, and erases lets. Its closed outputs therefore satisfy `Annotates`,
which supplies the value correspondence required by role declaration installation.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel
open IxVM.Refinement.Core

private def fvarTypesNormalized : KExpr → Prop
  | .fvar _ ty => noLetExpr ty = true
  | .app f a => fvarTypesNormalized f ∧ fvarTypesNormalized a
  | .lam ty b _ | .forallE ty b _ => fvarTypesNormalized ty ∧ fvarTypesNormalized b
  | .letE ty v b _ => fvarTypesNormalized ty ∧ fvarTypesNormalized v ∧ fvarTypesNormalized b
  | .proj _ _ e => fvarTypesNormalized e
  | _ => True

private theorem fvarTypesNormalized_closed : ∀ {e : KExpr},
    e.hasFvar = false → fvarTypesNormalized e := by
  intro e
  induction e <;> simp_all [fvarTypesNormalized, Expr.hasFvar, Bool.or_eq_false_iff]

private theorem fvarTypesNormalized_instantiate1 {v : KExpr}
    (hv : fvarTypesNormalized v) : ∀ (e : KExpr) (k : Nat),
      fvarTypesNormalized e → fvarTypesNormalized (e.instantiate1 v k) := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> trivial
  | fvar _ _ _ => exact fun _ h => h
  | sort _ | const _ _ | lit _ => exact fun _ _ => trivial
  | app f a ihf iha =>
    intro k h
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty b m iht ihb | forallE ty b m iht ihb =>
    intro k h
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty v b m iht ihv ihb =>
    intro k h
    exact ⟨iht k h.1, ihv k h.2.1, ihb (k + 1) h.2.2⟩
  | proj s i e ih => exact fun k h => ih k h

private theorem annotates_refl_normalized : ∀ {e : KExpr},
    noLetExpr e = true → IxVM.Consistency.Annotates e e := by
  intro e
  induction e with
  | bvar _ => exact fun _ => .bvar
  | sort _ => exact fun _ => .sort
  | const _ _ => exact fun _ => .const
  | lit _ => exact fun _ => .lit
  | fvar _ _ ih => exact fun h => .fvar (ih h)
  | app f a ihf iha =>
    intro h
    simp only [noLetExpr, Bool.and_eq_true] at h
    exact .app (ihf h.1) (iha h.2)
  | lam ty b m iht ihb =>
    intro h
    simp only [noLetExpr, Bool.and_eq_true] at h
    exact .lam (iht h.1) (ihb h.2)
  | forallE ty b m iht ihb =>
    intro h
    simp only [noLetExpr, Bool.and_eq_true] at h
    exact .forallE (iht h.1) (ihb h.2)
  | letE _ _ _ _ => exact fun h => nomatch h
  | proj _ _ e ih => exact fun h => .proj (ih h)

private theorem noLetExpr_abstract1 {e : KExpr} (h : noLetExpr e = true) :
    ∀ d k, noLetExpr (e.abstract1 d k) = true := by
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => exact fun _ _ => rfl
  | fvar i ty _ =>
    intro d k
    simp only [Expr.abstract1]
    split
    · rfl
    · exact h
  | app f a ihf iha =>
    intro d k
    simp only [noLetExpr, Bool.and_eq_true] at h
    simp only [Expr.abstract1, noLetExpr, Bool.and_eq_true]
    exact ⟨ihf h.1 d k, iha h.2 d k⟩
  | lam ty b m iht ihb | forallE ty b m iht ihb =>
    intro d k
    simp only [noLetExpr, Bool.and_eq_true] at h
    simp only [Expr.abstract1, noLetExpr, Bool.and_eq_true]
    exact ⟨iht h.1 d k, ihb h.2 d (k + 1)⟩
  | letE _ _ _ _ => cases h
  | proj s i e ih => exact fun d k => ih h d k

private theorem annotates_abstract1 {e' e : KExpr}
    (h : IxVM.Consistency.Annotates e' e) :
    ∀ d k, IxVM.Consistency.Annotates (e'.abstract1 d k) (e.abstract1 d k) := by
  induction h with
  | bvar => exact fun _ _ => .bvar
  | fvar hty _ =>
    intro d k
    simp only [Expr.abstract1]
    split
    · exact .bvar
    · exact .fvar hty
  | sort => exact fun _ _ => .sort
  | const => exact fun _ _ => .const
  | lit => exact fun _ _ => .lit
  | app _ _ ihf iha => exact fun d k => .app (ihf d k) (iha d k)
  | lam _ _ iht ihb => exact fun d k => .lam (iht d k) (ihb d (k + 1))
  | forallE _ _ iht ihb => exact fun d k => .forallE (iht d k) (ihb d (k + 1))
  | proj _ ih => exact fun d k => .proj (ih d k)
  | @letE _ ty v b m _ ih =>
    intro d k
    apply IxVM.Consistency.Annotates.letE
    have heq := InferAux.abstract1_instantiate1Lift (V := v) (d := d) (k := k) (B := b) (j := 0)
    simp only [Nat.add_zero] at heq
    rw [← heq]
    exact ih d k

private theorem abstract1_instantiate1_scoped {d : Nat} (ty : KExpr) :
    ∀ {e : KExpr} (k : Nat), e.fvarsBelow d → e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1 (.fvar d ty) k).abstract1 d k = e
  | .bvar i, k, _, hb => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1]
    by_cases hik : i = k
    · subst hik; simp [Expr.abstract1]
    · rw [ite_eq_right hik, ite_eq_right (by omega)]
      rfl
  | .fvar i fty, k, hf, _ => by
    simp only [Expr.fvarsBelow] at hf
    simp [Expr.instantiate1, Expr.abstract1, Nat.ne_of_lt hf]
  | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .app f a, k, hf, hb => by
    simp only [Expr.fvarsBelow, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_scoped ty k hf.1 hb.1,
      abstract1_instantiate1_scoped ty k hf.2 hb.2]
  | .lam ty₀ b _, k, hf, hb | .forallE ty₀ b _, k, hf, hb => by
    simp only [Expr.fvarsBelow, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_scoped ty k hf.1 hb.1,
      abstract1_instantiate1_scoped ty (k + 1) hf.2 hb.2]
  | .letE ty₀ v b _, k, hf, hb => by
    simp only [Expr.fvarsBelow, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_scoped ty k hf.1 hb.1.1,
      abstract1_instantiate1_scoped ty k hf.2.1 hb.1.2,
      abstract1_instantiate1_scoped ty (k + 1) hf.2.2 hb.2]
  | .proj s i e, k, hf, hb => by
    simp only [Expr.fvarsBelow, Expr.looseBVarsBounded] at hf hb
    simpa [Expr.instantiate1, Expr.abstract1] using abstract1_instantiate1_scoped ty k hf hb

private theorem annotateCore_proj_shape {env : Env .anon} {fuel d : Nat}
    {sn : Key .anon} {i : Nat} {e e' : KExpr}
    (h : annotateCore .verified env (fuel + 1) d (.proj sn i e) = .ok e') :
    ∃ e₂, annotateCore .verified env fuel d e = .ok e₂ ∧ e' = .proj sn i e₂ := by
  obtain ⟨e₂, tt, te, he, hi, hw, T, us, entry, hfn, hfp, _, hout⟩ := annotateCore_proj_inv h
  have heq : T = sn := by
    by_contra hne
    rw [annotateCore_succ] at h
    simp [annotateBody, Bind.bind, Except.bind, annotate_def, inferTypeIO_def, whnf_def,
      he, hi, hw, hfn, hfp, hne] at h
  exact ⟨e₂, he, by rw [heq] at hout; exact hout⟩

private theorem annotateCore_shape_aux {env : Env .anon} :
    ∀ (fuel : Nat) (e : KExpr) {d : Nat} {e' : KExpr},
      annotateCore .verified env fuel d e = .ok e' → e.WScoped d →
      e.looseBVarsBounded 0 = true → fvarTypesNormalized e →
      IxVM.Consistency.Annotates e' e ∧ noLetExpr e' = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro e d e' h _ _ _
    simp [annotateCore_zero, throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel ih =>
    intro e d e' h hw hb hn
    cases e with
    | bvar i => simp [Expr.looseBVarsBounded] at hb
    | fvar i ty =>
      simp only [Expr.WScoped] at hw
      rw [annotateCore_succ] at h
      simp [annotateBody, hw.1] at h
      subst e'
      exact ⟨.fvar (annotates_refl_normalized hn), hn⟩
    | sort u =>
      rw [annotateCore_succ] at h
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
      subst e'
      exact ⟨.sort, rfl⟩
    | const n us =>
      rw [annotateCore_succ] at h
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
      subst e'
      exact ⟨.const, rfl⟩
    | lit l =>
      rw [annotateCore_succ] at h
      cases l <;> dsimp only [annotateBody] at h
      all_goals
        split at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          subst e'
          exact ⟨.lit, rfl⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h
    | app f a =>
      obtain ⟨f', a', hf, ha, rfl⟩ := annotateCore_app_inv h
      simp only [Expr.WScoped] at hw
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      obtain ⟨hfshape, hfno⟩ := ih f hf hw.1 hb.1 hn.1
      obtain ⟨hashape, hano⟩ := ih a ha hw.2 hb.2 hn.2
      exact ⟨.app hfshape hashape, by simp only [noLetExpr, hfno, hano, Bool.and_self]⟩
    | lam ty body bm =>
      obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_lam_inv h
      simp only [Expr.WScoped] at hw
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      obtain ⟨htyshape, htyno⟩ := ih ty hty hw.1 hb.1 hn.1
      have hwty' := annotateCore_WScoped fuel ty hty hw.1
      obtain ⟨hbshape, hbno⟩ := ih (body.instantiate1 (.fvar d ty')) hbody
        (hwty'.instantiate1 0 hw.2) (looseBVarsBounded_instantiate1 body 0 hb.2)
        (fvarTypesNormalized_instantiate1 (v := .fvar d ty') htyno body 0 hn.2)
      have hclosed := annotates_abstract1 hbshape d 0
      rw [abstract1_instantiate1_scoped ty' 0 hw.2.fvarsBelow hb.2] at hclosed
      exact ⟨.lam htyshape hclosed,
        by simp only [noLetExpr, Bool.and_eq_true]; exact ⟨htyno, noLetExpr_abstract1 hbno d 0⟩⟩
    | forallE ty body bm =>
      obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_forallE_inv h
      simp only [Expr.WScoped] at hw
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      obtain ⟨htyshape, htyno⟩ := ih ty hty hw.1 hb.1 hn.1
      have hwty' := annotateCore_WScoped fuel ty hty hw.1
      obtain ⟨hbshape, hbno⟩ := ih (body.instantiate1 (.fvar d ty')) hbody
        (hwty'.instantiate1 0 hw.2) (looseBVarsBounded_instantiate1 body 0 hb.2)
        (fvarTypesNormalized_instantiate1 (v := .fvar d ty') htyno body 0 hn.2)
      have hclosed := annotates_abstract1 hbshape d 0
      rw [abstract1_instantiate1_scoped ty' 0 hw.2.fvarsBelow hb.2] at hclosed
      exact ⟨.forallE htyshape hclosed,
        by simp only [noLetExpr, Bool.and_eq_true]; exact ⟨htyno, noLetExpr_abstract1 hbno d 0⟩⟩
    | letE ty value body lm =>
      obtain ⟨_, _, _, _, hbody, _⟩ := annotateCore_letE_inv h
      simp only [Expr.WScoped] at hw
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      obtain ⟨hshape, hno⟩ := ih (body.instantiate1 value) hbody
        (Expr.WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
        (Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2)
        (fvarTypesNormalized_instantiate1 hn.2.1 body 0 hn.2.2)
      refine ⟨.letE ?_, hno⟩
      rw [Expr.instantiate1Lift_eq_instantiate1 hb.1.2]
      exact hshape
    | proj sn idx inner =>
      simp only [Expr.WScoped] at hw
      obtain ⟨inner', hi, rfl⟩ := annotateCore_proj_shape h
      obtain ⟨hshape, hno⟩ := ih inner hi hw hb hn
      exact ⟨.proj hshape, hno⟩

/-- A successful kernel annotation of a closed reader expression preserves its declared shape,
while allowing changed binder metadata and erasing lets. -/
theorem annotateCore_to_annotates {env : Env .anon} {fuel : Nat} {e e' : KExpr}
    (h : annotateCore .verified env fuel 0 e = .ok e')
    (hfv : e.hasFvar = false) (hb : e.looseBVarsBounded 0 = true) :
    IxVM.Consistency.Annotates e' e :=
  (annotateCore_shape_aux fuel e h (Expr.WScoped.of_not_hasFvar hfv) hb
    (fvarTypesNormalized_closed hfv)).1

end IxVM.Refinement.Decl
