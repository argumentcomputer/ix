import IxVMRefinement.Decl.NativeRec

/-! # Level parameters of a related annotation

`Expr.allLevelParamsDefined` asks two things of a term: that the levels of its sorts and
constants have their parameters among `lps`, and that the zero-ness data of its binders do. A
term `d` that annotates a term `e` and is related by `WrapRelSem` to a term `g` gets each half
from one side:

* its binder data are `g`'s (`WrapRelSem` compares binder data exactly, a consumption keeps an
  argument of an application spine, and an annotation has no `let`, so `WrapRelSem`'s `zeta`
  arm does not occur);
* its sorts and constants are `e`'s (`Annotates` keeps them, and its `let` arm instantiates,
  which keeps the parameters of the value and the body).

`wrapRelSem_annot_allLevelParamsDefined` recombines the two halves.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Ix.Kernel (Expr LevelParam)
open IxVM.Refinement.Core (KExpr KKey)

/-! ## The binder-data half -/

/-- The zero-ness data of every binder of a term (free variables' types included) have their
parameters among `lps`. -/
private def binderPWDefined (lps : List LevelParam) : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar _ ty => binderPWDefined lps ty
  | .app f a => binderPWDefined lps f && binderPWDefined lps a
  | .lam ty b m | .forallE ty b m =>
    (binderPWDefined lps ty && binderPWDefined lps b) && m.pw.paramsDefined lps
  | .letE ty v b _ =>
    (binderPWDefined lps ty && binderPWDefined lps v) && binderPWDefined lps b
  | .proj _ _ e => binderPWDefined lps e

/-- No `let` node, free variables' types included. -/
private def letFreeDeep : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar _ ty => letFreeDeep ty
  | .app f a => letFreeDeep f && letFreeDeep a
  | .lam ty b _ | .forallE ty b _ => letFreeDeep ty && letFreeDeep b
  | .letE _ _ _ _ => false
  | .proj _ _ e => letFreeDeep e

/-- An annotation has no `let`, free variables' types included. -/
private theorem annotates_letFreeDeep {a e : KExpr} (h : IxVM.Consistency.Annotates a e) :
    letFreeDeep a = true := by
  induction h with
  | bvar | sort | const | lit => rfl
  | fvar _ ih => simp only [letFreeDeep]; exact ih
  | app _ _ ihf iha =>
    simp only [letFreeDeep, Bool.and_eq_true]; exact ⟨ihf, iha⟩
  | lam _ _ iht ihb =>
    simp only [letFreeDeep, Bool.and_eq_true]; exact ⟨iht, ihb⟩
  | forallE _ _ iht ihb =>
    simp only [letFreeDeep, Bool.and_eq_true]; exact ⟨iht, ihb⟩
  | proj _ ih => simp only [letFreeDeep]; exact ih
  | letE _ ih => exact ih

/-- **`WrapRelSem` carries binder data**: a `let`-free term related to a term whose level
parameters are among `lps` has its binder data's parameters among `lps`. -/
private theorem wrapRelSem_binderPWDefined
    {find? : KKey → Option (Ix.Kernel.ConstantInfo .anon)} {lps : List LevelParam}
    {g d : KExpr} (hw : Decl.WrapRelSem find? g d) (hg : g.allLevelParamsDefined lps = true)
    (hd : letFreeDeep d = true) : binderPWDefined lps d = true := by
  have hP : ∀ f x : KExpr, (Expr.app f x).allLevelParamsDefined lps = true →
      f.allLevelParamsDefined lps = true ∧ x.allLevelParamsDefined lps = true := by
    intro f x h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    exact h
  exact Decl.WrapRelSem.rec (find? := find?)
    (motive_1 := fun g d _ => g.allLevelParamsDefined lps = true → letFreeDeep d = true →
      binderPWDefined lps d = true)
    (motive_2 := fun t t' _ => t.allLevelParamsDefined lps = true → letFreeDeep t' = true →
      binderPWDefined lps t' = true)
    (bvar := fun _ _ _ => rfl)
    (fvar := fun _ ih hg hl => by
      simp only [Expr.allLevelParamsDefined] at hg
      simp only [letFreeDeep] at hl
      simp only [binderPWDefined]
      exact ih hg hl)
    (sort := fun _ _ _ => rfl)
    (const := fun _ _ _ => rfl)
    (lit := fun _ _ _ => rfl)
    (app := fun _ _ ihf iha hg hl => by
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hg
      simp only [letFreeDeep, Bool.and_eq_true] at hl
      simp only [binderPWDefined, Bool.and_eq_true]
      exact ⟨ihf hg.1 hl.1, iha hg.2 hl.2⟩)
    (lam := fun hpw _ _ iht ihb hg hl => by
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hg
      simp only [letFreeDeep, Bool.and_eq_true] at hl
      simp only [binderPWDefined, Bool.and_eq_true]
      refine ⟨⟨iht hg.1.1 hl.1, ihb hg.1.2 hl.2⟩, ?_⟩
      rw [← hpw]
      exact hg.2)
    (forallE := fun hpw _ _ iht ihb hg hl => by
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hg
      simp only [letFreeDeep, Bool.and_eq_true] at hl
      simp only [binderPWDefined, Bool.and_eq_true]
      refine ⟨⟨iht hg.1.1 hl.1, ihb hg.1.2 hl.2⟩, ?_⟩
      rw [← hpw]
      exact hg.2)
    (letE := fun _ _ _ _ _ _ _ hl => by simp [letFreeDeep] at hl)
    (proj := fun _ ih hg hl => by
      simp only [Expr.allLevelParamsDefined] at hg
      simp only [letFreeDeep] at hl
      simp only [binderPWDefined]
      exact ih hg hl)
    (zeta := fun _ _ _ hl => by simp [letFreeDeep] at hl)
    (keep := fun _ ih hg hl => ih hg hl)
    (consume := fun hc _ ih hg hl =>
      ih (Ix.Kernel.Semantics.consumeWrapper_of
        (P := fun e : KExpr => e.allLevelParamsDefined lps = true) hP hc hg) hl)
    hw hg hd

/-! ## The levels half -/

private theorem allLPD_liftLooseBVars {lps : List LevelParam} (n : Nat) :
    ∀ (e : KExpr) (c : Nat),
      e.allLevelParamsDefined lps = true →
      (e.liftLooseBVars n c).allLevelParamsDefined lps = true
  | .bvar _, _, _ => by
    simp only [Expr.liftLooseBVars]
    split <;> rfl
  | .fvar _ _, _, h => h
  | .sort _, _, h => h
  | .const _ _, _, h => h
  | .lit _, _, _ => rfl
  | .app f a, c, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨allLPD_liftLooseBVars n f c h.1, allLPD_liftLooseBVars n a c h.2⟩
  | .lam ty b _, c, h | .forallE ty b _, c, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLPD_liftLooseBVars n ty c h.1.1, allLPD_liftLooseBVars n b (c + 1) h.1.2⟩, h.2⟩
  | .letE ty v b _, c, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLPD_liftLooseBVars n ty c h.1.1, allLPD_liftLooseBVars n v c h.1.2⟩,
      allLPD_liftLooseBVars n b (c + 1) h.2⟩
  | .proj _ _ e, c, h => by
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined]
    exact allLPD_liftLooseBVars n e c h

private theorem allLPD_instantiate1Lift {lps : List LevelParam} {v : KExpr}
    (hv : v.allLevelParamsDefined lps = true) :
    ∀ (b : KExpr) (j : Nat),
      b.allLevelParamsDefined lps = true →
      (b.instantiate1Lift v j).allLevelParamsDefined lps = true
  | .bvar _, j, _ => by
    simp only [Expr.instantiate1Lift]
    split
    · exact allLPD_liftLooseBVars j v 0 hv
    · split <;> rfl
  | .fvar _ _, _, hb => hb
  | .sort _, _, hb => hb
  | .const _ _, _, hb => hb
  | .lit _, _, _ => rfl
  | .app f a, j, hb => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨allLPD_instantiate1Lift hv f j hb.1, allLPD_instantiate1Lift hv a j hb.2⟩
  | .lam ty b _, j, hb | .forallE ty b _, j, hb => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLPD_instantiate1Lift hv ty j hb.1.1,
      allLPD_instantiate1Lift hv b (j + 1) hb.1.2⟩, hb.2⟩
  | .letE ty val b _, j, hb => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLPD_instantiate1Lift hv ty j hb.1.1, allLPD_instantiate1Lift hv val j hb.1.2⟩,
      allLPD_instantiate1Lift hv b (j + 1) hb.2⟩
  | .proj _ _ e, j, hb => by
    simp only [Expr.allLevelParamsDefined] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined]
    exact allLPD_instantiate1Lift hv e j hb

/-- **An annotation takes its levels from the annotated term**: an annotation whose binder data
have their parameters among `lps`, of a term whose level parameters are among `lps`, has its
level parameters among `lps`. -/
private theorem annotates_allLPD_of_binderPW {lps : List LevelParam} {e' e₀ : KExpr}
    (hann : IxVM.Consistency.Annotates e' e₀) (hpw : binderPWDefined lps e' = true)
    (hdef : e₀.allLevelParamsDefined lps = true) :
    e'.allLevelParamsDefined lps = true := by
  induction hann with
  | bvar | sort | const | lit => exact hdef
  | fvar _ ih =>
    simp only [binderPWDefined] at hpw
    simp only [Expr.allLevelParamsDefined] at hdef ⊢
    exact ih hpw hdef
  | app _ _ ihf iha =>
    simp only [binderPWDefined, Bool.and_eq_true] at hpw
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef ⊢
    exact ⟨ihf hpw.1 hdef.1, iha hpw.2 hdef.2⟩
  | lam _ _ ihty ihb | forallE _ _ ihty ihb =>
    simp only [binderPWDefined, Bool.and_eq_true] at hpw
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef ⊢
    exact ⟨⟨ihty hpw.1.1 hdef.1.1, ihb hpw.1.2 hdef.1.2⟩, hpw.2⟩
  | proj _ ihe =>
    simp only [binderPWDefined] at hpw
    simp only [Expr.allLevelParamsDefined] at hdef ⊢
    exact ihe hpw hdef
  | letE _ ih =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    exact ih hpw (allLPD_instantiate1Lift hdef.1.2 _ 0 hdef.2)

/-! ## Recombination -/

/-- A term related by `WrapRelSem` to a term whose level parameters (binder data included) are
among `lps`, and which annotates a term whose level parameters are among `lps`, has its level
parameters among `lps`: its binder data are the related term's (`WrapRelSem` compares the
zero-ness data of binders exactly), its sorts and constants are the annotated term's. -/
theorem wrapRelSem_annot_allLevelParamsDefined
    {find? : KKey → Option (Ix.Kernel.ConstantInfo .anon)} {lps : List LevelParam}
    {g d e : KExpr}
    (hw : Decl.WrapRelSem find? g d) (hg : g.allLevelParamsDefined lps = true)
    (hann : IxVM.Consistency.Annotates d e) (he : e.allLevelParamsDefined lps = true) :
    d.allLevelParamsDefined lps = true :=
  annotates_allLPD_of_binderPW hann
    (wrapRelSem_binderPWDefined hw hg (annotates_letFreeDeep hann)) he

end IxVM.Refinement.Typing
