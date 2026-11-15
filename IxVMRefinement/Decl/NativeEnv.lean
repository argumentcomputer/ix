import IxVMRefinement.Decl.NativeCommon
import IxC.Kernel.Model.Inductives.StructRecKit2
import IxC.Kernel.Model.Inductives.StructEntryFree
import IxC.Kernel.Semantics.Inductives.DeclStructEta
import IxC.Kernel.Verify.Rename.Native1

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open Ix.Kernel (ConstantInfo ConstantVal RecRule Declaration Level LevelParam Expr EnvExt)
open Ix.Kernel.Rules (Annot Infer DefEq Red Certs DefEqList EtaProjCerts Grade)
open Ix.Kernel.Semantics (Judgements ConstantValRunJ ConstantValCheckJ
  FormerStoredJ SumIndRunJ FieldSortsJ StructDomsJ SumCtorRunJ SumCtorsRunJ FormerReadJ
  DeclNativeRunJ DeclNativeNoRecRunJ DeclRecTwinRunJ TwinRuleJ WrapRel WrapDom letFree)
open Ix.Kernel.Model (rulesJ)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

abbrev KConstantVal : Type := ConstantVal .anon
abbrev KConstantInfo : Type := ConstantInfo .anon

/-! ## `noProjAt`: absence of `.proj T _ _` nodes from full-grade `Rules.Infer` -/

/-- `true` iff `e` contains no `.proj T _ _` node (descending through `.fvar` annotations). -/
def noProjAt (T : KKey) : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar _ ty => noProjAt T ty
  | .app f a => noProjAt T f && noProjAt T a
  | .lam ty bo _ | .forallE ty bo _ => noProjAt T ty && noProjAt T bo
  | .letE ty v bo _ => noProjAt T ty && noProjAt T v && noProjAt T bo
  | .proj s _ e => !(s == T) && noProjAt T e

/-- Every `.fvar` annotation inside `e` satisfies `noProjAt T`. -/
def fvarNoProjAt (T : KKey) : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar _ ty => noProjAt T ty
  | .app f a => fvarNoProjAt T f && fvarNoProjAt T a
  | .lam ty bo _ | .forallE ty bo _ => fvarNoProjAt T ty && fvarNoProjAt T bo
  | .letE ty v bo _ => fvarNoProjAt T ty && fvarNoProjAt T v && fvarNoProjAt T bo
  | .proj _ _ e => fvarNoProjAt T e

theorem fvarNoProjAt_of_hasFvar_false {T : KKey} :
    ∀ {e : KExpr}, e.hasFvar = false → fvarNoProjAt T e = true := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _; rfl
  | fvar _ _ _ => intro h; simp [Expr.hasFvar] at h
  | app f a ihf iha =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [fvarNoProjAt, ihf h.1, iha h.2]
  | lam ty bo _ iht ihb | forallE ty bo _ iht ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [fvarNoProjAt, iht h.1, ihb h.2]
  | letE ty v bo _ iht ihv ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [fvarNoProjAt, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj _ _ e ihe => intro h; exact ihe h

theorem fvarNoProjAt_instantiate1 {T : KKey} {v : KExpr} (hv : fvarNoProjAt T v = true) :
    ∀ (e : KExpr) (k : Nat), fvarNoProjAt T e = true → fvarNoProjAt T (e.instantiate1 v k) = true
  | .bvar i, k, _ => by
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | .fvar _ _, _, h | .sort _, _, h | .const _ _, _, h | .lit _, _, h => h
  | .app f a, k, h => by
    simp only [fvarNoProjAt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarNoProjAt,
      fvarNoProjAt_instantiate1 hv f k h.1, fvarNoProjAt_instantiate1 hv a k h.2]
  | .lam ty bo _, k, h | .forallE ty bo _, k, h => by
    simp only [fvarNoProjAt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarNoProjAt,
      fvarNoProjAt_instantiate1 hv ty k h.1, fvarNoProjAt_instantiate1 hv bo (k + 1) h.2]
  | .letE ty val bo _, k, h => by
    simp only [fvarNoProjAt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarNoProjAt,
      fvarNoProjAt_instantiate1 hv ty k h.1.1,
      fvarNoProjAt_instantiate1 hv val k h.1.2,
      fvarNoProjAt_instantiate1 hv bo (k + 1) h.2]
  | .proj _ _ e, k, h => fvarNoProjAt_instantiate1 hv e k h

theorem noProjAt_of_instantiate1 {T : KKey} {v : KExpr} :
    ∀ {e : KExpr} (k : Nat), noProjAt T (e.instantiate1 v k) = true → noProjAt T e = true := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | fvar _ _ _ => intro _ h; exact h
  | app _ _ ihf iha =>
    intro k h
    simp only [Expr.instantiate1, noProjAt, Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro k h
    simp only [Expr.instantiate1, noProjAt, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE _ _ _ _ iht ihv ihb =>
    intro k h
    simp only [Expr.instantiate1, noProjAt, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj _ _ _ ihe =>
    intro k h
    simp only [Expr.instantiate1, noProjAt, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ihe k h.2⟩

private def nexprDepth : KExpr → Nat
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lit _ => 0
  | .app f a => 1 + max (nexprDepth f) (nexprDepth a)
  | .lam ty bo _ | .forallE ty bo _ => 1 + max (nexprDepth ty) (nexprDepth bo)
  | .letE ty v bo _ => 1 + max (max (nexprDepth ty) (nexprDepth v)) (nexprDepth bo)
  | .proj _ _ e => 1 + nexprDepth e

private theorem nexprDepth_instantiate1_fvar (d : Nat) (ty : KExpr) :
    ∀ (e : KExpr) (k : Nat), nexprDepth (e.instantiate1 (.fvar d ty) k) = nexprDepth e
  | .bvar _, _ => by
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, k => by
    simp [Expr.instantiate1, nexprDepth,
      nexprDepth_instantiate1_fvar d ty f k, nexprDepth_instantiate1_fvar d ty a k]
  | .lam t b _, k | .forallE t b _, k => by
    simp [Expr.instantiate1, nexprDepth,
      nexprDepth_instantiate1_fvar d ty t k, nexprDepth_instantiate1_fvar d ty b (k + 1)]
  | .letE t v b _, k => by
    simp [Expr.instantiate1, nexprDepth,
      nexprDepth_instantiate1_fvar d ty t k, nexprDepth_instantiate1_fvar d ty v k,
      nexprDepth_instantiate1_fvar d ty b (k + 1)]
  | .proj _ _ e, k => by
    simp [Expr.instantiate1, nexprDepth, nexprDepth_instantiate1_fvar d ty e k]

private theorem noProjAt_of_infer_aux {T : KKey} :
    ∀ (n : Nat) {env : Ix.Kernel.Env .anon} {g : Grade} {d : Nat} {e t : KExpr},
      nexprDepth e ≤ n →
      (∀ i, env.findProj? T i = none) →
      Infer env g d e t → g = .full → fvarNoProjAt T e = true →
      noProjAt T e = true
  | 0, _, _, _, _, _, hdep, _, hinf, hg, hfv => by
    cases hinf with
    | sort | const _ _ _ | natLit _ | strLit _ => rfl
    | fvar _ => exact hfv
    | forallE => simp only [nexprDepth] at hdep; omega
    | lam => simp only [nexprDepth] at hdep; omega
    | app => simp only [nexprDepth] at hdep; omega
    | appSkip => nomatch hg
    | proj => simp only [nexprDepth] at hdep; omega
  | n + 1, env, g, d, e, t, hdep, hno, hinf, hg, hfv => by
    cases hinf with
    | sort | const _ _ _ | natLit _ | strLit _ => rfl
    | fvar _ => exact hfv
    | forallE hty _ hbo _ _ =>
      simp only [nexprDepth] at hdep
      simp only [fvarNoProjAt, Bool.and_eq_true] at hfv
      have hty_np := noProjAt_of_infer_aux n (by omega) hno hty hg hfv.1
      have hbo_np := noProjAt_of_infer_aux n (by rw [nexprDepth_instantiate1_fvar]; omega)
        hno hbo hg (fvarNoProjAt_instantiate1 (v := .fvar _ _) hty_np _ 0 hfv.2)
      simp only [noProjAt, Bool.and_eq_true]
      exact ⟨hty_np, noProjAt_of_instantiate1 0 hbo_np⟩
    | lam hty _ hbo _ _ _ _ =>
      simp only [nexprDepth] at hdep
      simp only [fvarNoProjAt, Bool.and_eq_true] at hfv
      have hty_np := noProjAt_of_infer_aux n (by omega) hno (hty hg) rfl hfv.1
      have hbo_np := noProjAt_of_infer_aux n (by rw [nexprDepth_instantiate1_fvar]; omega)
        hno hbo hg (fvarNoProjAt_instantiate1 (v := .fvar _ _) hty_np _ 0 hfv.2)
      simp only [noProjAt, Bool.and_eq_true]
      exact ⟨hty_np, noProjAt_of_instantiate1 0 hbo_np⟩
    | app hfn _ harg _ =>
      simp only [nexprDepth] at hdep
      simp only [fvarNoProjAt, Bool.and_eq_true] at hfv
      simp only [noProjAt, Bool.and_eq_true]
      exact ⟨noProjAt_of_infer_aux n (by omega) hno hfn hg hfv.1,
        noProjAt_of_infer_aux n (by omega) hno harg hg hfv.2⟩
    | appSkip => nomatch hg
    | @proj _ _ sn i pe _ _ _ _ hpe _ _ hent _ _ _ =>
      simp only [nexprDepth] at hdep
      simp only [noProjAt, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
      refine ⟨?_, noProjAt_of_infer_aux n (by omega) hno hpe hg hfv⟩
      intro hsn
      subst hsn
      rw [hno i] at hent
      exact nomatch hent

/-- Full-grade `Rules.Infer` on an fvar-free expression in an environment with no projection
table for `T` guarantees `noProjAt T e = true`. -/
theorem noProjAt_of_infer_full {T : KKey} {env : Ix.Kernel.Env .anon} {d : Nat} {e t : KExpr}
    (hno : ∀ i, env.findProj? T i = none) (hinf : Infer env .full d e t)
    (hfv : e.hasFvar = false) :
    noProjAt T e = true :=
  noProjAt_of_infer_aux (nexprDepth e) (Nat.le_refl _) hno hinf rfl
    (fvarNoProjAt_of_hasFvar_false hfv)

theorem noProjAt_instantiateLevelParams (T : KKey) (ps : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr), noProjAt T (e.instantiateLevelParams ps us) = noProjAt T e
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ ty => noProjAt_instantiateLevelParams T ps us ty
  | .app f a => by
    simp [Expr.instantiateLevelParams, noProjAt,
      noProjAt_instantiateLevelParams T ps us f, noProjAt_instantiateLevelParams T ps us a]
  | .lam ty bo _ | .forallE ty bo _ => by
    simp [Expr.instantiateLevelParams, noProjAt,
      noProjAt_instantiateLevelParams T ps us ty, noProjAt_instantiateLevelParams T ps us bo]
  | .letE ty v bo _ => by
    simp [Expr.instantiateLevelParams, noProjAt,
      noProjAt_instantiateLevelParams T ps us ty,
      noProjAt_instantiateLevelParams T ps us v,
      noProjAt_instantiateLevelParams T ps us bo]
  | .proj s _ e => by
    simp [Expr.instantiateLevelParams, noProjAt, noProjAt_instantiateLevelParams T ps us e]

/-- Let-freeness descending through `.fvar` annotations. -/
def exprNoLet : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar _ ty => exprNoLet ty
  | .app f a => exprNoLet f && exprNoLet a
  | .lam ty bo _ | .forallE ty bo _ => exprNoLet ty && exprNoLet bo
  | .letE _ _ _ _ => false
  | .proj _ _ e => exprNoLet e

theorem exprNoLet_of_letFree {e : KExpr} (hlf : letFree e = true) (hfv : e.hasFvar = false) :
    exprNoLet e = true := by
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => rfl
  | fvar _ _ _ => simp [Expr.hasFvar] at hfv
  | app _ _ ihf iha =>
    simp only [letFree, Bool.and_eq_true] at hlf
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp [exprNoLet, ihf hlf.1 hfv.1, iha hlf.2 hfv.2]
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    simp only [letFree, Bool.and_eq_true] at hlf
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp [exprNoLet, iht hlf.1 hfv.1, ihb hlf.2 hfv.2]
  | letE _ _ _ _ => simp [letFree] at hlf
  | proj _ _ _ ihe => exact ihe hlf hfv

theorem noProjAt_of_annotates {T : KKey} {e' e : KExpr} (ha : IxVM.Consistency.Annotates e' e)
    (hnl : exprNoLet e = true) :
    noProjAt T e' = noProjAt T e := by
  induction ha with
  | bvar | sort | const | lit => rfl
  | fvar _ ih => simp only [exprNoLet] at hnl; simp [noProjAt, ih hnl]
  | app _ _ ihf iha =>
    simp only [exprNoLet, Bool.and_eq_true] at hnl
    simp [noProjAt, ihf hnl.1, iha hnl.2]
  | lam _ _ iht ihb =>
    simp only [exprNoLet, Bool.and_eq_true] at hnl
    simp [noProjAt, iht hnl.1, ihb hnl.2]
  | forallE _ _ iht ihb =>
    simp only [exprNoLet, Bool.and_eq_true] at hnl
    simp [noProjAt, iht hnl.1, ihb hnl.2]
  | proj _ ihe => simp only [exprNoLet] at hnl; simp [noProjAt, ihe hnl]
  | letE _ => simp [exprNoLet] at hnl

theorem noProjAt_stripPis {T : KKey} :
    ∀ {n : Nat} {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {body : KExpr},
      e.stripPis n = some (bs, body) → noProjAt T e = true →
      (∀ b ∈ bs, noProjAt T b.1 = true) ∧ noProjAt T body = true := by
  intro n
  induction n with
  | zero =>
    intro e bs body hst hnp
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact ⟨(fun _ hb => nomatch hb), hnp⟩
  | succ n ih =>
    intro e bs body hst hnp
    cases e with
    | forallE dom bo mb =>
      simp only [noProjAt, Bool.and_eq_true] at hnp
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
      obtain ⟨⟨bs', body'⟩, hst', heq⟩ := hst
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨hbs', hbo'⟩ := ih hst' hnp.2
      refine ⟨fun b hb => ?_, hbo'⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hnp.1
      · exact hbs' b hb
    | _ => simp [Expr.stripPis] at hst

theorem noProjAt_getApp {T : KKey} :
    ∀ {e : KExpr}, noProjAt T e = true →
      noProjAt T e.getAppFn = true ∧ ∀ a ∈ e.getAppArgs, noProjAt T a = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    simp only [noProjAt, Bool.and_eq_true] at h
    obtain ⟨hfn, hargs⟩ := ihf h.1
    refine ⟨hfn, fun x hx => ?_⟩
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hargs x hx
    · exact h.2
  | _ => intro h; exact ⟨h, fun _ hx => nomatch hx⟩

/-! ## `mentionsConst`, `litResolve`, `constsResolve`, and `Annotates` combinators -/

theorem mentionsConst_instantiateLevelParams (T : KKey) (ps : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr), (e.instantiateLevelParams ps us).mentionsConst T = e.mentionsConst T
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ ty => mentionsConst_instantiateLevelParams T ps us ty
  | .app f a => by
    simp [Expr.instantiateLevelParams, Expr.mentionsConst,
      mentionsConst_instantiateLevelParams T ps us f,
      mentionsConst_instantiateLevelParams T ps us a]
  | .lam ty bo _ | .forallE ty bo _ => by
    simp [Expr.instantiateLevelParams, Expr.mentionsConst,
      mentionsConst_instantiateLevelParams T ps us ty,
      mentionsConst_instantiateLevelParams T ps us bo]
  | .letE ty v bo _ => by
    simp [Expr.instantiateLevelParams, Expr.mentionsConst,
      mentionsConst_instantiateLevelParams T ps us ty,
      mentionsConst_instantiateLevelParams T ps us v,
      mentionsConst_instantiateLevelParams T ps us bo]
  | .proj _ _ e => by
    simp [Expr.instantiateLevelParams, Expr.mentionsConst,
      mentionsConst_instantiateLevelParams T ps us e]

theorem mentionsConst_of_annotates {T : KKey} {e' e : KExpr}
    (ha : IxVM.Consistency.Annotates e' e) (hnl : exprNoLet e = true) :
    e'.mentionsConst T = e.mentionsConst T := by
  induction ha with
  | bvar | sort | const | lit => rfl
  | fvar _ ih => simp only [exprNoLet] at hnl; simp [Expr.mentionsConst, ih hnl]
  | app _ _ ihf iha =>
    simp only [exprNoLet, Bool.and_eq_true] at hnl
    simp [Expr.mentionsConst, ihf hnl.1, iha hnl.2]
  | lam _ _ iht ihb =>
    simp only [exprNoLet, Bool.and_eq_true] at hnl
    simp [Expr.mentionsConst, iht hnl.1, ihb hnl.2]
  | forallE _ _ iht ihb =>
    simp only [exprNoLet, Bool.and_eq_true] at hnl
    simp [Expr.mentionsConst, iht hnl.1, ihb hnl.2]
  | proj _ ihe => simp only [exprNoLet] at hnl; simp [Expr.mentionsConst, ihe hnl]
  | letE _ => simp [exprNoLet] at hnl

theorem hasLooseBVar_of_annotates {e' e : KExpr} (ha : IxVM.Consistency.Annotates e' e)
    (hnl : exprNoLet e = true) :
    ∀ (k : Nat), e'.hasLooseBVar k = e.hasLooseBVar k := by
  induction ha with
  | bvar | sort | const | lit | fvar => intro _; rfl
  | app _ _ ihf iha =>
    simp only [exprNoLet, Bool.and_eq_true] at hnl
    intro k; simp [Expr.hasLooseBVar, ihf hnl.1 k, iha hnl.2 k]
  | lam _ _ iht ihb =>
    simp only [exprNoLet, Bool.and_eq_true] at hnl
    intro k; simp [Expr.hasLooseBVar, iht hnl.1 k, ihb hnl.2 (k + 1)]
  | forallE _ _ iht ihb =>
    simp only [exprNoLet, Bool.and_eq_true] at hnl
    intro k; simp [Expr.hasLooseBVar, iht hnl.1 k, ihb hnl.2 (k + 1)]
  | proj _ ihe =>
    simp only [exprNoLet] at hnl
    intro k; simp [Expr.hasLooseBVar, ihe hnl k]
  | letE _ => simp [exprNoLet] at hnl

theorem stripPis_of_annotates_right :
    ∀ {n : Nat} {e' e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {body : KExpr},
      IxVM.Consistency.Annotates e' e → exprNoLet e = true →
      e.stripPis n = some (bs, body) →
      ∃ bs' body',
        e'.stripPis n = some (bs', body') ∧
        List.Forall₂ (fun b' b => IxVM.Consistency.Annotates b'.1 b.1 ∧ exprNoLet b.1 = true) bs' bs ∧
        IxVM.Consistency.Annotates body' body ∧ exprNoLet body = true := by
  intro n
  induction n with
  | zero =>
    intro e' _ bs body ha hnl hst
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact ⟨[], e', rfl, .nil, ha, hnl⟩
  | succ n ih =>
    intro e' e bs body ha hnl hst
    cases ha with
    | @forallE ty' ty b' b m' m hdom hbo =>
      simp only [exprNoLet, Bool.and_eq_true] at hnl
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
      obtain ⟨⟨bs₁, body₁⟩, hst₁, heq⟩ := hst
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨bs', body', hst', hbs', hbo', hnl_bo⟩ := ih hbo hnl.2 hst₁
      exact ⟨(ty', m') :: bs', body', by simp [Expr.stripPis, hst'],
        .cons ⟨hdom, hnl.1⟩ hbs', hbo', hnl_bo⟩
    | letE _ => simp [exprNoLet] at hnl
    | _ => simp [Expr.stripPis] at hst

theorem stripPis_of_annotates_left :
    ∀ {n : Nat} {e' e : KExpr} {bs' : List (KExpr × Ix.Kernel.BinderMeta)} {body' : KExpr},
      IxVM.Consistency.Annotates e' e → exprNoLet e = true →
      e'.stripPis n = some (bs', body') →
      ∃ bs body,
        e.stripPis n = some (bs, body) ∧
        List.Forall₂ (fun b' b => IxVM.Consistency.Annotates b'.1 b.1 ∧ exprNoLet b.1 = true) bs' bs ∧
        IxVM.Consistency.Annotates body' body ∧ exprNoLet body = true := by
  intro n
  induction n with
  | zero =>
    intro _ e bs' body' ha hnl hst
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact ⟨[], e, rfl, .nil, ha, hnl⟩
  | succ n ih =>
    intro e' e bs' body' ha hnl hst
    cases ha with
    | @forallE ty' ty b' b m' m hdom hbo =>
      simp only [exprNoLet, Bool.and_eq_true] at hnl
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
      obtain ⟨⟨bs₁, body₁⟩, hst₁, heq⟩ := hst
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨bs, body, hst', hbs, hbo', hnl_bo⟩ := ih hbo hnl.2 hst₁
      exact ⟨(ty, m) :: bs, body, by simp [Expr.stripPis, hst'],
        .cons ⟨hdom, hnl.1⟩ hbs, hbo', hnl_bo⟩
    | letE _ => simp [exprNoLet] at hnl
    | _ => simp [Expr.stripPis] at hst

theorem structUsedLater_of_annotates {e' e : KExpr} (ha : IxVM.Consistency.Annotates e' e)
    (hnl : exprNoLet e = true) (nP j : Nat) :
    Ix.Kernel.structUsedLater e' nP j = Ix.Kernel.structUsedLater e nP j := by
  unfold Ix.Kernel.structUsedLater
  cases hst : e.stripPis (nP + j + 1) with
  | none =>
    cases hst' : e'.stripPis (nP + j + 1) with
    | none => rfl
    | some p' =>
      obtain ⟨bs, body, h, _, _⟩ := stripPis_of_annotates_left ha hnl hst'
      rw [hst] at h
      exact nomatch h
  | some p =>
    rcases p with ⟨bs, body⟩
    obtain ⟨bs', body', hst', _, hbo, hnl_bo⟩ := stripPis_of_annotates_right ha hnl hst
    rw [hst']
    simp only [Expr.hasLooseBVarB_eq]
    exact hasLooseBVar_of_annotates hbo hnl_bo 0

/-- Literal-constant resolution in `env` across all `.lit` subterms (descending into `.fvar`
annotations). -/
def litResolve (env : Ix.Kernel.Env .anon) : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ => true
  | .lit l => (Expr.lit (md := .anon) l).constsResolve env
  | .fvar _ ty => litResolve env ty
  | .app f a => litResolve env f && litResolve env a
  | .lam ty bo _ | .forallE ty bo _ => litResolve env ty && litResolve env bo
  | .letE ty v bo _ => litResolve env ty && litResolve env v && litResolve env bo
  | .proj _ _ e => litResolve env e

theorem litResolve_instantiate1 {env : Ix.Kernel.Env .anon} {v : KExpr}
    (hv : litResolve env v = true) :
    ∀ (e : KExpr) (k : Nat), litResolve env e = true →
      litResolve env (e.instantiate1 v k) = true
  | .bvar _, _, _ => by
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | .sort _, _, _ | .const _ _, _, _ => rfl
  | .lit _, _, h | .fvar _ _, _, h => h
  | .app f a, k, h => by
    simp only [litResolve, Bool.and_eq_true] at h
    simp [Expr.instantiate1, litResolve,
      litResolve_instantiate1 hv f k h.1, litResolve_instantiate1 hv a k h.2]
  | .lam ty bo _, k, h | .forallE ty bo _, k, h => by
    simp only [litResolve, Bool.and_eq_true] at h
    simp [Expr.instantiate1, litResolve,
      litResolve_instantiate1 hv ty k h.1, litResolve_instantiate1 hv bo (k + 1) h.2]
  | .letE ty val bo _, k, h => by
    simp only [litResolve, Bool.and_eq_true] at h
    simp [Expr.instantiate1, litResolve,
      litResolve_instantiate1 hv ty k h.1.1,
      litResolve_instantiate1 hv val k h.1.2,
      litResolve_instantiate1 hv bo (k + 1) h.2]
  | .proj _ _ e, k, h => litResolve_instantiate1 hv e k h

theorem litResolve_of_instantiate1 {env : Ix.Kernel.Env .anon} {v : KExpr} :
    ∀ {e : KExpr} (k : Nat), litResolve env (e.instantiate1 v k) = true → litResolve env e = true := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ => intro _ _; rfl
  | lit _ | fvar _ _ _ => intro _ h; exact h
  | app _ _ ihf iha =>
    intro k h
    simp only [Expr.instantiate1, litResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro k h
    simp only [Expr.instantiate1, litResolve, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE _ _ _ _ iht ihv ihb =>
    intro k h
    simp only [Expr.instantiate1, litResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj _ _ _ ihe =>
    intro k h
    simp only [Expr.instantiate1, litResolve] at h ⊢
    exact ihe k h

private def fvarLitResolve (env : Ix.Kernel.Env .anon) : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar _ ty => litResolve env ty
  | .app f a => fvarLitResolve env f && fvarLitResolve env a
  | .lam ty bo _ | .forallE ty bo _ => fvarLitResolve env ty && fvarLitResolve env bo
  | .letE ty v bo _ => fvarLitResolve env ty && fvarLitResolve env v && fvarLitResolve env bo
  | .proj _ _ e => fvarLitResolve env e

private theorem fvarLitResolve_of_hasFvar_false {env : Ix.Kernel.Env .anon} :
    ∀ {e : KExpr}, e.hasFvar = false → fvarLitResolve env e = true := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _; rfl
  | fvar _ _ _ => intro h; simp [Expr.hasFvar] at h
  | app _ _ ihf iha =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [fvarLitResolve, ihf h.1, iha h.2]
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [fvarLitResolve, iht h.1, ihb h.2]
  | letE _ _ _ _ iht ihv ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [fvarLitResolve, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj _ _ _ ihe => intro h; exact ihe h

private theorem fvarLitResolve_instantiate1 {env : Ix.Kernel.Env .anon} {v : KExpr}
    (hv : fvarLitResolve env v = true) :
    ∀ (e : KExpr) (k : Nat), fvarLitResolve env e = true →
      fvarLitResolve env (e.instantiate1 v k) = true
  | .bvar i, k, _ => by
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .fvar _ _, _, h => h
  | .app f a, k, h => by
    simp only [fvarLitResolve, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarLitResolve,
      fvarLitResolve_instantiate1 hv f k h.1, fvarLitResolve_instantiate1 hv a k h.2]
  | .lam ty bo _, k, h | .forallE ty bo _, k, h => by
    simp only [fvarLitResolve, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarLitResolve,
      fvarLitResolve_instantiate1 hv ty k h.1, fvarLitResolve_instantiate1 hv bo (k + 1) h.2]
  | .letE ty val bo _, k, h => by
    simp only [fvarLitResolve, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarLitResolve,
      fvarLitResolve_instantiate1 hv ty k h.1.1,
      fvarLitResolve_instantiate1 hv val k h.1.2,
      fvarLitResolve_instantiate1 hv bo (k + 1) h.2]
  | .proj _ _ e, k, h => fvarLitResolve_instantiate1 hv e k h

private theorem stripPis_not_sort_of_const_cod {A : KExpr} {c : KKey} {us : List KLevel}
    {mb : Ix.Kernel.BinderMeta} :
    ∀ (m : Nat) (bs : List (KExpr × Ix.Kernel.BinderMeta)) (u : KLevel),
      (Expr.forallE A (.const c us) mb).stripPis m ≠ some (bs, .sort u)
  | 0, _, _, h => by simp [Expr.stripPis] at h
  | 1, _, _, h => by simp [Expr.stripPis] at h
  | _ + 2, _, _, h => by simp [Expr.stripPis] at h

private theorem stripPis_not_sort_of_app_cod1 {A f a : KExpr} {mb : Ix.Kernel.BinderMeta} :
    ∀ (m : Nat) (bs : List (KExpr × Ix.Kernel.BinderMeta)) (u : KLevel),
      (Expr.forallE A (.app f a) mb).stripPis m ≠ some (bs, .sort u)
  | 0, _, _, h => by simp [Expr.stripPis] at h
  | 1, _, _, h => by simp [Expr.stripPis] at h
  | _ + 2, _, _, h => by simp [Expr.stripPis] at h

private theorem stripPis_not_sort_of_app_cod3 {A B C f a : KExpr}
    {mb1 mb2 mb3 : Ix.Kernel.BinderMeta} :
    ∀ (m : Nat) (bs : List (KExpr × Ix.Kernel.BinderMeta)) (u : KLevel),
      (Expr.forallE A (.forallE B (.forallE C (.app f a) mb3) mb2) mb1).stripPis m ≠
        some (bs, .sort u)
  | 0, _, _, h => by simp [Expr.stripPis] at h
  | 1, _, _, h => by simp [Expr.stripPis] at h
  | 2, _, _, h => by simp [Expr.stripPis] at h
  | 3, _, _, h => by simp [Expr.stripPis] at h
  | _ + 4, _, _, h => by simp [Expr.stripPis] at h

private theorem lit_constsResolve_of_cons_former {env : Ix.Kernel.Env .anon} {ci : KConstantInfo}
    (hstore : Ix.Kernel.Open.StoreInv env)
    (hbasis : Ix.Kernel.reservedBasisNames.contains ci.name = false)
    (hsort : ∃ m bs u, ci.toConstantVal.type.stripPis m = some (bs, .sort u)) :
    (∀ n, Ix.Kernel.natLitSupported ⟨ci :: env.consts⟩ = true →
      (Expr.lit (md := .anon) (.natVal n)).constsResolve env = true) ∧
    (∀ s, Ix.Kernel.strLitSupported ⟨ci :: env.consts⟩ = true →
      (Expr.lit (md := .anon) (.strVal s)).constsResolve env = true) := by
  have hnot_basis : ∀ k : KKey, Ix.Kernel.reservedBasisNames.contains k = true →
      (⟨ci :: env.consts⟩ : Ix.Kernel.Env .anon).find? k = env.find? k := by
    intro k hk
    have hne : (ci.name == k) = false := by
      rw [beq_eq_false_iff_ne]
      intro heq; subst heq; rw [hbasis] at hk; exact nomatch hk
    simp [Ix.Kernel.Env.find?, List.find?, hne]
  have hnat_imp : Ix.Kernel.natLitSupported ⟨ci :: env.consts⟩ = true →
      ((env.find? Ix.Kernel.natName).isSome &&
       (env.find? Ix.Kernel.natZeroName).isSome &&
       (env.find? Ix.Kernel.natSuccName).isSome) = true := by
    intro hnat
    have hn1 : (⟨ci :: env.consts⟩ : Ix.Kernel.Env .anon).find? Ix.Kernel.natName =
        env.find? Ix.Kernel.natName :=
      hnot_basis Ix.Kernel.natName (by simp [Ix.Kernel.reservedBasisNames])
    have hn2 : (⟨ci :: env.consts⟩ : Ix.Kernel.Env .anon).find? Ix.Kernel.natZeroName =
        env.find? Ix.Kernel.natZeroName :=
      hnot_basis Ix.Kernel.natZeroName (by simp [Ix.Kernel.reservedBasisNames])
    have hn3 : (⟨ci :: env.consts⟩ : Ix.Kernel.Env .anon).find? Ix.Kernel.natSuccName =
        env.find? Ix.Kernel.natSuccName :=
      hnot_basis Ix.Kernel.natSuccName (by simp [Ix.Kernel.reservedBasisNames])
    simp only [Ix.Kernel.natLitSupported, hn1, hn2, hn3, Bool.and_eq_true] at hnat
    obtain ⟨⟨h1, h2⟩, h3⟩ := hnat
    have s1 : (env.find? Ix.Kernel.natName).isSome = true := by
      cases hf : env.find? Ix.Kernel.natName <;> simp_all [Ix.Kernel.natIndOk]
    have s2 : (env.find? Ix.Kernel.natZeroName).isSome = true := by
      cases hf : env.find? Ix.Kernel.natZeroName <;> simp_all [Ix.Kernel.natZeroOk]
    have s3 : (env.find? Ix.Kernel.natSuccName).isSome = true := by
      cases hf : env.find? Ix.Kernel.natSuccName <;> simp_all [Ix.Kernel.natSuccOk]
    simp [s1, s2, s3]
  refine ⟨fun n hnat => hnat_imp hnat, fun s hstr => ?_⟩
  obtain ⟨m, bs, u, hst⟩ := hsort
  simp only [Ix.Kernel.strLitSupported, Bool.and_eq_true] at hstr
  obtain ⟨⟨⟨⟨⟨⟨⟨hnat, _⟩, hsl⟩, _⟩, hln⟩, hlc⟩, _⟩, hcn⟩ := hstr
  have hnat' := hnat_imp hnat
  simp only [Bool.and_eq_true] at hnat'
  -- `stringOfListName` cannot be `ci.name`
  have hne_sl : (ci.name == Ix.Kernel.stringOfListName) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have hf : (⟨ci :: env.consts⟩ : Ix.Kernel.Env .anon).find? Ix.Kernel.stringOfListName =
        some ci := by simp [Ix.Kernel.Env.find?, List.find?, heq]
    rw [hf] at hsl
    simp only [Ix.Kernel.stringOfListTyOk, Bool.and_eq_true] at hsl
    split at hsl
    · rename_i l1 us1 c1 c2 mb hty
      rw [hty] at hst
      exact stripPis_not_sort_of_const_cod m bs u hst
    · exact nomatch hsl.2
  have hne_ln : (ci.name == Ix.Kernel.listNilName) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have hf : (⟨ci :: env.consts⟩ : Ix.Kernel.Env .anon).find? Ix.Kernel.listNilName =
        some ci := by simp [Ix.Kernel.Env.find?, List.find?, heq]
    rw [hf] at hln
    simp only [Ix.Kernel.listNilTyOk] at hln
    split at hln
    · split at hln
      · rename_i u1 l1 us1 mb hty
        rw [hty] at hst
        exact stripPis_not_sort_of_app_cod1 m bs u hst
      · exact nomatch hln
    · exact nomatch hln
  have hne_lc : (ci.name == Ix.Kernel.listConsName) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have hf : (⟨ci :: env.consts⟩ : Ix.Kernel.Env .anon).find? Ix.Kernel.listConsName =
        some ci := by simp [Ix.Kernel.Env.find?, List.find?, heq]
    rw [hf] at hlc
    simp only [Ix.Kernel.listConsTyOk] at hlc
    split at hlc
    · split at hlc
      · rename_i u1 l1 us1 l2 us2 mb3 mb2 mb1 hty
        rw [hty] at hst
        exact stripPis_not_sort_of_app_cod3 m bs u hst
      · exact nomatch hlc
    · exact nomatch hlc
  have hne_cn : (ci.name == Ix.Kernel.charOfNatName) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have hf : (⟨ci :: env.consts⟩ : Ix.Kernel.Env .anon).find? Ix.Kernel.charOfNatName =
        some ci := by simp [Ix.Kernel.Env.find?, List.find?, heq]
    rw [hf] at hcn
    simp only [Ix.Kernel.charOfNatTyOk, Bool.and_eq_true] at hcn
    split at hcn
    · rename_i c1 c2 mb hty
      rw [hty] at hst
      exact stripPis_not_sort_of_const_cod m bs u hst
    · exact nomatch hcn.2
  have hf_sl : (⟨ci :: env.consts⟩ : Ix.Kernel.Env .anon).find? Ix.Kernel.stringOfListName =
      env.find? Ix.Kernel.stringOfListName := by simp [Ix.Kernel.Env.find?, List.find?, hne_sl]
  have hf_ln : (⟨ci :: env.consts⟩ : Ix.Kernel.Env .anon).find? Ix.Kernel.listNilName =
      env.find? Ix.Kernel.listNilName := by simp [Ix.Kernel.Env.find?, List.find?, hne_ln]
  have hf_lc : (⟨ci :: env.consts⟩ : Ix.Kernel.Env .anon).find? Ix.Kernel.listConsName =
      env.find? Ix.Kernel.listConsName := by simp [Ix.Kernel.Env.find?, List.find?, hne_lc]
  have hf_cn : (⟨ci :: env.consts⟩ : Ix.Kernel.Env .anon).find? Ix.Kernel.charOfNatName =
      env.find? Ix.Kernel.charOfNatName := by simp [Ix.Kernel.Env.find?, List.find?, hne_cn]
  rw [hf_sl] at hsl; rw [hf_ln] at hln; rw [hf_lc] at hlc; rw [hf_cn] at hcn
  have isSome_ln : (env.find? Ix.Kernel.listNilName).isSome = true := by
    cases hf : env.find? Ix.Kernel.listNilName <;> simp_all [Ix.Kernel.listNilTyOk]
  have isSome_lc : (env.find? Ix.Kernel.listConsName).isSome = true := by
    cases hf : env.find? Ix.Kernel.listConsName <;> simp_all [Ix.Kernel.listConsTyOk]
  have isSome_cn : (env.find? Ix.Kernel.charOfNatName).isSome = true := by
    cases hf : env.find? Ix.Kernel.charOfNatName <;> simp_all [Ix.Kernel.charOfNatTyOk]
  cases hfind_sl : env.find? Ix.Kernel.stringOfListName with
  | none => simp [hfind_sl, Ix.Kernel.stringOfListTyOk] at hsl
  | some ci_sl =>
    have isSome_sl : (env.find? Ix.Kernel.stringOfListName).isSome = true := by simp [hfind_sl]
    have hmem_sl : ci_sl ∈ env.consts := List.mem_of_find?_eq_some hfind_sl
    have hres_sl : ci_sl.toConstantVal.type.constsResolve env = true :=
      (hstore.wf ci_sl hmem_sl).2.2.1
    rw [hfind_sl] at hsl
    simp only [Ix.Kernel.stringOfListTyOk, Bool.and_eq_true] at hsl
    split at hsl
    · rename_i l1 us1 c1 c2 mb hty
      simp only [Bool.and_eq_true, beq_iff_eq] at hsl
      obtain ⟨⟨⟨rfl, _⟩, rfl⟩, rfl⟩ := hsl.2
      rw [hty] at hres_sl
      simp only [Expr.constsResolve, Bool.and_eq_true] at hres_sl
      simp [Expr.constsResolve, hnat'.1.1, hnat'.1.2, hnat'.2,
        hres_sl.2, isSome_sl, hres_sl.1.1, isSome_ln, isSome_lc, hres_sl.1.2, isSome_cn]
    · exact nomatch hsl.2

private theorem litResolve_of_infer_aux {env env₁ : Ix.Kernel.Env .anon} {ci : KConstantInfo}
    (henv₁ : env₁ = ⟨ci :: env.consts⟩)
    (hlit_nat : ∀ n, Ix.Kernel.natLitSupported env₁ = true →
      (Expr.lit (md := .anon) (.natVal n)).constsResolve env = true)
    (hlit_str : ∀ s, Ix.Kernel.strLitSupported env₁ = true →
      (Expr.lit (md := .anon) (.strVal s)).constsResolve env = true) :
    ∀ (n : Nat) {g : Grade} {d : Nat} {e t : KExpr},
      nexprDepth e ≤ n → Infer env₁ g d e t → g = .full →
      fvarLitResolve env e = true → litResolve env e = true
  | 0, _, _, _, _, hdep, hinf, hg, hfv => by
    cases hinf with
    | sort | const _ _ _ => rfl
    | fvar _ => exact hfv
    | @natLit _ _ n hn => exact hlit_nat n hn
    | @strLit _ _ s hs => exact hlit_str s hs
    | forallE => simp only [nexprDepth] at hdep; omega
    | lam => simp only [nexprDepth] at hdep; omega
    | app => simp only [nexprDepth] at hdep; omega
    | appSkip => nomatch hg
    | proj => simp only [nexprDepth] at hdep; omega
  | n + 1, g, d, e, t, hdep, hinf, hg, hfv => by
    cases hinf with
    | sort | const _ _ _ => rfl
    | fvar _ => exact hfv
    | @natLit _ _ k hn => exact hlit_nat k hn
    | @strLit _ _ s hs => exact hlit_str s hs
    | forallE hty _ hbo _ _ =>
      simp only [nexprDepth] at hdep
      simp only [fvarLitResolve, Bool.and_eq_true] at hfv
      have hty_lr := litResolve_of_infer_aux henv₁ hlit_nat hlit_str n (by omega) hty hg hfv.1
      have hbo_lr := litResolve_of_infer_aux henv₁ hlit_nat hlit_str n
        (by rw [nexprDepth_instantiate1_fvar]; omega) hbo hg
        (fvarLitResolve_instantiate1 (v := .fvar _ _) hty_lr _ 0 hfv.2)
      simp only [litResolve, Bool.and_eq_true]
      exact ⟨hty_lr, litResolve_of_instantiate1 0 hbo_lr⟩
    | lam hty _ hbo _ _ _ _ =>
      simp only [nexprDepth] at hdep
      simp only [fvarLitResolve, Bool.and_eq_true] at hfv
      have hty_lr := litResolve_of_infer_aux henv₁ hlit_nat hlit_str n (by omega) (hty hg) rfl hfv.1
      have hbo_lr := litResolve_of_infer_aux henv₁ hlit_nat hlit_str n
        (by rw [nexprDepth_instantiate1_fvar]; omega) hbo hg
        (fvarLitResolve_instantiate1 (v := .fvar _ _) hty_lr _ 0 hfv.2)
      simp only [litResolve, Bool.and_eq_true]
      exact ⟨hty_lr, litResolve_of_instantiate1 0 hbo_lr⟩
    | app hfn _ harg _ =>
      simp only [nexprDepth] at hdep
      simp only [fvarLitResolve, Bool.and_eq_true] at hfv
      simp only [litResolve, Bool.and_eq_true]
      exact ⟨litResolve_of_infer_aux henv₁ hlit_nat hlit_str n (by omega) hfn hg hfv.1,
        litResolve_of_infer_aux henv₁ hlit_nat hlit_str n (by omega) harg hg hfv.2⟩
    | appSkip => nomatch hg
    | @proj _ _ sn i pe _ _ _ _ hpe _ _ _ _ _ _ =>
      simp only [nexprDepth] at hdep
      exact litResolve_of_infer_aux henv₁ hlit_nat hlit_str n (e := pe) (by omega) hpe hg hfv

/-- Full-grade `Rules.Infer` in `⟨ci :: env.consts⟩` (where `ci` is an unpinned telescope former)
establishes `litResolve env e = true` on any fvar-free expression `e`. -/
theorem litResolve_of_infer_cons_former {env env₁ : Ix.Kernel.Env .anon} {ci : KConstantInfo}
    {d : Nat} {e t : KExpr}
    (hstore : Ix.Kernel.Open.StoreInv env)
    (henv₁ : env₁ = ⟨ci :: env.consts⟩)
    (hbasis : Ix.Kernel.reservedBasisNames.contains ci.name = false)
    (hsort : ∃ m bs u, ci.toConstantVal.type.stripPis m = some (bs, .sort u))
    (hinf : Infer env₁ .full d e t)
    (hfv : e.hasFvar = false) :
    litResolve env e = true := by
  obtain ⟨hnat, hstr⟩ := lit_constsResolve_of_cons_former hstore hbasis hsort
  exact litResolve_of_infer_aux henv₁
    (fun n hn => hnat n (by rwa [← henv₁]))
    (fun s hs => hstr s (by rwa [← henv₁]))
    (nexprDepth e) (Nat.le_refl _) hinf rfl (fvarLitResolve_of_hasFvar_false hfv)

/-- If `e` does not mention `ci.name` and its literals resolve in `env`, resolution in
`⟨ci :: env.consts⟩` descends to `env`. -/
theorem constsResolve_of_cons_not_mentionsConst {env : Ix.Kernel.Env .anon}
    {ci : KConstantInfo} :
    ∀ {e : KExpr}, litResolve env e = true → e.mentionsConst ci.name = false →
      e.constsResolve ⟨ci :: env.consts⟩ = true → e.constsResolve env = true := by
  intro e
  induction e with
  | bvar _ | sort _ => intro _ _ _; rfl
  | lit _ => intro hlit _ _; exact hlit
  | const n _ =>
    intro _ hm hres
    simp only [Expr.mentionsConst, beq_eq_false_iff_ne] at hm
    have hne : (ci.name == n) = false := beq_eq_false_iff_ne.mpr (Ne.symm hm)
    simpa [Expr.constsResolve, Ix.Kernel.Env.find?, List.find?, hne] using hres
  | fvar _ _ ih => intro hlit hm hres; exact ih hlit hm hres
  | app _ _ ihf iha =>
    intro hlit hm hres
    simp only [litResolve, Expr.constsResolve, Bool.and_eq_true] at hlit hres ⊢
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm
    exact ⟨ihf hlit.1 hm.1 hres.1, iha hlit.2 hm.2 hres.2⟩
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro hlit hm hres
    simp only [litResolve, Expr.constsResolve, Bool.and_eq_true] at hlit hres ⊢
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm
    exact ⟨iht hlit.1 hm.1 hres.1, ihb hlit.2 hm.2 hres.2⟩
  | letE _ _ _ _ iht ihv ihb =>
    intro hlit hm hres
    simp only [litResolve, Expr.constsResolve, Bool.and_eq_true] at hlit hres ⊢
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm
    exact ⟨⟨iht hlit.1.1 hm.1.1 hres.1.1, ihv hlit.1.2 hm.1.2 hres.1.2⟩,
      ihb hlit.2 hm.2 hres.2⟩
  | proj s _ _ ihe =>
    intro hlit hm hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres ⊢
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hm
    have hne : (ci.name == s) = false := beq_eq_false_iff_ne.mpr (Ne.symm hm.1)
    refine ⟨?_, ihe hlit hm.2 hres.2⟩
    simpa [Ix.Kernel.Env.find?, List.find?, hne] using hres.1

theorem mentionsConst_getApp {T : KKey} :
    ∀ {e : KExpr}, e.mentionsConst T = false →
      e.getAppFn.mentionsConst T = false ∧ ∀ a ∈ e.getAppArgs, a.mentionsConst T = false := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h
    obtain ⟨hfn, hargs⟩ := ihf h.1
    refine ⟨hfn, fun x hx => ?_⟩
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hargs x hx
    · exact h.2
  | _ => intro h; exact ⟨h, fun _ hx => nomatch hx⟩

theorem constsResolve_getApp {env : Ix.Kernel.Env .anon} :
    ∀ {e : KExpr}, e.constsResolve env = true →
      e.getAppFn.constsResolve env = true ∧ ∀ a ∈ e.getAppArgs, a.constsResolve env = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    obtain ⟨hfn, hargs⟩ := ihf h.1
    refine ⟨hfn, fun x hx => ?_⟩
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hargs x hx
    · exact h.2
  | _ => intro h; exact ⟨h, fun _ hx => nomatch hx⟩

theorem litResolve_getApp {env : Ix.Kernel.Env .anon} :
    ∀ {e : KExpr}, litResolve env e = true →
      litResolve env e.getAppFn = true ∧ ∀ a ∈ e.getAppArgs, litResolve env a = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    simp only [litResolve, Bool.and_eq_true] at h
    obtain ⟨hfn, hargs⟩ := ihf h.1
    refine ⟨hfn, fun x hx => ?_⟩
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hargs x hx
    · exact h.2
  | _ => intro h; exact ⟨h, fun _ hx => nomatch hx⟩

theorem openPisAtFvars_constsResolve {env : Ix.Kernel.Env .anon} :
    ∀ (n : Nat) {e : KExpr} {d : Nat} {fvs : List KExpr} {o : KExpr},
      e.constsResolve env = true →
      Ix.Kernel.openPisAtFvars n e d = some (fvs, o) →
      (∀ x ∈ fvs, x.fvarTypeD.constsResolve env = true) ∧ o.constsResolve env = true := by
  intro n
  induction n with
  | zero =>
    intro e _ fvs o he hop
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨(fun _ hx => nomatch hx), he⟩
  | succ n ih =>
    intro e d fvs o he hop
    cases e with
    | forallE dom bo mb =>
      simp only [Expr.constsResolve, Bool.and_eq_true] at he
      simp only [Ix.Kernel.openPisAtFvars] at hop
      split at hop
      · next fvs₁ o₁ hop₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have hbo : (bo.instantiate1 (.fvar d dom)).constsResolve env = true :=
          Expr.constsResolve_instantiate1 he.1 0 he.2
        obtain ⟨hfvs₁, ho₁⟩ := ih hbo hop₁
        refine ⟨fun x hx => ?_, ho₁⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact he.1
        · exact hfvs₁ x hx
      · exact nomatch hop
    | _ => simp [Ix.Kernel.openPisAtFvars] at hop

theorem openPisAtFvars_litResolve {env : Ix.Kernel.Env .anon} :
    ∀ (n : Nat) {e : KExpr} {d : Nat} {fvs : List KExpr} {o : KExpr},
      litResolve env e = true →
      Ix.Kernel.openPisAtFvars n e d = some (fvs, o) →
      (∀ x ∈ fvs, litResolve env x.fvarTypeD = true) ∧ litResolve env o = true := by
  intro n
  induction n with
  | zero =>
    intro e _ fvs o he hop
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨(fun _ hx => nomatch hx), he⟩
  | succ n ih =>
    intro e d fvs o he hop
    cases e with
    | forallE dom bo mb =>
      simp only [litResolve, Bool.and_eq_true] at he
      simp only [Ix.Kernel.openPisAtFvars] at hop
      split at hop
      · next fvs₁ o₁ hop₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have hbo : litResolve env (bo.instantiate1 (.fvar d dom)) = true :=
          litResolve_instantiate1 (v := .fvar d dom) he.1 bo 0 he.2
        obtain ⟨hfvs₁, ho₁⟩ := ih hbo hop₁
        refine ⟨fun x hx => ?_, ho₁⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact he.1
        · exact hfvs₁ x hx
      · exact nomatch hop
    | _ => simp [Ix.Kernel.openPisAtFvars] at hop

theorem mentionsConst_instantiate1_of_false {T : KKey} {v : KExpr} (hv : v.mentionsConst T = false) :
    ∀ (e : KExpr) (k : Nat), (e.instantiate1 v k).mentionsConst T = e.mentionsConst T
  | .bvar i, k => by
    simp only [Expr.instantiate1, Expr.mentionsConst]
    split
    · exact hv
    · split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, k => by
    simp [Expr.instantiate1, Expr.mentionsConst,
      mentionsConst_instantiate1_of_false hv f k,
      mentionsConst_instantiate1_of_false hv a k]
  | .lam ty bo _, k | .forallE ty bo _, k => by
    simp [Expr.instantiate1, Expr.mentionsConst,
      mentionsConst_instantiate1_of_false hv ty k,
      mentionsConst_instantiate1_of_false hv bo (k + 1)]
  | .letE ty val bo _, k => by
    simp [Expr.instantiate1, Expr.mentionsConst,
      mentionsConst_instantiate1_of_false hv ty k,
      mentionsConst_instantiate1_of_false hv val k,
      mentionsConst_instantiate1_of_false hv bo (k + 1)]
  | .proj _ _ e, k => by
    simp [Expr.instantiate1, Expr.mentionsConst,
      mentionsConst_instantiate1_of_false hv e k]

theorem mentionsConst_instantiate1_of_not_hasLooseBVar {T : KKey} {v : KExpr} :
    ∀ (e : KExpr) (k : Nat), e.hasLooseBVar k = false →
      (e.instantiate1 v k).mentionsConst T = e.mentionsConst T
  | .bvar i, k, hk => by
    simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne] at hk
    simp only [Expr.instantiate1]
    split
    · next heq => exact absurd heq.symm hk
    · split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, k, hk => by
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hk
    simp [Expr.instantiate1, Expr.mentionsConst,
      mentionsConst_instantiate1_of_not_hasLooseBVar f k hk.1,
      mentionsConst_instantiate1_of_not_hasLooseBVar a k hk.2]
  | .lam ty bo _, k, hk | .forallE ty bo _, k, hk => by
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hk
    simp [Expr.instantiate1, Expr.mentionsConst,
      mentionsConst_instantiate1_of_not_hasLooseBVar ty k hk.1,
      mentionsConst_instantiate1_of_not_hasLooseBVar bo (k + 1) hk.2]
  | .letE ty val bo _, k, hk => by
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hk
    simp [Expr.instantiate1, Expr.mentionsConst,
      mentionsConst_instantiate1_of_not_hasLooseBVar ty k hk.1.1,
      mentionsConst_instantiate1_of_not_hasLooseBVar val k hk.1.2,
      mentionsConst_instantiate1_of_not_hasLooseBVar bo (k + 1) hk.2]
  | .proj _ _ e, k, hk => by
    simp only [Expr.hasLooseBVar] at hk
    simp [Expr.instantiate1, Expr.mentionsConst,
      mentionsConst_instantiate1_of_not_hasLooseBVar e k hk]

/-! ## Stage judgement upgrades along `CapsUpgradeAt` -/

namespace CapsUpgradeAt

variable {T : KKey} {cvS : KConstantVal} {caps : Ix.Kernel.IndCaps .anon}
  {envₐ envᵦ : Ix.Kernel.Env .anon}

theorem find_isSome_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (k : KKey) :
    (envᵦ.find? k).isSome = (envₐ.find? k).isSome := by
  by_cases hk : k = T
  · subst hk; rw [h.find_self_b, h.find_self_a]; rfl
  · rw [h.find_ne hk]

theorem find_isNone_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (k : KKey) :
    (envᵦ.find? k).isNone = (envₐ.find? k).isNone := by
  by_cases hk : k = T
  · subst hk; rw [h.find_self_b, h.find_self_a]; rfl
  · rw [h.find_ne hk]

theorem constsResolve_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (e : KExpr) :
    e.constsResolve envᵦ = e.constsResolve envₐ :=
  Expr.constsResolve_congr h.find_isSome_eq e

theorem constantValCheckJ (h : CapsUpgradeAt T cvS caps envₐ envᵦ)
    {cv cv' : KConstantVal} (hc : ConstantValCheckJ rulesJ envₐ cv cv') :
    ConstantValCheckJ rulesJ envᵦ cv cv' := by
  obtain ⟨ty', ⟨hfresh, hbasis, hshape, hnd, hlbd, hfv, hann, hlpd, hcr,
    ⟨sty, u, hinf, hred⟩⟩, hcv⟩ := hc
  refine ⟨ty', ⟨?_, hbasis, hshape, hnd, hlbd, hfv, hann, hlpd, ?_,
    ⟨sty, u, h.upgradeInfer hinf, h.upgradeRed hred⟩⟩, hcv⟩
  · rwa [h.find_isNone_eq]
  · rwa [h.constsResolve_eq]

theorem structDomsJ (h : CapsUpgradeAt T cvS caps envₐ envᵦ)
    {off : Nat} {fvs doms : List KExpr} {n : Nat}
    (hd : StructDomsJ rulesJ envₐ off fvs doms n) :
    StructDomsJ rulesJ envᵦ off fvs doms n := by
  intro i hi
  obtain ⟨a, b, ha, hb, hde⟩ := hd i hi
  exact ⟨a, b, ha, hb, h.upgradeDefEq hde⟩

theorem fieldSortsJ (h : CapsUpgradeAt T cvS caps envₐ envᵦ)
    {isProp large : Bool} {s : KLevel} {nP : Nat} {fvs idxArgs : List KExpr}
    {n : Nat} {sorts : List KLevel}
    (hs : FieldSortsJ rulesJ envₐ isProp large s nP fvs idxArgs n sorts) :
    FieldSortsJ rulesJ envᵦ isProp large s nP fvs idxArgs n sorts := by
  refine ⟨hs.1, fun i hi => ?_⟩
  obtain ⟨fv, ty, u, hfv, hu, hinf, hred, hle, hpr⟩ := hs.2 i hi
  exact ⟨fv, ty, u, hfv, hu, h.upgradeInfer hinf, h.upgradeRed hred, hle, hpr⟩

theorem sumCtorRunJ (h : CapsUpgradeAt T cvS caps envₐ envᵦ)
    {T' : KKey} {lps : List LevelParam} {nP nIdx : Nat} {resSort : KLevel}
    {isProp large : Bool} {cvC : KConstantVal} {nF : Nat} {cvTa cvCa : KConstantVal}
    {sorts : List KLevel}
    (hc : SumCtorRunJ rulesJ envₐ envₐ T' lps nP nIdx resSort isProp large cvC nF cvTa cvCa sorts) :
    SumCtorRunJ rulesJ envᵦ envᵦ T' lps nP nIdx resSort isProp large cvC nF cvTa cvCa sorts := by
  obtain ⟨⟨cvCa₀, hc₀, halt⟩, hres_sh, fvsP, crest, tfvs, trest, xFvs, idxArgs,
    hopP, hopT, hdoms, hopF, hilen, hxres, hires, hfsorts⟩ := hc
  refine ⟨⟨cvCa₀, h.constantValCheckJ hc₀, ?_⟩, hres_sh,
    fvsP, crest, tfvs, trest, xFvs, idxArgs,
    hopP, hopT, h.structDomsJ hdoms, hopF, hilen, ?_, ?_, h.fieldSortsJ hfsorts⟩
  · rcases halt with rfl | ⟨ty', hc'⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨ty', h.constantValCheckJ hc'⟩
  · intro x hx; rw [h.constsResolve_eq]; exact hxres x hx
  · intro e he; rw [h.constsResolve_eq]; exact hires e he

theorem sumCtorsRunJ (h : CapsUpgradeAt T cvS caps envₐ envᵦ)
    {T' : KKey} {lps : List LevelParam} {nP nIdx : Nat} {resSort : KLevel}
    {isProp large : Bool} {cvTa : KConstantVal} {cs ctorsA : List (KConstantVal × Nat)}
    {sortss : List (List KLevel)}
    (hcs : SumCtorsRunJ rulesJ envₐ envₐ T' lps nP nIdx resSort isProp large cvTa cs ctorsA sortss) :
    SumCtorsRunJ rulesJ envᵦ envᵦ T' lps nP nIdx resSort isProp large cvTa cs ctorsA sortss := by
  refine ⟨hcs.1, hcs.2.1, fun j c cA hj hjA => ?_⟩
  obtain ⟨hnF, sorts, hsorts, hc⟩ := hcs.2.2 j c cA hj hjA
  exact ⟨hnF, sorts, hsorts, h.sumCtorRunJ hc⟩

end CapsUpgradeAt

/-! ## Index binder sorts from the telescope former (`FieldSortsJ`) -/

theorem infer_openPisAtFvars_sorts {env : Ix.Kernel.Env .anon} :
    ∀ (n : Nat) {d : Nat} {e ty : KExpr} {fvs : List KExpr} {o : KExpr},
      Infer env .full d e ty →
      Ix.Kernel.openPisAtFvars n e d = some (fvs, o) →
      ∀ (i : Nat), i < n →
        ∃ fv sdom u,
          fvs[i]? = some fv ∧
          Infer env .full (d + i) fv.fvarTypeD sdom ∧
          Red env (d + i) sdom (.sort u)
  | 0, _, _, _, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, d, e, ty, fvs, o, hinf, hop, i, hi => by
    cases hinf with
    | @forallE _ _ dom bo sdom sbo u₁ u₂ mb hty hrty hbo _ _ =>
      simp only [Ix.Kernel.openPisAtFvars] at hop
      split at hop
      · next fvs₁ o₁ hop₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        cases i with
        | zero =>
          refine ⟨.fvar d dom, sdom, u₁, rfl, ?_, ?_⟩
          · rw [Nat.add_zero]; exact hty
          · rw [Nat.add_zero]; exact hrty
        | succ i' =>
          simp only [List.getElem?_cons_succ]
          obtain ⟨fv, sdom', u', hfv, hinf', hred'⟩ :=
            infer_openPisAtFvars_sorts n hbo hop₁ i' (by omega)
          rw [show d + 1 + i' = d + (i' + 1) by omega] at hinf' hred'
          exact ⟨fv, sdom', u', hfv, hinf', hred'⟩
      · exact nomatch hop
    | sort | fvar _ | const _ _ _ | natLit _ | strLit _ | lam _ _ _ _ _ _ _
    | app _ _ _ _ | proj _ _ _ _ _ _ _ =>
      simp [Ix.Kernel.openPisAtFvars] at hop

/-- Extract `openPisAtFvars (nP + nIdx) cvTa.type 0 = some (tfvs, .sort resSort)` and
`FieldSortsJ rulesJ env₁ true false resSort nP (tfvs.drop nP) [] nIdx isorts` from a checked
telescope former `cvTa`. -/
theorem index_fieldSortsJ_of_former {env env₁ : Ix.Kernel.Env .anon}
    {cvT cvTa : KConstantVal} {nP nIdx : Nat}
    {bs : List (KExpr × Ix.Kernel.BinderMeta)} {resSort : KLevel}
    (hc : ConstantValCheckJ rulesJ env cvT cvTa)
    (hstrip : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort resSort))
    (hExt : EnvExt env env₁) :
    ∃ tfvs isorts,
      Ix.Kernel.openPisAtFvars (nP + nIdx) cvTa.type 0 = some (tfvs, .sort resSort) ∧
      FieldSortsJ rulesJ env₁ true false resSort nP (tfvs.drop nP) [] nIdx isorts := by
  obtain ⟨ty', ⟨_, _, _, _, _, _, _, _, _, ⟨sty, _, hinf, _⟩⟩, hcv⟩ := hc
  have hty_eq : cvTa.type = ty' := by rw [hcv]
  rw [← hty_eq] at hinf
  obtain ⟨tfvs, hop⟩ := Ix.Kernel.Model.openPisAtFvars_of_stripPis_sort (nP + nIdx) 0 hstrip
  have hlen : tfvs.length = nP + nIdx := Ix.Kernel.Model.openPisAtFvars_length (nP + nIdx) hop
  have hall := infer_openPisAtFvars_sorts (nP + nIdx) hinf hop
  let isortOf : Nat → KLevel := fun i =>
    if hi : i < nIdx then
      Classical.choose (Classical.choose_spec
        (Classical.choose_spec (hall (nP + i) (by omega))))
    else .zero
  refine ⟨tfvs, (List.range nIdx).map isortOf, hop, by simp, fun i hi => ?_⟩
  obtain ⟨u0, hu0⟩ : ∃ u0, isortOf i = u0 := ⟨isortOf i, rfl⟩
  have hspec_u0 : ∃ fv0 sdom0, tfvs[nP + i]? = some fv0 ∧
      Infer env .full (0 + (nP + i)) fv0.fvarTypeD sdom0 ∧
      Red env (0 + (nP + i)) sdom0 (.sort u0) := by
    rw [← hu0]
    simp only [isortOf, hi, ↓reduceDIte]
    exact ⟨_, _, Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (hall (nP + i) (by omega))))⟩
  obtain ⟨fv0, sdom0, hfv, hinf_i, hred_i⟩ := hspec_u0
  have hdrop : (tfvs.drop nP)[i]? = some fv0 := by
    rw [List.getElem?_drop]; exact hfv
  have hisort : ((List.range nIdx).map isortOf)[i]? = some u0 := by
    rw [List.getElem?_map, List.getElem?_range hi, Option.map_some, hu0]
  rw [Nat.zero_add] at hinf_i hred_i
  exact ⟨fv0, sdom0, u0, hdrop, hisort,
    Infer.weaken hExt hinf_i, Red.weaken hExt hred_i,
    (fun h => nomatch h), (fun _ h => nomatch h)⟩

/-! ## Spine helpers, `instOpen`, and `classifyFixKinds` + `nativeFieldsOk` -/

theorem mkAppN_append :
    ∀ (xs ys : List KExpr) (hd : KExpr),
      Expr.mkAppN hd (xs ++ ys) = Expr.mkAppN (Expr.mkAppN hd xs) ys
  | [], _, _ => rfl
  | x :: xs, ys, hd => mkAppN_append xs ys (.app hd x)

theorem eq_mkAppN_getApp :
    ∀ (e : KExpr),
      Expr.mkAppN e.getAppFn e.getAppArgs = e
  | .app f a => by
    rw [Expr.getAppFn, Expr.getAppArgs, mkAppN_append]
    simp [Expr.mkAppN, eq_mkAppN_getApp f]
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _
  | .lam _ _ _ | .forallE _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

theorem getAppFn_mkAppN :
    ∀ (args : List KExpr) (hd : KExpr),
      (Expr.mkAppN hd args).getAppFn = hd.getAppFn
  | [], _ => rfl
  | a :: args, hd => getAppFn_mkAppN args (.app hd a)

theorem getAppArgs_mkAppN :
    ∀ (args : List KExpr) (hd : KExpr),
      (Expr.mkAppN hd args).getAppArgs = hd.getAppArgs ++ args
  | [], _ => by simp [Expr.mkAppN]
  | a :: args, hd => by
    simp [Expr.mkAppN, getAppArgs_mkAppN args (.app hd a), Expr.getAppArgs, List.append_assoc]

theorem getAppArgs_mkAppN_const (c : KKey) (us : List KLevel) (args : List KExpr) :
    (Expr.mkAppN (.const c us) args).getAppArgs = args := by
  rw [getAppArgs_mkAppN]
  rfl

/-- Sequential instantiation of an opened free-variable prefix `vs` at binder depth `j`. -/
def instOpen : List KExpr → Nat → KExpr → KExpr
  | [], _, e => e
  | v :: vs, j, e => instOpen vs j (e.instantiate1 v (j + vs.length))

theorem instOpen_const (vs : List KExpr) (j : Nat) (c : KKey) (us : List KLevel) :
    instOpen vs j (.const c us) = .const c us := by
  induction vs generalizing j with
  | nil => rfl
  | cons _ vs ih => exact ih j

theorem instOpen_fvar (vs : List KExpr) (j idx : Nat) (ty : KExpr) :
    instOpen vs j (.fvar idx ty) = .fvar idx ty := by
  induction vs generalizing j with
  | nil => rfl
  | cons _ vs ih => exact ih j

theorem instOpen_app (vs : List KExpr) :
    ∀ (j : Nat) (f a : KExpr),
      instOpen vs j (.app f a) = .app (instOpen vs j f) (instOpen vs j a) := by
  induction vs with
  | nil => intros; rfl
  | cons v vs ih => intro j f a; exact ih j (f.instantiate1 v (j + vs.length)) (a.instantiate1 v (j + vs.length))

theorem instOpen_forallE (vs : List KExpr) :
    ∀ (j : Nat) (dom bo : KExpr) (mb : Ix.Kernel.BinderMeta),
      instOpen vs j (.forallE dom bo mb) =
        .forallE (instOpen vs j dom) (instOpen vs (j + 1) bo) mb := by
  induction vs with
  | nil => intros; rfl
  | cons v vs ih =>
    intro j dom bo mb
    simp only [instOpen, Expr.instantiate1, show j + vs.length + 1 = j + 1 + vs.length by omega]
    exact ih j _ _ mb

theorem instOpen_mkAppN (vs : List KExpr) (j : Nat) :
    ∀ (args : List KExpr) (hd : KExpr),
      instOpen vs j (Expr.mkAppN hd args) =
        Expr.mkAppN (instOpen vs j hd) (args.map (instOpen vs j))
  | [], _ => rfl
  | a :: args, hd => by
    show instOpen vs j (Expr.mkAppN (.app hd a) args) = _
    rw [instOpen_mkAppN vs j args (.app hd a), instOpen_app]
    rfl

theorem instOpen_append :
    ∀ (vs₁ vs₂ : List KExpr) (j : Nat) (e : KExpr),
      instOpen (vs₁ ++ vs₂) j e = instOpen vs₂ j (instOpen vs₁ (j + vs₂.length) e)
  | [], _, _, _ => rfl
  | v :: vs₁, vs₂, j, e => by
    simp only [List.cons_append, instOpen, List.length_append,
      show j + (vs₁.length + vs₂.length) = j + vs₂.length + vs₁.length by omega]
    exact instOpen_append vs₁ vs₂ j _

/-- Closed-form characterization of `openPisAtFvars` in terms of `stripPis` and `instOpen`. -/
theorem openPisAtFvars_eq_instOpen :
    ∀ (m : Nat) {e : KExpr} {d : Nat} {bs : List (KExpr × Ix.Kernel.BinderMeta)}
      {body : KExpr} {fvs : List KExpr} {o : KExpr},
      e.stripPis m = some (bs, body) →
      Ix.Kernel.openPisAtFvars m e d = some (fvs, o) →
      o = instOpen fvs 0 body ∧
      (∀ v ∈ fvs, ∃ q ty, v = .fvar q ty) ∧
      ∀ (t : Nat) (b : KExpr × Ix.Kernel.BinderMeta) (fv : KExpr),
        bs[t]? = some b → fvs[t]? = some fv →
        fv = .fvar (d + t) (instOpen (fvs.take t) 0 b.1) := by
  intro m
  induction m with
  | zero =>
    intro e _ bs body fvs o hst hop
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hst
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨rfl, (fun _ h => nomatch h), (fun _ _ _ hb _ => nomatch hb)⟩
  | succ m ih =>
    intro e d bs body fvs o hst hop
    cases e with
    | forallE dom bo mb =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
      obtain ⟨⟨bs₀, body₀⟩, hst₀, heq⟩ := hst
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Ix.Kernel.openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have hlen' : fvs'.length = m := Ix.Kernel.Model.openPisAtFvars_length m hop'
        have hsome₁ := Expr.stripPis_instantiate1_isSome (v := .fvar d dom) m 0
          (by rw [hst₀]; rfl)
        obtain ⟨⟨bs₁, body₁⟩, hst₁⟩ := Option.isSome_iff_exists.mp hsome₁
        obtain ⟨hb_eq, hdom_eq⟩ := Expr.stripPis_instantiate1_eq (v := .fvar d dom) m 0 hst₀ hst₁
        rw [Nat.zero_add] at hb_eq
        subst hb_eq
        obtain ⟨ho', hall_fvar, hpos'⟩ := ih hst₁ hop'
        refine ⟨?_, ?_, ?_⟩
        · simp only [instOpen, Nat.zero_add, hlen']
          exact ho'
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact ⟨d, dom, rfl⟩
          · exact hall_fvar v hv
        · intro t b fv hbt hfvt
          cases t with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hbt hfvt
            subst hbt hfvt
            simp [instOpen]
          | succ t' =>
            simp only [List.getElem?_cons_succ] at hbt hfvt
            have hbs₁_len : bs₁.length = m := Expr.stripPis_length m hst₁
            have ht' : t' < m := by
              obtain ⟨ht_lt, _⟩ := List.getElem?_eq_some_iff.mp hfvt
              omega
            have hb₁_some : bs₁[t']? = some (bs₁[t']'(by omega)) :=
              List.getElem?_eq_getElem (by omega)
            have hd_eq := hdom_eq t' b (bs₁[t']'(by omega)) hbt hb₁_some
            rw [Nat.zero_add] at hd_eq
            have hfv_eq := hpos' t' (bs₁[t']'(by omega)) fv hb₁_some hfvt
            have htake_len : (fvs'.take t').length = t' := by
              rw [List.length_take]; omega
            rw [hfv_eq, hd_eq, show d + 1 + t' = d + (t' + 1) by omega]
            congr 1
            simp only [List.take_succ_cons, instOpen, Nat.zero_add, htake_len]
      · exact nomatch hop
    | _ => simp [Expr.stripPis] at hst

/-- When `vs` consists of `.fvar`s and each slot in `vs` is either `T`-free or corresponds to an
absent de Bruijn variable in `e`, `instOpen vs j e` preserves `mentionsConst T`. -/
def OpenFreeAt (T : KKey) (vs : List KExpr) (j : Nat) (e : KExpr) : Prop :=
  (∀ v ∈ vs, ∀ i, v.hasLooseBVar i = false) ∧
  ∀ (r : Nat) (v : KExpr), vs[r]? = some v →
    v.mentionsConst T = false ∨ e.hasLooseBVar (j + (vs.length - 1 - r)) = false

theorem OpenFreeAt.step {T : KKey} {v : KExpr} {vs : List KExpr} {j : Nat} {e : KExpr}
    (h : OpenFreeAt T (v :: vs) j e) :
    (e.instantiate1 v (j + vs.length)).mentionsConst T = e.mentionsConst T ∧
      OpenFreeAt T vs j (e.instantiate1 v (j + vs.length)) := by
  have hv_l : ∀ i, v.hasLooseBVar i = false := h.1 v List.mem_cons_self
  have h0 := h.2 0 v rfl
  simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at h0
  have hmc : (e.instantiate1 v (j + vs.length)).mentionsConst T = e.mentionsConst T := by
    rcases h0 with hvT | heB
    · exact mentionsConst_instantiate1_of_false hvT e (j + vs.length)
    · exact mentionsConst_instantiate1_of_not_hasLooseBVar e (j + vs.length) heB
  refine ⟨hmc, ⟨fun w hw => h.1 w (List.mem_cons_of_mem _ hw), fun r w hr => ?_⟩⟩
  have hr' : (v :: vs)[r + 1]? = some w := hr
  have hlt : r < vs.length := (List.getElem?_eq_some_iff.mp hr).1
  rcases h.2 (r + 1) w hr' with hwT | heB
  · exact Or.inl hwT
  · right
    rw [Ix.Kernel.Model.hasLooseBVar_instantiate1_lt hv_l e (j + (vs.length - 1 - r))
      (j + vs.length) (by omega)]
    have hidx : j + (vs.length - 1 - r) = j + ((v :: vs).length - 1 - (r + 1)) := by
      simp; omega
    rw [hidx]
    exact heB

theorem OpenFreeAt.mentionsConst_instOpen {T : KKey} :
    ∀ (vs : List KExpr) {j : Nat} {e : KExpr},
      OpenFreeAt T vs j e → (instOpen vs j e).mentionsConst T = e.mentionsConst T
  | [], _, _, _ => rfl
  | v :: vs, j, e, h => by
    obtain ⟨hmc, h'⟩ := h.step
    rw [instOpen, h'.mentionsConst_instOpen, hmc]

theorem OpenFreeAt.forallE {T : KKey} {vs : List KExpr} {j : Nat}
    {dom bo : KExpr} {mb : Ix.Kernel.BinderMeta}
    (h : OpenFreeAt T vs j (.forallE dom bo mb)) :
    OpenFreeAt T vs j dom ∧ OpenFreeAt T vs (j + 1) bo := by
  refine ⟨⟨h.1, fun r v hr => ?_⟩, ⟨h.1, fun r v hr => ?_⟩⟩
  · rcases h.2 r v hr with hv | hb
    · exact Or.inl hv
    · simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hb
      exact Or.inr hb.1
  · rcases h.2 r v hr with hv | hb
    · exact Or.inl hv
    · simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff,
        show j + (vs.length - 1 - r) + 1 = j + 1 + (vs.length - 1 - r) by omega] at hb
      exact Or.inr hb.2

theorem OpenFreeAt.app {T : KKey} {vs : List KExpr} {j : Nat} {f a : KExpr}
    (h : OpenFreeAt T vs j (.app f a)) :
    OpenFreeAt T vs j f ∧ OpenFreeAt T vs j a := by
  refine ⟨⟨h.1, fun r v hr => ?_⟩, ⟨h.1, fun r v hr => ?_⟩⟩
  · rcases h.2 r v hr with hv | hb
    · exact Or.inl hv
    · simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hb
      exact Or.inr hb.1
  · rcases h.2 r v hr with hv | hb
    · exact Or.inl hv
    · simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hb
      exact Or.inr hb.2

theorem OpenFreeAt.getAppArgs {T : KKey} {vs : List KExpr} {j : Nat} :
    ∀ {e : KExpr},
      OpenFreeAt T vs j e →
      ∀ a ∈ e.getAppArgs, OpenFreeAt T vs j a := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h x hx
    obtain ⟨hf, ha⟩ := h.app
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ihf hf x hx
    · exact ha
  | _ => intro _ _ hx; exact nomatch hx

private theorem instOpen_bvar_lt :
    ∀ (vs : List KExpr) (j b : Nat),
      b < j → instOpen vs j (.bvar b) = .bvar b
  | [], _, _, _ => rfl
  | _ :: vs, j, b, hlt => by
    simp only [instOpen, Expr.instantiate1]
    split
    · omega
    · split
      · omega
      · exact instOpen_bvar_lt vs j b hlt

private theorem instOpen_param_slot :
    ∀ (fvsP : List KExpr) (fieldFvs : List KExpr) (k p : Nat) (fv : KExpr),
      (∀ v ∈ fvsP, ∃ q ty, v = .fvar q ty) →
      fvsP[p]? = some fv →
      instOpen (fvsP ++ fieldFvs) k (.bvar (k + fieldFvs.length + fvsP.length - 1 - p)) = fv
  | [], _, _, p, _, _, hp => nomatch hp
  | v₀ :: fvsP', fieldFvs, k, 0, fv, hall, hp => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
    subst hp
    obtain ⟨q, ty, rfl⟩ := hall _ List.mem_cons_self
    simp only [List.cons_append, List.length_cons, instOpen, List.length_append,
      show k + fieldFvs.length + (fvsP'.length + 1) - 1 - 0 = k + (fvsP'.length + fieldFvs.length)
        by omega,
      Expr.instantiate1, ↓reduceIte, instOpen_fvar]
  | v₀ :: fvsP', fieldFvs, k, p + 1, fv, hall, hp => by
    simp only [List.getElem?_cons_succ] at hp
    have hp_lt : p < fvsP'.length := (List.getElem?_eq_some_iff.mp hp).1
    simp only [List.cons_append, List.length_cons, instOpen, List.length_append,
      Expr.instantiate1]
    split
    · omega
    · split
      · omega
      · rw [show k + fieldFvs.length + (fvsP'.length + 1) - 1 - (p + 1) =
          k + fieldFvs.length + fvsP'.length - 1 - p by omega]
        exact instOpen_param_slot fvsP' fieldFvs k p fv
          (fun w hw => hall w (List.mem_cons_of_mem _ hw)) hp

/-- Opening `fvsP ++ fieldFvs` at depth `k` maps `structPsAt (fieldFvs.length + k) fvsP.length`
onto `fvsP`. -/
theorem map_instOpen_structPsAt (fvsP fieldFvs : List KExpr) (k : Nat)
    (hall : ∀ v ∈ fvsP, ∃ q ty, v = .fvar q ty) :
    (Ix.Kernel.structPsAt (fieldFvs.length + k) fvsP.length).map (instOpen (fvsP ++ fieldFvs) k) =
      fvsP := by
  apply List.ext_getElem
  · simp [Ix.Kernel.structPsAt]
  · intro p h1 h2
    simp only [Ix.Kernel.structPsAt, List.length_map, List.length_range] at h1
    simp only [Ix.Kernel.structPsAt, List.getElem_map, List.getElem_range,
      show fieldFvs.length + k + fvsP.length - 1 - p =
        k + fieldFvs.length + fvsP.length - 1 - p by omega]
    exact instOpen_param_slot fvsP fieldFvs k p fvsP[p] hall (List.getElem?_eq_getElem h2)

private theorem hasLooseBVar_stripPis :
    ∀ (m : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {body : KExpr} (d : Nat),
      e.stripPis m = some (bs, body) → e.hasLooseBVar d = false →
      body.hasLooseBVar (d + m) = false ∧
      ∀ (u : Nat) (b : KExpr × Ix.Kernel.BinderMeta), bs[u]? = some b →
        b.1.hasLooseBVar (d + u) = false := by
  intro m
  induction m with
  | zero =>
    intro e bs body d hst hb
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact ⟨by simpa using hb, fun _ _ h => nomatch h⟩
  | succ m ih =>
    intro e bs body d hst hb
    cases e with
    | forallE dom bo mb =>
      simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hb
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
      obtain ⟨⟨bs', body'⟩, hst', heq⟩ := hst
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨hbody, hbs'⟩ := ih (d + 1) hst' hb.2
      refine ⟨by rw [show d + (m + 1) = d + 1 + m by omega]; exact hbody, fun u b hu => ?_⟩
      cases u with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hu
        subst hu; simpa using hb.1
      | succ u' =>
        simp only [List.getElem?_cons_succ] at hu
        rw [show d + (u' + 1) = d + 1 + u' by omega]
        exact hbs' u' b hu
    | _ => simp [Expr.stripPis] at hst

private theorem stripPis_split :
    ∀ (a b : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {body : KExpr},
      e.stripPis (a + b) = some (bs, body) →
      ∃ bs₁ rest bs₂,
        e.stripPis a = some (bs₁, rest) ∧
        rest.stripPis b = some (bs₂, body) ∧
        bs = bs₁ ++ bs₂ ∧ bs₁.length = a := by
  intro a
  induction a with
  | zero =>
    intro b e bs body hst
    rw [Nat.zero_add] at hst
    exact ⟨[], e, bs, rfl, hst, rfl, rfl⟩
  | succ a ih =>
    intro b e bs body hst
    cases e with
    | forallE dom bo mb =>
      rw [show a + 1 + b = (a + b) + 1 by omega] at hst
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
      obtain ⟨⟨bs', body'⟩, hst', heq⟩ := hst
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨bs₁, rest, bs₂, h1, h2, rfl, hlen⟩ := ih b hst'
      exact ⟨(dom, mb) :: bs₁, rest, bs₂, by simp [Expr.stripPis, h1], h2, rfl, by simp [hlen]⟩
    | _ =>
      rw [show a + 1 + b = (a + b) + 1 by omega] at hst
      simp [Expr.stripPis] at hst

private theorem recPosLeaf_recursive_inv {T : KKey} {lps : List LevelParam}
    {nP nIdx o : Nat} {e : KExpr} {k : Nat}
    (h : Ix.Kernel.recPositivityLeaf T lps nP nIdx o e k = .recursive) :
    k = 0 ∧ Ix.Kernel.recFamOk T lps nP nIdx (o + k) e = true := by
  unfold Ix.Kernel.recPositivityLeaf at h
  split at h
  · exact nomatch h
  · split at h
    · split at h
      · split at h
        · next hfam =>
          split at h
          · next hk0 => exact ⟨beq_iff_eq.mp hk0, hfam⟩
          · exact nomatch h
        · exact nomatch h
      · exact nomatch h
    · split at h
      · split at h <;> exact nomatch h
      · exact nomatch h

private theorem recPosLeaf_reflexive_inv {T : KKey} {lps : List LevelParam}
    {nP nIdx o : Nat} {e : KExpr} {k : Nat}
    (h : Ix.Kernel.recPositivityLeaf T lps nP nIdx o e k = .reflexive) :
    k ≠ 0 ∧ Ix.Kernel.recFamOk T lps nP nIdx (o + k) e = true := by
  unfold Ix.Kernel.recPositivityLeaf at h
  split at h
  · exact nomatch h
  · split at h
    · split at h
      · split at h
        · next hfam =>
          split at h
          · exact nomatch h
          · next hk0 => exact ⟨beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hk0), hfam⟩
        · exact nomatch h
      · exact nomatch h
    · split at h
      · split at h <;> exact nomatch h
      · exact nomatch h

private theorem recPosLeaf_ordinary_inv {T : KKey} {lps : List LevelParam}
    {nP nIdx o : Nat} {e : KExpr} {k : Nat}
    (h : Ix.Kernel.recPositivityLeaf T lps nP nIdx o e k = .ordinary) :
    e.mentionsConst T = false := by
  unfold Ix.Kernel.recPositivityLeaf at h
  split at h
  · next hnoT => simpa using hnoT
  · split at h
    · split at h
      · split at h
        · split at h <;> exact nomatch h
        · exact nomatch h
      · exact nomatch h
    · split at h
      · split at h <;> exact nomatch h
      · exact nomatch h

private theorem recPositivity_ne_recursive_succ {T : KKey} {lps : List LevelParam}
    {nP nIdx o : Nat} :
    ∀ (e : KExpr) (k : Nat),
      Ix.Kernel.recPositivity T lps nP nIdx o e (k + 1) ≠ .recursive := by
  intro e
  induction e with
  | forallE d b _ _ ihb =>
    intro k h
    unfold Ix.Kernel.recPositivity at h
    split at h
    · exact nomatch h
    · exact ihb (k + 1) h
  | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
  | lit _ | proj _ _ _ =>
    intro k h
    rw [Ix.Kernel.recPositivity_leaf _ _ _ _ _ _ _ (by intro _ _ _ heq; cases heq)] at h
    obtain ⟨hk, _⟩ := recPosLeaf_recursive_inv h
    omega

private theorem recPositivity_recursive_inv {T : KKey} {lps : List LevelParam}
    {nP nIdx o : Nat} {dom : KExpr}
    (h : Ix.Kernel.recPositivity T lps nP nIdx o dom 0 = .recursive) :
    Ix.Kernel.recFamOk T lps nP nIdx o dom = true := by
  cases dom with
  | forallE d b mb =>
    unfold Ix.Kernel.recPositivity at h
    split at h
    · exact nomatch h
    · exact absurd h (recPositivity_ne_recursive_succ b 0)
  | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
  | lit _ | proj _ _ _ =>
    rw [Ix.Kernel.recPositivity_leaf _ _ _ _ _ _ _ (by intro _ _ _ heq; cases heq)] at h
    obtain ⟨_, hfam⟩ := recPosLeaf_recursive_inv h
    rwa [Nat.add_zero] at hfam

private theorem recPositivity_reflexive_inv {T : KKey} {lps : List LevelParam}
    {nP nIdx o : Nat} (dom : KExpr) :
    ∀ (k : Nat),
      Ix.Kernel.recPositivity T lps nP nIdx o dom k = .reflexive →
      let (abs, abody) := dom.piBinders
      k + abs.length ≠ 0 ∧
      (∀ b ∈ abs, b.1.mentionsConst T = false) ∧
      abody.piBinders = ([], abody) ∧
      Ix.Kernel.recFamOk T lps nP nIdx (o + (k + abs.length)) abody = true := by
  induction dom with
  | forallE d bo mb _ ihbo =>
    intro k h
    unfold Ix.Kernel.recPositivity at h
    split at h
    · exact nomatch h
    · next hd_noT =>
      simp only [Bool.not_eq_true] at hd_noT
      have ih := ihbo (k + 1) h
      cases hpb : bo.piBinders with
      | mk abs' abody' =>
        simp only [hpb] at ih
        simp only [Expr.piBinders, hpb, List.length_cons,
          show k + (abs'.length + 1) = k + 1 + abs'.length by omega]
        refine ⟨ih.1, fun b hb => ?_, ih.2.2.1, ih.2.2.2⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hd_noT
        · exact ih.2.1 b hb
  | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
  | lit _ | proj _ _ _ =>
    intro k h
    rw [Ix.Kernel.recPositivity_leaf _ _ _ _ _ _ _ (by intro _ _ _ heq; cases heq)] at h
    obtain ⟨hk, hfam⟩ := recPosLeaf_reflexive_inv h
    dsimp only [Expr.piBinders]
    rw [List.length_nil, Nat.add_zero]
    exact ⟨hk, (fun _ hb => nomatch hb), rfl, hfam⟩

private theorem piBinders_instOpen_of_const_head {c : KKey} {us : List KLevel} :
    ∀ (dom : KExpr) (vs : List KExpr) (j : Nat),
      dom.piBinders.2.getAppFn = .const c us →
      (instOpen vs j dom).piBinders =
        ((dom.piBinders.1.zipIdx).map (fun ⟨b, r⟩ => (instOpen vs (j + r) b.1, b.2)),
          instOpen vs (j + dom.piBinders.1.length) dom.piBinders.2) ∧
      (instOpen vs j dom).stripPis dom.piBinders.1.length =
        some ((dom.piBinders.1.zipIdx).map (fun ⟨b, r⟩ => (instOpen vs (j + r) b.1, b.2)),
          instOpen vs (j + dom.piBinders.1.length) dom.piBinders.2)
  | .forallE d bo mb, vs, j, hfn => by
    have hfn' : bo.piBinders.2.getAppFn = .const c us := by
      simpa [Expr.piBinders] using hfn
    obtain ⟨hpb, hst⟩ := piBinders_instOpen_of_const_head bo vs (j + 1) hfn'
    cases hbo_pb : bo.piBinders with
    | mk abs abody =>
      simp only [hbo_pb] at hpb hst
      rw [Expr.piBinders, hbo_pb, instOpen_forallE]
      have hzip :
          (((d, mb) :: abs).zipIdx).map (fun ⟨b, r⟩ => (instOpen vs (j + r) b.1, b.2)) =
            (instOpen vs j d, mb) ::
              (abs.zipIdx).map (fun ⟨b, r⟩ => (instOpen vs (j + 1 + r) b.1, b.2)) := by
        simp only [List.zipIdx_cons, Nat.add_zero, List.map_cons]
        congr 1
        rw [List.zipIdx_eq_map_add, List.map_map]
        apply List.map_congr_left
        intro ⟨b, r⟩ _
        simp [Function.comp_def, Nat.add_assoc, Nat.add_comm 1 r]
      refine ⟨?_, ?_⟩
      · simp only [Expr.piBinders, hpb, hzip, List.length_cons,
          show j + (abs.length + 1) = j + 1 + abs.length by omega]
      · simp only [List.length_cons, Expr.stripPis, hst, Option.map_some, hzip,
          show j + (abs.length + 1) = j + 1 + abs.length by omega]
  | .const c' us', vs, j, _ => by
    simp [Expr.piBinders, instOpen_const, Expr.stripPis]
  | .app f a, vs, j, _ => by
    simp [Expr.piBinders, instOpen_app, Expr.stripPis]
  | .bvar _, _, _, hfn | .fvar _ _, _, _, hfn | .sort _, _, _, hfn
  | .lam _ _ _, _, _, hfn | .letE _ _ _ _, _, _, hfn | .lit _, _, _, hfn
  | .proj _ _ _, _, _, hfn => nomatch hfn

private theorem openFree_piBinders {T : KKey} {vs : List KExpr} :
    ∀ (dom : KExpr) (j : Nat),
      OpenFreeAt T vs j dom →
      OpenFreeAt T vs (j + dom.piBinders.1.length) dom.piBinders.2 ∧
      ∀ (r : Nat) (b : KExpr × Ix.Kernel.BinderMeta),
        dom.piBinders.1[r]? = some b → OpenFreeAt T vs (j + r) b.1
  | .forallE d bo mb, j, h => by
    obtain ⟨hd, hbo⟩ := h.forallE
    obtain ⟨hbody, hbs⟩ := openFree_piBinders bo (j + 1) hbo
    cases hpb : bo.piBinders with
    | mk abs abody =>
      simp only [hpb] at hbody hbs
      simp only [Expr.piBinders, hpb, List.length_cons,
        show j + (abs.length + 1) = j + 1 + abs.length by omega]
      refine ⟨hbody, fun r b hr => ?_⟩
      cases r with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
        subst hr; simpa using hd
      | succ r' =>
        simp only [List.getElem?_cons_succ] at hr
        rw [show j + (r' + 1) = j + 1 + r' by omega]
        exact hbs r' b hr
  | .bvar _, j, h | .fvar _ _, j, h | .sort _, j, h | .const _ _, j, h
  | .app _ _, j, h | .lam _ _ _, j, h | .letE _ _ _ _, j, h | .lit _, j, h
  | .proj _ _ _, j, h => by
    simp only [Expr.piBinders, List.length_nil, Nat.add_zero]
    exact ⟨h, fun _ _ hr => nomatch hr⟩

private theorem recFamOk_opened {env env₁ : Ix.Kernel.Env .anon} {ci : KConstantInfo}
    {T : KKey} {lps : List LevelParam} {nP nIdx : Nat}
    {fvsP fieldFvs : List KExpr} {k : Nat} {abody : KExpr}
    (henv₁ : env₁ = ⟨ci :: env.consts⟩) (hci : ci.name = T)
    (hfvsP_len : fvsP.length = nP)
    (hfvsP_fv : ∀ v ∈ fvsP, ∃ q ty, v = .fvar q ty)
    (hfam : Ix.Kernel.recFamOk T lps nP nIdx (fieldFvs.length + k) abody = true)
    (hof : OpenFreeAt T (fvsP ++ fieldFvs) k abody)
    (hres : (instOpen (fvsP ++ fieldFvs) k abody).constsResolve env₁ = true)
    (hlit : litResolve env (instOpen (fvsP ++ fieldFvs) k abody) = true) :
    let body := instOpen (fvsP ++ fieldFvs) k abody
    body.getAppFn = .const T (lps.map .param) ∧
    body.getAppArgs.take nP = fvsP ∧
    body.getAppArgs.length = nP + nIdx ∧
    ∀ e ∈ body.getAppArgs.drop nP, e.constsResolve env = true := by
  simp only [Ix.Kernel.recFamOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    Bool.not_eq_true'] at hfam
  obtain ⟨⟨⟨hfn, hlen⟩, htake⟩, hdrop_noT⟩ := hfam
  have habody_eq :
      abody = Expr.mkAppN (.const T (lps.map .param))
        (Ix.Kernel.structPsAt (fieldFvs.length + k) nP ++ abody.getAppArgs.drop nP) := by
    have hsplit : abody.getAppArgs = abody.getAppArgs.take nP ++ abody.getAppArgs.drop nP :=
      (List.take_append_drop nP abody.getAppArgs).symm
    have hm := eq_mkAppN_getApp abody
    rw [hfn, hsplit, htake] at hm
    exact hm.symm
  have hbody_eq :
      instOpen (fvsP ++ fieldFvs) k abody =
        Expr.mkAppN (.const T (lps.map .param))
          (fvsP ++ (abody.getAppArgs.drop nP).map (instOpen (fvsP ++ fieldFvs) k)) := by
    conv_lhs => rw [habody_eq]
    rw [instOpen_mkAppN, instOpen_const, List.map_append]
    congr 2
    rw [← hfvsP_len]
    exact map_instOpen_structPsAt fvsP fieldFvs k hfvsP_fv
  have hargs :
      (instOpen (fvsP ++ fieldFvs) k abody).getAppArgs =
        fvsP ++ (abody.getAppArgs.drop nP).map (instOpen (fvsP ++ fieldFvs) k) := by
    rw [hbody_eq, getAppArgs_mkAppN_const]
  have hfn' : (instOpen (fvsP ++ fieldFvs) k abody).getAppFn = .const T (lps.map .param) := by
    rw [hbody_eq, getAppFn_mkAppN]; rfl
  have hdrop_len : (abody.getAppArgs.drop nP).length = nIdx := by
    rw [List.length_drop, hlen]; omega
  refine ⟨hfn', ?_, ?_, ?_⟩
  · rw [hargs, List.take_append_of_le_length (by omega), ← hfvsP_len, List.take_length]
  · rw [hargs, List.length_append, List.length_map, hfvsP_len, hdrop_len]
  · have hdrop_args :
        (instOpen (fvsP ++ fieldFvs) k abody).getAppArgs.drop nP =
          (abody.getAppArgs.drop nP).map (instOpen (fvsP ++ fieldFvs) k) := by
      rw [hargs]
      simpa [hfvsP_len] using List.drop_left (l₁ := fvsP)
        (l₂ := (abody.getAppArgs.drop nP).map (instOpen (fvsP ++ fieldFvs) k))
    rw [hdrop_args]
    intro e he
    obtain ⟨a, ha_mem, rfl⟩ := List.mem_map.mp he
    have ha_noT : a.mentionsConst T = false := hdrop_noT a ha_mem
    have ha_of : OpenFreeAt T (fvsP ++ fieldFvs) k a :=
      hof.getAppArgs a (List.mem_of_mem_drop ha_mem)
    have he_noT : (instOpen (fvsP ++ fieldFvs) k a).mentionsConst ci.name = false := by
      rw [hci, ha_of.mentionsConst_instOpen]; exact ha_noT
    have he_res₁ : (instOpen (fvsP ++ fieldFvs) k a).constsResolve env₁ = true :=
      (constsResolve_getApp hres).2 _ (by rw [hargs]; exact List.mem_append_right _ he)
    have he_lit : litResolve env (instOpen (fvsP ++ fieldFvs) k a) = true :=
      (litResolve_getApp hlit).2 _ (by rw [hargs]; exact List.mem_append_right _ he)
    exact constsResolve_of_cons_not_mentionsConst he_lit he_noT (by rwa [← henv₁])

private theorem mentionsConst_false_of_recPositivity_ordinary {T : KKey} {lps : List LevelParam}
    {nP nIdx o : Nat} :
    ∀ (dom : KExpr) (k : Nat),
      Ix.Kernel.recPositivity T lps nP nIdx o dom k = .ordinary →
      dom.mentionsConst T = false := by
  intro dom
  induction dom with
  | forallE d bo mb _ ihbo =>
    intro k h
    unfold Ix.Kernel.recPositivity at h
    split at h
    · exact nomatch h
    · next hd_noT =>
      simp only [Bool.not_eq_true] at hd_noT
      simp [Expr.mentionsConst, hd_noT, ihbo (k + 1) h]
  | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
  | lit _ | proj _ _ _ =>
    intro k h
    rw [Ix.Kernel.recPositivity_leaf _ _ _ _ _ _ _ (by intro _ _ _ heq; cases heq)] at h
    exact recPosLeaf_ordinary_inv h

private theorem mentionsConst_false_of_recFieldKind_ordinary {T : KKey} {lps : List LevelParam}
    {nP nIdx o : Nat} {dom : KExpr}
    (h : Ix.Kernel.recFieldKind T lps nP nIdx o dom = .ordinary) :
    dom.mentionsConst T = false := by
  unfold Ix.Kernel.recFieldKind at h
  split at h
  · exact mentionsConst_false_of_recPositivity_ordinary dom 0 h
  · next hnoT => exact Bool.eq_false_iff.mpr hnoT

private theorem openFreeAt_append_extra {T : KKey} {vs₁ : List KExpr} :
    ∀ (vs₂ : List KExpr) {e : KExpr},
      (∀ w ∈ vs₂, (∀ i, w.hasLooseBVar i = false) ∧ w.mentionsConst T = false) →
      OpenFreeAt T vs₁ vs₂.length e →
      OpenFreeAt T (vs₁ ++ vs₂) 0 e := by
  intro vs₂ e hvs₂ h₁
  refine ⟨fun w hw => ?_, fun r w hr => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact h₁.1 w hw
    · exact (hvs₂ w hw).1
  · by_cases hlt : r < vs₁.length
    · rw [List.getElem?_append_left hlt] at hr
      rcases h₁.2 r w hr with hwT | hb
      · exact Or.inl hwT
      · right
        simpa [List.length_append,
          show vs₁.length + vs₂.length - 1 - r = vs₂.length + (vs₁.length - 1 - r) by omega]
          using hb
    · rw [List.getElem?_append_right (by omega)] at hr
      have hw_mem : w ∈ vs₂ := List.mem_of_getElem? hr
      exact Or.inl (hvs₂ w hw_mem).2

private theorem not_mentionsFvar_of_leaf_free {q : Nat} {e : KExpr}
    (h : ∀ l ∈ e.fvarLeaves, l.1 ≠ q) :
    e.mentionsFvar q = false := by
  unfold Expr.mentionsFvar
  rw [List.any_eq_false]
  intro l hl
  simp [beq_iff_eq, h l hl]

/-- Single-constructor classification and opened-field verification from positivity and
unused-later recursive fields. -/
theorem recCtorKinds_and_nativeOpenedOk {env env₁ : Ix.Kernel.Env .anon} {ci : KConstantInfo}
    {T : KKey} {lps : List LevelParam} {nP nIdx : Nat}
    {cA : KConstantVal × Nat}
    {cbs : List (KExpr × Ix.Kernel.BinderMeta)} {es : List KExpr}
    (henv₁ : env₁ = ⟨ci :: env.consts⟩) (hci : ci.name = T)
    (hstrip : cA.1.type.stripPis (nP + cA.2) =
      some (cbs, Expr.mkAppN (.const T (lps.map .param)) (Ix.Kernel.structPsAt cA.2 nP ++ es)))
    (hes_len : es.length = nIdx)
    (hes_noT : ∀ a ∈ es, a.mentionsConst T = false)
    (hfv : cA.1.type.hasFvar = false)
    (hres : cA.1.type.constsResolve env₁ = true)
    (hlit : litResolve env cA.1.type = true)
    (hpdom_noT : ∀ p < nP, (cbs.getD p default).1.mentionsConst T = false)
    (hpos : ∀ i < cA.2,
      Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 ≠ .negative ∧
      Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 ≠ .unsupported)
    (hunused : ∀ i < cA.2,
      (Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 = .recursive ∨
       Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 = .reflexive) →
      Ix.Kernel.structUsedLater cA.1.type nP i = false) :
    ∃ ks,
      Ix.Kernel.recCtorKinds T lps nP nIdx cA = some ks ∧
      ks.length = cA.2 ∧
      (∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported) ∧
      Ix.Kernel.nativeOpenedOk env T lps nP nIdx cA.1.type cA.2 ks = true := by
  rcases cA with ⟨cvC, nF⟩
  dsimp only at *
  let cbody := Expr.mkAppN (.const T (lps.map .param)) (Ix.Kernel.structPsAt nF nP ++ es)
  have hcbs_len : cbs.length = nP + nF := Expr.stripPis_length (nP + nF) hstrip
  have hcbody_args : cbody.getAppArgs = Ix.Kernel.structPsAt nF nP ++ es :=
    getAppArgs_mkAppN_const T (lps.map .param) _
  have hps_len : (Ix.Kernel.structPsAt nF nP : List KExpr).length = nP := by
    simp [Ix.Kernel.structPsAt]
  have hcbody_drop : cbody.getAppArgs.drop nP = es := by
    rw [hcbody_args]
    simpa [hps_len] using List.drop_left (l₁ := Ix.Kernel.structPsAt nF nP) (l₂ := es)
  have hcbody_all_noT : (cbody.getAppArgs.drop nP).all (fun a => !a.mentionsConst T) = true := by
    rw [hcbody_drop, List.all_eq_true]
    intro a ha
    simp [hes_noT a ha]
  let ks : List Ix.Kernel.RecFieldKind :=
    (List.range nF).map fun i => Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1
  have hks_eq :
      ((List.range nF).map fun i =>
        match Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 with
        | .recursive => if Ix.Kernel.structUsedLater cvC.type nP i then .unsupported else .recursive
        | .reflexive => if Ix.Kernel.structUsedLater cvC.type nP i then .unsupported else .reflexive
        | k => k) = ks := by
    apply List.map_congr_left
    intro i hi
    have hi_lt : i < nF := List.mem_range.mp hi
    cases hkind : Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 with
    | ordinary | negative | unsupported => rfl
    | recursive => simp [hunused i hi_lt (Or.inl hkind)]
    | reflexive => simp [hunused i hi_lt (Or.inr hkind)]
  have hrck : Ix.Kernel.recCtorKinds T lps nP nIdx (cvC, nF) = some ks := by
    unfold Ix.Kernel.recCtorKinds
    dsimp only
    rw [hstrip]
    change (if ((cbody.getAppArgs.drop nP).all fun a => !a.mentionsConst T) = true then _ else _) =
      some ks
    rw [hcbody_all_noT]
    simp only [↓reduceIte]
    exact congrArg some hks_eq
  have hks_len : ks.length = nF := by simp [ks]
  have hks_ok : ∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    exact hpos i (List.mem_range.mp hi)
  refine ⟨ks, hrck, hks_len, hks_ok, ?_⟩
  -- Open parameters and fields
  obtain ⟨cbs₁, crest₀, _, hstP, _, _, _⟩ := stripPis_split nP nF hstrip
  obtain ⟨fvsP, crest, hopP⟩ :=
    Ix.Kernel.Model.openPisAtFvars_of_stripPis_isSome nP 0 (by rw [hstP]; rfl)
  have hfvsP_len : fvsP.length = nP := Ix.Kernel.Model.openPisAtFvars_length nP hopP
  have hstrip_some : (cvC.type.stripPis (nP + nF)).isSome = true := by rw [hstrip]; rfl
  obtain ⟨fvsAll_tmp, o_tmp, hopAll_tmp⟩ :=
    Ix.Kernel.Model.openPisAtFvars_of_stripPis_isSome (nP + nF) 0 hstrip_some
  -- `openPisAtFvars nF crest nP` must succeed because `openPisAtFvars (nP + nF) cvC.type 0` succeeds
  have hopF_ex : ∃ xFvs xrest, Ix.Kernel.openPisAtFvars nF crest nP = some (xFvs, xrest) := by
    have hsplit_open :
        ∀ (a b : Nat) {e : KExpr} {d : Nat} {fvsA : List KExpr} {oA : KExpr}
          {fvs₁ : List KExpr} {r₁ : KExpr},
          Ix.Kernel.openPisAtFvars (a + b) e d = some (fvsA, oA) →
          Ix.Kernel.openPisAtFvars a e d = some (fvs₁, r₁) →
          ∃ fvs₂ o₂, Ix.Kernel.openPisAtFvars b r₁ (d + a) = some (fvs₂, o₂) := by
      intro a
      induction a with
      | zero =>
        intro b e d fvsA oA fvs₁ r₁ hab ha
        simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        rw [Nat.zero_add] at hab
        rw [Nat.add_zero]
        exact ⟨fvsA, oA, hab⟩
      | succ a ih =>
        intro b e d fvsA oA fvs₁ r₁ hab ha
        cases e with
        | forallE dom bo mb =>
          rw [show a + 1 + b = a + b + 1 by omega] at hab
          simp only [Ix.Kernel.openPisAtFvars] at hab ha
          cases h1 : Ix.Kernel.openPisAtFvars (a + b) (bo.instantiate1 (.fvar d dom)) (d + 1) with
          | none => rw [h1] at hab; exact nomatch hab
          | some p1 =>
            cases h2 : Ix.Kernel.openPisAtFvars a (bo.instantiate1 (.fvar d dom)) (d + 1) with
            | none => rw [h2] at ha; exact nomatch ha
            | some p2 =>
              rw [h2] at ha
              simp only [Option.some.injEq, Prod.mk.injEq] at ha
              obtain ⟨rfl, rfl⟩ := ha
              obtain ⟨fvs₂, o₂, hb'⟩ := ih b h1 h2
              rw [show d + (a + 1) = d + 1 + a by omega]
              exact ⟨fvs₂, o₂, hb'⟩
        | _ => simp [Ix.Kernel.openPisAtFvars] at ha
    simpa using hsplit_open nP nF hopAll_tmp hopP
  obtain ⟨xFvs, xrest, hopF⟩ := hopF_ex
  have hxFvs_len : xFvs.length = nF := Ix.Kernel.Model.openPisAtFvars_length nF hopF
  have hopAll : Ix.Kernel.openPisAtFvars (nP + nF) cvC.type 0 = some (fvsP ++ xFvs, xrest) :=
    Ix.Kernel.Model.openPisAtFvars_add nP hopP (by simpa using hopF)
  obtain ⟨hxrest_eq, hall_fv, hpos_fv⟩ := openPisAtFvars_eq_instOpen (nP + nF) hstrip hopAll
  obtain ⟨hres_all, hxrest_res₁⟩ := openPisAtFvars_constsResolve (nP + nF) hres hopAll
  obtain ⟨hlit_all, hxrest_lit⟩ := openPisAtFvars_litResolve (nP + nF) hlit hopAll
  have hfvsP_fv : ∀ v ∈ fvsP, ∃ q ty, v = .fvar q ty :=
    fun v hv => hall_fv v (List.mem_append_left _ hv)
  have hall_nolb : ∀ v ∈ fvsP ++ xFvs, ∀ k, v.hasLooseBVar k = false := by
    intro v hv k
    obtain ⟨q, ty, rfl⟩ := hall_fv v hv
    rfl
  -- Unused recursive fields give `hasLooseBVar = false` on all later binders and on `cbody`
  have hunused_bvar :
      ∀ (m : Nat), m < nF →
        (Ix.Kernel.recFieldKind T lps nP nIdx m (cbs.getD (nP + m) default).1 = .recursive ∨
         Ix.Kernel.recFieldKind T lps nP nIdx m (cbs.getD (nP + m) default).1 = .reflexive) →
        cbody.hasLooseBVar (nP + nF - 1 - (nP + m)) = false ∧
        ∀ (t : Nat) (ht₁ : nP + m < t) (ht₂ : t < nP + nF),
          (cbs[t]'(by rw [hcbs_len]; exact ht₂)).1.hasLooseBVar (t - 1 - (nP + m)) = false := by
    intro m hm hkind
    have hun := hunused m hm hkind
    obtain ⟨cbs_pre, rest_m, cbs_post, hst_m, hst_post, hcbs_app, hpre_len⟩ :=
      stripPis_split (nP + m + 1) (nP + nF - (nP + m + 1))
        (by rw [show nP + m + 1 + (nP + nF - (nP + m + 1)) = nP + nF by omega]; exact hstrip)
    have hrest_lb : rest_m.hasLooseBVar 0 = false := by
      simp only [Ix.Kernel.structUsedLater, hst_m, Expr.hasLooseBVarB_eq] at hun
      exact hun
    obtain ⟨hcbody_lb, hpost_lb⟩ := hasLooseBVar_stripPis _ 0 hst_post hrest_lb
    refine ⟨?_, fun t ht₁ ht₂ => ?_⟩
    · simpa [show 0 + (nP + nF - (nP + m + 1)) = nP + nF - 1 - (nP + m) by omega] using hcbody_lb
    · have hcbs_t : (cbs_pre ++ cbs_post)[t]? = some (cbs[t]'(by rw [hcbs_len]; exact ht₂)) := by
        rw [← hcbs_app]
        exact List.getElem?_eq_getElem (by rw [hcbs_len]; exact ht₂)
      rw [List.getElem?_append_right (by omega), hpre_len] at hcbs_t
      have h := hpost_lb (t - (nP + m + 1)) (cbs[t]'(by rw [hcbs_len]; exact ht₂)) hcbs_t
      simpa [show 0 + (t - (nP + m + 1)) = t - 1 - (nP + m) by omega] using h
  -- Strong induction on `t < nP + nF` establishing `OpenFreeAt` and `mentionsConst T = false`
  -- on parameter slots and ordinary field slots
  have hslot :
      ∀ (t : Nat) (ht : t < nP + nF),
        OpenFreeAt T ((fvsP ++ xFvs).take t) 0 (cbs[t]'(by omega)).1 ∧
        ((t < nP ∨
          Ix.Kernel.recFieldKind T lps nP nIdx (t - nP) (cbs.getD t default).1 = .ordinary) →
          ((fvsP ++ xFvs)[t]'(by rw [List.length_append, hfvsP_len, hxFvs_len]; exact ht)).mentionsConst T = false) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t iht =>
      intro ht
      have hof_t : OpenFreeAt T ((fvsP ++ xFvs).take t) 0 (cbs[t]'(by omega)).1 := by
        refine ⟨fun v hv => hall_nolb v (List.mem_of_mem_take hv), fun r v hr => ?_⟩
        have htake_len : ((fvsP ++ xFvs).take t).length = t := by
          rw [List.length_take, List.length_append, hfvsP_len, hxFvs_len]; omega
        have hr_lt : r < t := by
          have := (List.getElem?_eq_some_iff.mp hr).1; omega
        rw [List.getElem?_take_of_lt hr_lt] at hr
        have hv_eq : v = (fvsP ++ xFvs)[r]'(by rw [List.length_append, hfvsP_len, hxFvs_len]; omega) := by
          rw [List.getElem?_eq_getElem] at hr
          exact (Option.some.inj hr).symm
        subst hv_eq
        by_cases hrP : r < nP
        · exact Or.inl ((iht r hr_lt (by omega)).2 (Or.inl hrP))
        · have hm_lt : r - nP < nF := by omega
          have hr_eq : nP + (r - nP) = r := by omega
          have hgetD_r : cbs.getD r default = cbs.getD (nP + (r - nP)) default := by rw [hr_eq]
          cases hkr : Ix.Kernel.recFieldKind T lps nP nIdx (r - nP)
              (cbs.getD (nP + (r - nP)) default).1 with
          | ordinary =>
            rw [← hgetD_r] at hkr
            exact Or.inl ((iht r hr_lt (by omega)).2 (Or.inr hkr))
          | recursive =>
            right
            rw [htake_len, Nat.zero_add, ← hr_eq]
            exact (hunused_bvar (r - nP) hm_lt (Or.inl hkr)).2 t (by omega) ht
          | reflexive =>
            right
            rw [htake_len, Nat.zero_add, ← hr_eq]
            exact (hunused_bvar (r - nP) hm_lt (Or.inr hkr)).2 t (by omega) ht
          | negative => exact absurd hkr (hpos (r - nP) hm_lt).1
          | unsupported => exact absurd hkr (hpos (r - nP) hm_lt).2
      refine ⟨hof_t, fun hcase => ?_⟩
      have hfv_eq := hpos_fv t (cbs[t]'(by omega))
        ((fvsP ++ xFvs)[t]'(by rw [List.length_append, hfvsP_len, hxFvs_len]; exact ht))
        (List.getElem?_eq_getElem (by omega))
        (List.getElem?_eq_getElem (by rw [List.length_append, hfvsP_len, hxFvs_len]; exact ht))
      have hdom_noT : (cbs[t]'(by omega)).1.mentionsConst T = false := by
        have hgetD : cbs.getD t default = cbs[t]'(by omega) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rcases hcase with htP | hord
        · rw [← hgetD]; exact hpdom_noT t htP
        · rw [← hgetD]
          exact mentionsConst_false_of_recFieldKind_ordinary hord
      rw [hfv_eq, Expr.mentionsConst, hof_t.mentionsConst_instOpen]
      exact hdom_noT
  have hof_cbody : OpenFreeAt T (fvsP ++ xFvs) 0 cbody := by
    refine ⟨hall_nolb, fun r v hr => ?_⟩
    have hall_len : (fvsP ++ xFvs).length = nP + nF := by
      rw [List.length_append, hfvsP_len, hxFvs_len]
    have hr_lt : r < nP + nF := by
      have := (List.getElem?_eq_some_iff.mp hr).1; omega
    have hv_eq : v = (fvsP ++ xFvs)[r]'(by omega) := by
      rw [List.getElem?_eq_getElem] at hr
      exact (Option.some.inj hr).symm
    subst hv_eq
    by_cases hrP : r < nP
    · exact Or.inl ((hslot r hr_lt).2 (Or.inl hrP))
    · have hm_lt : r - nP < nF := by omega
      have hr_eq : nP + (r - nP) = r := by omega
      have hgetD_r : cbs.getD r default = cbs.getD (nP + (r - nP)) default := by rw [hr_eq]
      cases hkr : Ix.Kernel.recFieldKind T lps nP nIdx (r - nP)
          (cbs.getD (nP + (r - nP)) default).1 with
      | ordinary =>
        rw [← hgetD_r] at hkr
        exact Or.inl ((hslot r hr_lt).2 (Or.inr hkr))
      | recursive =>
        right
        rw [hall_len, Nat.zero_add, ← hr_eq]
        exact (hunused_bvar (r - nP) hm_lt (Or.inl hkr)).1
      | reflexive =>
        right
        rw [hall_len, Nat.zero_add, ← hr_eq]
        exact (hunused_bvar (r - nP) hm_lt (Or.inr hkr)).1
      | negative => exact absurd hkr (hpos (r - nP) hm_lt).1
      | unsupported => exact absurd hkr (hpos (r - nP) hm_lt).2
  -- Now prove `nativeOpenedOk`
  unfold Ix.Kernel.nativeOpenedOk
  rw [hopP]
  dsimp only
  rw [hopF]
  dsimp only
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- Residual index arguments resolve in `env`
    have hcbody_fam : Ix.Kernel.recFamOk T lps nP nIdx (xFvs.length + 0) cbody = true := by
      simp only [Ix.Kernel.recFamOk, Nat.add_zero, hxFvs_len, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hcbody_all_noT⟩
      · show (Expr.mkAppN (.const T (lps.map .param)) _).getAppFn = _
        rw [getAppFn_mkAppN]; rfl
      · rw [hcbody_args, List.length_append, hps_len, hes_len]
      · rw [hcbody_args, List.take_append_of_le_length (by omega),
          List.take_of_length_le (by omega)]
    rw [hxrest_eq] at hxrest_res₁ hxrest_lit ⊢
    obtain ⟨_, _, _, hdrop_res⟩ :=
      recFamOk_opened henv₁ hci hfvsP_len hfvsP_fv hcbody_fam hof_cbody hxrest_res₁ hxrest_lit
    rw [List.all_eq_true]
    exact hdrop_res
  · -- Each field `i < nF`
    rw [List.all_eq_true]
    intro i hi_mem
    have hi : i < nF := List.mem_range.mp hi_mem
    have hi_x : i < xFvs.length := by rw [hxFvs_len]; exact hi
    have hxi_some : xFvs[i]? = some (xFvs[i]'hi_x) := List.getElem?_eq_getElem hi_x
    have hks_getD : ks.getD i .ordinary =
        Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 := by
      simp [ks, hi]
    rw [hxi_some, hks_getD]
    have htake_eq : (fvsP ++ xFvs).take (nP + i) = fvsP ++ xFvs.take i := by
      rw [List.take_append,
        List.take_of_length_le (by omega),
        show nP + i - fvsP.length = i by omega]
    have hxi_eq :
        xFvs[i]'hi_x =
          .fvar (nP + i) (instOpen (fvsP ++ xFvs.take i) 0 (cbs[nP + i]'(by rw [hcbs_len]; omega)).1) := by
      have h := hpos_fv (nP + i) (cbs[nP + i]'(by rw [hcbs_len]; omega)) (xFvs[i]'hi_x)
        (List.getElem?_eq_getElem (by rw [hcbs_len]; omega))
        (by rw [List.getElem?_append_right (by omega),
          show nP + i - fvsP.length = i by omega, List.getElem?_eq_getElem hi_x])
      rwa [Nat.zero_add, htake_eq] at h
    have hxi_fvarTypeD :
        (xFvs[i]'hi_x).fvarTypeD = instOpen (fvsP ++ xFvs.take i) 0 (cbs[nP + i]'(by rw [hcbs_len]; omega)).1 := by
      rw [hxi_eq]; rfl
    have hgetD_i : cbs.getD (nP + i) default = cbs[nP + i]'(by rw [hcbs_len]; omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hcbs_len]; omega), Option.getD_some]
    have hof_i : OpenFreeAt T (fvsP ++ xFvs.take i) 0 (cbs[nP + i]'(by rw [hcbs_len]; omega)).1 := by
      rw [← htake_eq]
      exact (hslot (nP + i) (by omega)).1
    have hxi_res₁ : (xFvs[i]'hi_x).fvarTypeD.constsResolve env₁ = true :=
      hres_all (xFvs[i]'hi_x) (List.mem_append_right _ (List.getElem_mem hi_x))
    have hxi_lit : litResolve env (xFvs[i]'hi_x).fvarTypeD = true :=
      hlit_all (xFvs[i]'hi_x) (List.mem_append_right _ (List.getElem_mem hi_x))
    -- Unused helper for `.recursive` and `.reflexive`
    have hleaf_unused :
        (Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 = .recursive ∨
         Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 = .reflexive) →
        (!(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
          !xrest.mentionsFvar (nP + i)) = true := by
      intro hk_rec
      have hun := hunused i hi hk_rec
      have hsome_st : (cvC.type.stripPis (nP + i + 1)).isSome = true :=
        Ix.Kernel.stripPis_isSome_of_le (by omega) hstrip_some
      obtain ⟨⟨bs_u, rest_u⟩, hst_u⟩ := Option.isSome_iff_exists.mp hsome_st
      have hrest_u : rest_u.hasLooseBVar 0 = false := by
        simp only [Ix.Kernel.structUsedLater, hst_u, Expr.hasLooseBVarB_eq] at hun
        exact hun
      obtain ⟨hleaves_k, hleaves_o⟩ := Ix.Kernel.Model.openPisAtFvars_leaf_free
        (nP + nF) (nP + i) hopAll (by omega) hst_u hrest_u
        (fun l hl => by
          rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv] at hl
          exact absurd hl List.not_mem_nil)
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨?_, not_mentionsFvar_of_leaf_free (by simpa using hleaves_o)⟩
      rw [List.any_eq_false]
      intro y hy
      obtain ⟨u, hu_lt, rfl⟩ := List.getElem_of_mem hy
      rw [List.length_drop, hxFvs_len] at hu_lt
      have hy_at : (fvsP ++ xFvs)[nP + (i + 1 + u)]? = some (xFvs.drop (i + 1))[u] := by
        rw [List.getElem?_append_right (by omega),
          show nP + (i + 1 + u) - fvsP.length = i + 1 + u by omega,
          List.getElem_drop, List.getElem?_eq_getElem (by omega)]
      have hy_fv : ∃ q ty, (xFvs.drop (i + 1))[u] = .fvar q ty :=
        hall_fv _ (List.mem_append_right _ (List.mem_of_mem_drop hy))
      obtain ⟨q, ty, hq_eq⟩ := hy_fv
      simp only [Bool.not_eq_true]
      refine not_mentionsFvar_of_leaf_free (fun l hl => ?_)
      have hl' : l ∈ ((xFvs.drop (i + 1))[u]).fvarLeaves := by
        rw [hq_eq] at hl ⊢
        simp only [Expr.fvarTypeD, Expr.fvarLeaves] at hl ⊢
        exact List.mem_cons_of_mem _ hl
      simpa using hleaves_k (nP + (i + 1 + u)) (by omega) _ hy_at l hl'
    cases hkind : Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 with
    | ordinary =>
      dsimp only
      have hdom_noT := mentionsConst_false_of_recFieldKind_ordinary hkind
      rw [hgetD_i] at hdom_noT
      have hxi_noT : (xFvs[i]'hi_x).fvarTypeD.mentionsConst ci.name = false := by
        rw [hci, hxi_fvarTypeD, hof_i.mentionsConst_instOpen]
        exact hdom_noT
      exact constsResolve_of_cons_not_mentionsConst hxi_lit hxi_noT (by rwa [← henv₁])
    | recursive =>
      dsimp only
      have hkind' := hkind
      unfold Ix.Kernel.recFieldKind at hkind'
      have hmc : (cbs.getD (nP + i) default).1.mentionsConst T = true := by
        cases h : (cbs.getD (nP + i) default).1.mentionsConst T
        · rw [h] at hkind'; exact nomatch hkind'
        · rfl
      simp only [hmc, ↓reduceIte] at hkind'
      have hfam := recPositivity_recursive_inv hkind'
      rw [hgetD_i] at hfam
      have htake_i_len : (xFvs.take i).length = i := by
        rw [List.length_take, hxFvs_len]; omega
      have hfam' : Ix.Kernel.recFamOk T lps nP nIdx ((xFvs.take i).length + 0)
          (cbs[nP + i]'(by rw [hcbs_len]; omega)).1 = true := by
        simpa [htake_i_len] using hfam
      rw [hxi_fvarTypeD] at hxi_res₁ hxi_lit ⊢
      obtain ⟨hfn', htake', hlen', hdrop'⟩ :=
        recFamOk_opened henv₁ hci hfvsP_len hfvsP_fv hfam' hof_i hxi_res₁ hxi_lit
      have hun_ok := hleaf_unused (Or.inl hkind)
      simp only [Bool.and_eq_true] at hun_ok
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
      exact ⟨⟨⟨⟨⟨hfn', htake'⟩, hlen'⟩, hdrop'⟩, hun_ok.1⟩, hun_ok.2⟩
    | reflexive =>
      dsimp only
      have hkind' := hkind
      unfold Ix.Kernel.recFieldKind at hkind'
      have hmc : (cbs.getD (nP + i) default).1.mentionsConst T = true := by
        cases h : (cbs.getD (nP + i) default).1.mentionsConst T
        · rw [h] at hkind'; exact nomatch hkind'
        · rfl
      simp only [hmc, ↓reduceIte] at hkind'
      rw [hgetD_i] at hkind'
      have hrefl := recPositivity_reflexive_inv (cbs[nP + i]'(by rw [hcbs_len]; omega)).1 0 hkind'
      cases hpb : (cbs[nP + i]'(by rw [hcbs_len]; omega)).1.piBinders with
      | mk abs abody =>
        simp only [hpb, Nat.zero_add] at hrefl
        obtain ⟨habs_ne, habs_noT, _, hfam⟩ := hrefl
        have habody_fn : abody.getAppFn = .const T (lps.map .param) := by
          simp only [Ix.Kernel.recFamOk, Bool.and_eq_true, beq_iff_eq] at hfam
          exact hfam.1.1.1
        obtain ⟨hpb_inst, hst_inst⟩ :=
          piBinders_instOpen_of_const_head (cbs[nP + i]'(by rw [hcbs_len]; omega)).1
            (fvsP ++ xFvs.take i) 0 (by rw [hpb]; exact habody_fn)
        simp only [hpb, Nat.zero_add] at hpb_inst hst_inst
        have hm_eq : ((xFvs[i]'hi_x).fvarTypeD.piBinders).1.length = abs.length := by
          rw [hxi_fvarTypeD, hpb_inst, List.length_map, List.length_zipIdx]
        rw [hm_eq]
        have hst_xi :
            (xFvs[i]'hi_x).fvarTypeD.stripPis abs.length =
              some ((abs.zipIdx).map (fun ⟨b, r⟩ =>
                  (instOpen (fvsP ++ xFvs.take i) r b.1, b.2)),
                instOpen (fvsP ++ xFvs.take i) abs.length abody) := by
          rw [hxi_fvarTypeD]; exact hst_inst
        obtain ⟨afvs, body', hopA⟩ :=
          Ix.Kernel.Model.openPisAtFvars_of_stripPis_isSome abs.length (nP + i)
            (by rw [hst_xi]; rfl)
        rw [hopA]
        dsimp only
        have hafvs_len : afvs.length = abs.length := Ix.Kernel.Model.openPisAtFvars_length abs.length hopA
        obtain ⟨hbody'_eq, hafvs_fv, hafvs_pos⟩ :=
          openPisAtFvars_eq_instOpen abs.length hst_xi hopA
        obtain ⟨hafvs_res₁, hbody'_res₁⟩ :=
          openPisAtFvars_constsResolve abs.length hxi_res₁ hopA
        obtain ⟨hafvs_lit, hbody'_lit⟩ :=
          openPisAtFvars_litResolve abs.length hxi_lit hopA
        obtain ⟨hof_abody, hof_abs⟩ := openFree_piBinders (cbs[nP + i]'(by rw [hcbs_len]; omega)).1 0 hof_i
        simp only [hpb, Nat.zero_add] at hof_abody hof_abs
        -- Every `a ∈ afvs` has `mentionsConst T = false`
        have hafvs_noT : ∀ (r : Nat) (hr : r < abs.length),
            (afvs[r]'(by rw [hafvs_len]; exact hr)).mentionsConst T = false := by
          intro r
          induction r using Nat.strong_induction_on with
          | h r ihr =>
            intro hr
            have hzip_r :
                ((abs.zipIdx).map (fun ⟨b, u⟩ =>
                  (instOpen (fvsP ++ xFvs.take i) u b.1, b.2)))[r]? =
                  some (instOpen (fvsP ++ xFvs.take i) r (abs[r]'hr).1, (abs[r]'hr).2) := by
              rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hr]
              simp
            have ha_eq := hafvs_pos r _ (afvs[r]'(by rw [hafvs_len]; exact hr)) hzip_r
              (List.getElem?_eq_getElem (by rw [hafvs_len]; exact hr))
            have htake_r_len : (afvs.take r).length = r := by
              rw [List.length_take, hafvs_len]; omega
            have hcomb :
                instOpen (afvs.take r) 0 (instOpen (fvsP ++ xFvs.take i) r (abs[r]'hr).1) =
                  instOpen ((fvsP ++ xFvs.take i) ++ afvs.take r) 0 (abs[r]'hr).1 := by
              have h := instOpen_append (fvsP ++ xFvs.take i) (afvs.take r) 0 (abs[r]'hr).1
              rw [Nat.zero_add, htake_r_len] at h
              exact h.symm
            have hof_r : OpenFreeAt T ((fvsP ++ xFvs.take i) ++ afvs.take r) 0 (abs[r]'hr).1 := by
              refine openFreeAt_append_extra (afvs.take r) (fun w hw => ?_) ?_
              · have hw_idx := List.getElem_of_mem hw
                obtain ⟨u, hu_lt, rfl⟩ := hw_idx
                rw [htake_r_len] at hu_lt
                have hfv_u := hafvs_fv _ (List.mem_of_mem_take hw)
                obtain ⟨q, ty, hq⟩ := hfv_u
                refine ⟨fun k => by rw [hq]; rfl, ?_⟩
                rw [List.getElem_take]
                exact ihr u hu_lt (by omega)
              · rw [htake_r_len]
                exact hof_abs r (abs[r]'hr) (List.getElem?_eq_getElem hr)
            rw [ha_eq, Expr.mentionsConst, hcomb, hof_r.mentionsConst_instOpen]
            exact habs_noT (abs[r]'hr) (List.getElem_mem hr)
        have hafvs_res_env : ∀ a ∈ afvs, a.fvarTypeD.constsResolve env = true := by
          intro a ha
          obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem ha
          have ha_fv := hafvs_fv _ ha
          obtain ⟨q, ty, hq⟩ := ha_fv
          have hnoT : (afvs[r]'hr).fvarTypeD.mentionsConst ci.name = false := by
            have := hafvs_noT r (by rw [← hafvs_len]; exact hr)
            rw [hq, Expr.mentionsConst] at this
            rw [hq, Expr.fvarTypeD, hci]
            exact this
          have hr₁ := hafvs_res₁ _ ha
          have hlit_a := hafvs_lit _ ha
          exact constsResolve_of_cons_not_mentionsConst hlit_a hnoT (by rwa [← henv₁])
        have hbody'_comb :
            body' = instOpen (fvsP ++ (xFvs.take i ++ afvs)) 0 abody := by
          have h := instOpen_append (fvsP ++ xFvs.take i) afvs 0 abody
          rw [Nat.zero_add, hafvs_len, List.append_assoc] at h
          rw [hbody'_eq, ← h]
        have hof_body' :
            OpenFreeAt T (fvsP ++ (xFvs.take i ++ afvs)) 0 abody := by
          rw [← List.append_assoc]
          refine openFreeAt_append_extra afvs (fun w hw => ?_) ?_
          · obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hw
            obtain ⟨q, ty, hq⟩ := hafvs_fv _ hw
            exact ⟨fun k => by rw [hq]; rfl, hafvs_noT r (by rw [← hafvs_len]; exact hr)⟩
          · rw [hafvs_len]; exact hof_abody
        have htake_i_len : (xFvs.take i).length = i := by
          rw [List.length_take, hxFvs_len]; omega
        have hfam' :
            Ix.Kernel.recFamOk T lps nP nIdx ((xFvs.take i ++ afvs).length + 0) abody = true := by
          simpa [List.length_append, htake_i_len, hafvs_len] using hfam
        rw [hbody'_comb] at hbody'_res₁ hbody'_lit ⊢
        obtain ⟨hfn', htake', hlen', hdrop'⟩ :=
          recFamOk_opened henv₁ hci hfvsP_len hfvsP_fv hfam' hof_body' hbody'_res₁ hbody'_lit
        have hun_ok := hleaf_unused (Or.inr hkind)
        simp only [Bool.and_eq_true] at hun_ok
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true]
        exact ⟨⟨⟨⟨⟨⟨⟨by rw [hafvs_len]; exact habs_ne, hafvs_res_env⟩, hfn'⟩, htake'⟩,
          hlen'⟩, hdrop'⟩, hun_ok.1⟩, hun_ok.2⟩
    | negative => exact absurd hkind (hpos i hi).1
    | unsupported => exact absurd hkind (hpos i hi).2

private theorem mapM_recCtorKinds_ok {T : KKey} {lps : List LevelParam} {nP nIdx : Nat} :
    ∀ {ctorsA : List (KConstantVal × Nat)} {kinds : List (List Ix.Kernel.RecFieldKind)},
      List.Forall₂
        (fun cA ks =>
          Ix.Kernel.recCtorKinds T lps nP nIdx cA = some ks ∧
          ks.length = cA.2 ∧
          ∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported)
        ctorsA kinds →
      ctorsA.mapM (Ix.Kernel.recCtorKinds T lps nP nIdx) = some kinds ∧
      kinds.any (fun ks => ks.any (· == .negative)) = false ∧
      kinds.any (fun ks => ks.any (· == .unsupported)) = false
  | _, _, .nil => ⟨rfl, rfl, rfl⟩
  | cA :: ctorsA, ks :: kinds, .cons ⟨hrck, _, hok⟩ htl => by
    obtain ⟨hmap, hneg, huns⟩ := mapM_recCtorKinds_ok htl
    have hks_neg : ks.any (· == .negative) = false := by
      rw [List.any_eq_false]
      intro k hk; simp [beq_iff_eq, (hok k hk).1]
    have hks_uns : ks.any (· == .unsupported) = false := by
      rw [List.any_eq_false]
      intro k hk; simp [beq_iff_eq, (hok k hk).2]
    refine ⟨by simp [List.mapM_cons, hrck, hmap], by simp [hks_neg, hneg], by simp [hks_uns, huns]⟩

private theorem forall2_get_nativeOpenedOk {env : Ix.Kernel.Env .anon}
    {T : KKey} {lps : List LevelParam} {nP nIdx : Nat} :
    ∀ {xs : List (KConstantVal × Nat)} {ys : List (List Ix.Kernel.RecFieldKind)},
      List.Forall₂
        (fun cA ks =>
          Ix.Kernel.recCtorKinds T lps nP nIdx cA = some ks ∧
          ks.length = cA.2 ∧
          (∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported) ∧
          Ix.Kernel.nativeOpenedOk env T lps nP nIdx cA.1.type cA.2 ks = true)
        xs ys →
      ∀ (u : Nat) (hu₁ : u < xs.length) (hu₂ : u < ys.length),
        (ys[u]'hu₂).length = (xs[u]'hu₁).2 ∧
        Ix.Kernel.nativeOpenedOk env T lps nP nIdx (xs[u]'hu₁).1.type (xs[u]'hu₁).2 (ys[u]'hu₂) = true
  | _, _, .nil, _, hu₁, _ => absurd hu₁ (Nat.not_lt_zero _)
  | _, _, .cons h _, 0, _, _ => ⟨h.2.1, h.2.2.2⟩
  | _, _, .cons _ htl, u + 1, hu₁, hu₂ =>
    forall2_get_nativeOpenedOk htl u (Nat.lt_of_succ_lt_succ hu₁) (Nat.lt_of_succ_lt_succ hu₂)

/-- Assemble `classifyFixKinds = .ok kinds` and `nativeFieldsOk = true` from per-constructor
`recCtorKinds` + `nativeOpenedOk` witnesses. -/
theorem classifyFixKinds_and_nativeFieldsOk {env : Ix.Kernel.Env .anon}
    {T : KKey} {lps : List LevelParam} {nP nIdx : Nat}
    {ctorsA : List (KConstantVal × Nat)} {kinds : List (List Ix.Kernel.RecFieldKind)}
    (hall : List.Forall₂
      (fun cA ks =>
        Ix.Kernel.recCtorKinds T lps nP nIdx cA = some ks ∧
        ks.length = cA.2 ∧
        (∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported) ∧
        Ix.Kernel.nativeOpenedOk env T lps nP nIdx cA.1.type cA.2 ks = true)
      ctorsA kinds) :
    Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM .anon) T lps nP nIdx ctorsA = .ok kinds ∧
      Ix.Kernel.nativeFieldsOk env T lps nP nIdx ctorsA kinds = true := by
  have hall' : List.Forall₂
      (fun cA ks =>
        Ix.Kernel.recCtorKinds T lps nP nIdx cA = some ks ∧
        ks.length = cA.2 ∧
        ∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported)
      ctorsA kinds := hall.imp (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
  obtain ⟨hmap, hneg, huns⟩ := mapM_recCtorKinds_ok hall'
  refine ⟨?_, ?_⟩
  · unfold Ix.Kernel.classifyFixKinds
    rw [hmap]
    show (do
      if kinds.any (fun ks => ks.any (· == .negative)) then throw _
      if kinds.any (fun ks => ks.any (· == .unsupported)) then throw _
      pure kinds : Ix.Kernel.CheckM .anon _) = .ok kinds
    rw [hneg, huns]
    rfl
  · unfold Ix.Kernel.nativeFieldsOk
    have hlen : ctorsA.length = kinds.length := hall.length_eq
    simp only [hlen, beq_self_eq_true, Bool.true_and, List.all_eq_true]
    intro j hj_mem
    have hj : j < kinds.length := List.mem_range.mp hj_mem
    have hjc : j < ctorsA.length := by omega
    rw [List.getElem?_eq_getElem hjc, List.getElem?_eq_getElem hj]
    obtain ⟨hklen, hopen⟩ := forall2_get_nativeOpenedOk hall j hjc hj
    simp [hklen, hopen]

/-! ## `checkStructProjTable`, `checkNativeTable`, and `InstallStep` assembly -/

private def projBodyWF (env : Ix.Kernel.Env .anon) (lps : List LevelParam) (k : Nat)
    (e : KExpr) : Prop :=
  e.hasFvar = false ∧
  e.allLevelParamsDefined lps = true ∧
  e.constsResolve env = true ∧
  e.looseBVarsBounded k = true

private theorem lbb_mono :
    ∀ {k₁ k₂ : Nat}, k₁ ≤ k₂ →
      ∀ {e : KExpr}, e.looseBVarsBounded k₁ = true → e.looseBVarsBounded k₂ = true := by
  intro k₁ k₂ hle e
  induction e generalizing k₁ k₂ with
  | bvar i =>
    intro h; simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h ⊢; omega
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _; rfl
  | app _ _ ihf iha =>
    intro h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨ihf hle h.1, iha hle h.2⟩
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iht hle h.1, ihb (by omega) h.2⟩
  | letE _ _ _ _ iht ihv ihb =>
    intro h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht hle h.1.1, ihv hle h.1.2⟩, ihb (by omega) h.2⟩
  | proj _ _ _ ihe => intro h; exact ihe hle h

private theorem liftLooseBVars_wf {env : Ix.Kernel.Env .anon} {lps : List LevelParam} (d : Nat) :
    ∀ (v : KExpr) (k s : Nat),
      projBodyWF env lps (k + s) v →
      projBodyWF env lps (k + d + s) (Expr.liftLooseBVars d s v)
  | .bvar i, k, s, ⟨hf, hl, hr, hb⟩ => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Expr.liftLooseBVars]; split <;> rfl
    · simp only [Expr.liftLooseBVars]; split <;> rfl
    · simp only [Expr.liftLooseBVars]; split <;> rfl
    · simp only [Expr.liftLooseBVars]
      split
      · simp only [Expr.looseBVarsBounded, decide_eq_true_eq]; omega
      · simp only [Expr.looseBVarsBounded, decide_eq_true_eq]; omega
  | .fvar _ _, _, _, ⟨hf, _, _, _⟩ => by simp [Expr.hasFvar] at hf
  | .sort _, _, _, ⟨hf, hl, hr, _⟩ => ⟨hf, hl, hr, rfl⟩
  | .const _ _, _, _, ⟨hf, hl, hr, _⟩ => ⟨hf, hl, hr, rfl⟩
  | .lit _, _, _, ⟨hf, hl, hr, _⟩ => ⟨hf, hl, hr, rfl⟩
  | .app f a, k, s, ⟨hf, hl, hr, hb⟩ => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hl
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hf₁, hl₁, hr₁, hb₁⟩ := liftLooseBVars_wf d f k s ⟨hf.1, hl.1, hr.1, hb.1⟩
    obtain ⟨hf₂, hl₂, hr₂, hb₂⟩ := liftLooseBVars_wf d a k s ⟨hf.2, hl.2, hr.2, hb.2⟩
    exact ⟨by simp [Expr.liftLooseBVars, Expr.hasFvar, hf₁, hf₂],
      by simp [Expr.liftLooseBVars, Expr.allLevelParamsDefined, hl₁, hl₂],
      by simp [Expr.liftLooseBVars, Expr.constsResolve, hr₁, hr₂],
      by simp [Expr.liftLooseBVars, Expr.looseBVarsBounded, hb₁, hb₂]⟩
  | .lam t b _, k, s, ⟨hf, hl, hr, hb⟩ | .forallE t b _, k, s, ⟨hf, hl, hr, hb⟩ => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hl
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hf₁, hl₁, hr₁, hb₁⟩ := liftLooseBVars_wf d t k s ⟨hf.1, hl.1.1, hr.1, hb.1⟩
    have hb_s : b.looseBVarsBounded (k + (s + 1)) = true := by
      rw [show k + (s + 1) = k + s + 1 by omega]; exact hb.2
    obtain ⟨hf₂, hl₂, hr₂, hb₂⟩ := liftLooseBVars_wf d b k (s + 1) ⟨hf.2, hl.1.2, hr.2, hb_s⟩
    rw [show k + d + (s + 1) = k + d + s + 1 by omega] at hb₂
    exact ⟨by simp [Expr.liftLooseBVars, Expr.hasFvar, hf₁, hf₂],
      by simp [Expr.liftLooseBVars, Expr.allLevelParamsDefined, hl₁, hl₂, hl.2],
      by simp [Expr.liftLooseBVars, Expr.constsResolve, hr₁, hr₂],
      by simp [Expr.liftLooseBVars, Expr.looseBVarsBounded, hb₁, hb₂]⟩
  | .letE t v b _, k, s, ⟨hf, hl, hr, hb⟩ => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hl
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hf₁, hl₁, hr₁, hb₁⟩ := liftLooseBVars_wf d t k s ⟨hf.1.1, hl.1.1, hr.1.1, hb.1.1⟩
    obtain ⟨hf₂, hl₂, hr₂, hb₂⟩ := liftLooseBVars_wf d v k s ⟨hf.1.2, hl.1.2, hr.1.2, hb.1.2⟩
    have hb_s : b.looseBVarsBounded (k + (s + 1)) = true := by
      rw [show k + (s + 1) = k + s + 1 by omega]; exact hb.2
    obtain ⟨hf₃, hl₃, hr₃, hb₃⟩ := liftLooseBVars_wf d b k (s + 1) ⟨hf.2, hl.2, hr.2, hb_s⟩
    rw [show k + d + (s + 1) = k + d + s + 1 by omega] at hb₃
    exact ⟨by simp [Expr.liftLooseBVars, Expr.hasFvar, hf₁, hf₂, hf₃],
      by simp [Expr.liftLooseBVars, Expr.allLevelParamsDefined, hl₁, hl₂, hl₃],
      by simp [Expr.liftLooseBVars, Expr.constsResolve, hr₁, hr₂, hr₃],
      by simp [Expr.liftLooseBVars, Expr.looseBVarsBounded, hb₁, hb₂, hb₃]⟩
  | .proj sn _ e, k, s, ⟨hf, hl, hr, hb⟩ => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    obtain ⟨hf₁, hl₁, hr₁, hb₁⟩ := liftLooseBVars_wf d e k s ⟨hf, hl, hr.2, hb⟩
    exact ⟨by simp [Expr.liftLooseBVars, Expr.hasFvar, hf₁],
      by simp [Expr.liftLooseBVars, Expr.allLevelParamsDefined, hl₁],
      by simp [Expr.liftLooseBVars, Expr.constsResolve, hr.1, hr₁],
      by simp [Expr.liftLooseBVars, Expr.looseBVarsBounded, hb₁]⟩

private theorem instantiate1Lift_wf {env : Ix.Kernel.Env .anon} {lps : List LevelParam}
    {v : KExpr} {k : Nat} (hv : projBodyWF env lps k v) :
    ∀ (e : KExpr) (d : Nat),
      projBodyWF env lps (k + 1 + d) e →
      projBodyWF env lps (k + d) (e.instantiate1Lift v d)
  | .bvar i, d, ⟨_, _, _, hb⟩ => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1Lift]
    split
    · simpa using liftLooseBVars_wf d v k 0 (by simpa using hv)
    · next hne =>
      split
      · exact ⟨rfl, rfl, rfl, by simp only [Expr.looseBVarsBounded, decide_eq_true_eq]; omega⟩
      · exact ⟨rfl, rfl, rfl, by simp only [Expr.looseBVarsBounded, decide_eq_true_eq]; omega⟩
  | .fvar _ _, _, ⟨hf, _, _, _⟩ => by simp [Expr.hasFvar] at hf
  | .sort _, _, ⟨hf, hl, hr, _⟩ => ⟨hf, hl, hr, rfl⟩
  | .const _ _, _, ⟨hf, hl, hr, _⟩ => ⟨hf, hl, hr, rfl⟩
  | .lit _, _, ⟨hf, hl, hr, _⟩ => ⟨hf, hl, hr, rfl⟩
  | .app f a, d, ⟨hf, hl, hr, hb⟩ => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hl
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hf₁, hl₁, hr₁, hb₁⟩ := instantiate1Lift_wf hv f d ⟨hf.1, hl.1, hr.1, hb.1⟩
    obtain ⟨hf₂, hl₂, hr₂, hb₂⟩ := instantiate1Lift_wf hv a d ⟨hf.2, hl.2, hr.2, hb.2⟩
    exact ⟨by simp [Expr.instantiate1Lift, Expr.hasFvar, hf₁, hf₂],
      by simp [Expr.instantiate1Lift, Expr.allLevelParamsDefined, hl₁, hl₂],
      by simp [Expr.instantiate1Lift, Expr.constsResolve, hr₁, hr₂],
      by simp [Expr.instantiate1Lift, Expr.looseBVarsBounded, hb₁, hb₂]⟩
  | .lam t b _, d, ⟨hf, hl, hr, hb⟩ | .forallE t b _, d, ⟨hf, hl, hr, hb⟩ => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hl
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hf₁, hl₁, hr₁, hb₁⟩ := instantiate1Lift_wf hv t d ⟨hf.1, hl.1.1, hr.1, hb.1⟩
    have hb' : b.looseBVarsBounded (k + 1 + (d + 1)) = true := by
      rw [show k + 1 + (d + 1) = k + 1 + d + 1 by omega]; exact hb.2
    obtain ⟨hf₂, hl₂, hr₂, hb₂⟩ := instantiate1Lift_wf hv b (d + 1) ⟨hf.2, hl.1.2, hr.2, hb'⟩
    rw [show k + (d + 1) = k + d + 1 by omega] at hb₂
    exact ⟨by simp [Expr.instantiate1Lift, Expr.hasFvar, hf₁, hf₂],
      by simp [Expr.instantiate1Lift, Expr.allLevelParamsDefined, hl₁, hl₂, hl.2],
      by simp [Expr.instantiate1Lift, Expr.constsResolve, hr₁, hr₂],
      by simp [Expr.instantiate1Lift, Expr.looseBVarsBounded, hb₁, hb₂]⟩
  | .letE t val b _, d, ⟨hf, hl, hr, hb⟩ => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hl
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hf₁, hl₁, hr₁, hb₁⟩ := instantiate1Lift_wf hv t d ⟨hf.1.1, hl.1.1, hr.1.1, hb.1.1⟩
    obtain ⟨hf₂, hl₂, hr₂, hb₂⟩ := instantiate1Lift_wf hv val d ⟨hf.1.2, hl.1.2, hr.1.2, hb.1.2⟩
    have hb' : b.looseBVarsBounded (k + 1 + (d + 1)) = true := by
      rw [show k + 1 + (d + 1) = k + 1 + d + 1 by omega]; exact hb.2
    obtain ⟨hf₃, hl₃, hr₃, hb₃⟩ := instantiate1Lift_wf hv b (d + 1) ⟨hf.2, hl.2, hr.2, hb'⟩
    rw [show k + (d + 1) = k + d + 1 by omega] at hb₃
    exact ⟨by simp [Expr.instantiate1Lift, Expr.hasFvar, hf₁, hf₂, hf₃],
      by simp [Expr.instantiate1Lift, Expr.allLevelParamsDefined, hl₁, hl₂, hl₃],
      by simp [Expr.instantiate1Lift, Expr.constsResolve, hr₁, hr₂, hr₃],
      by simp [Expr.instantiate1Lift, Expr.looseBVarsBounded, hb₁, hb₂, hb₃]⟩
  | .proj sn _ e, d, ⟨hf, hl, hr, hb⟩ => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    obtain ⟨hf₁, hl₁, hr₁, hb₁⟩ := instantiate1Lift_wf hv e d ⟨hf, hl, hr.2, hb⟩
    exact ⟨by simp [Expr.instantiate1Lift, Expr.hasFvar, hf₁],
      by simp [Expr.instantiate1Lift, Expr.allLevelParamsDefined, hl₁],
      by simp [Expr.instantiate1Lift, Expr.constsResolve, hr.1, hr₁],
      by simp [Expr.instantiate1Lift, Expr.looseBVarsBounded, hb₁]⟩

private theorem instPisAtLift_wf {env : Ix.Kernel.Env .anon} {lps : List LevelParam}
    {k : Nat} :
    ∀ (as_ : List KExpr) {m : Nat} {e : KExpr},
      (∀ a ∈ as_, projBodyWF env lps k a) →
      (e.stripPis (as_.length + m)).isSome = true →
      projBodyWF env lps k e →
      ∃ r, Expr.instPisAtLift as_ e = some r ∧
        (r.stripPis m).isSome = true ∧ projBodyWF env lps k r
  | [], m, e, _, hst, hwf => ⟨e, rfl, by simpa using hst, hwf⟩
  | a :: as_, m, e, has, hst, ⟨hf, hl, hr, hb⟩ => by
    rw [List.length_cons, show as_.length + 1 + m = (as_.length + m) + 1 by omega] at hst
    cases e with
    | forallE dom bo mb =>
      simp only [Expr.stripPis, Option.isSome_map] at hst
      obtain ⟨⟨bs₀, body₀⟩, hst₀⟩ := Option.isSome_iff_exists.mp hst
      obtain ⟨bs₁, hst₁, _⟩ := Expr.stripPis_instantiate1Lift_full (v := a) (as_.length + m) 0 hst₀
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hl
      simp only [Expr.constsResolve, Bool.and_eq_true] at hr
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      have hwf_bo : projBodyWF env lps k (bo.instantiate1Lift a) := by
        simpa using instantiate1Lift_wf (has a List.mem_cons_self) bo 0
          ⟨hf.2, hl.1.2, hr.2, by simpa using hb.2⟩
      exact instPisAtLift_wf as_ (fun x hx => has x (List.mem_cons_of_mem _ hx))
        (by rw [hst₁]; rfl) hwf_bo
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
    | lit _ | proj _ _ _ => simp [Expr.stripPis] at hst

private theorem structProjBodiesGo_wf {env : Ix.Kernel.Env .anon} {T : KKey}
    {lps : List LevelParam} {nP : Nat} (hT : (env.find? T).isSome = true) :
    ∀ (m i : Nat) {r : KExpr},
      (r.stripPis m).isSome = true →
      projBodyWF env lps (nP + 1) r →
      ∃ bs, Ix.Kernel.structProjBodiesGo T m i r = some bs ∧
        bs.length = m ∧ ∀ b ∈ bs, projBodyWF env lps (nP + 1) b
  | 0, _, _, _, _ => ⟨[], rfl, rfl, fun _ hb => nomatch hb⟩
  | m + 1, i, r, hst, ⟨hf, hl, hr, hb⟩ => by
    cases r with
    | forallE fdom bo mb =>
      simp only [Expr.stripPis, Option.isSome_map] at hst
      obtain ⟨⟨bs₀, body₀⟩, hst₀⟩ := Option.isSome_iff_exists.mp hst
      obtain ⟨bs₁, hst₁, _⟩ :=
        Expr.stripPis_instantiate1Lift_full (v := Ix.Kernel.structProjArgP T i) m 0 hst₀
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hl
      simp only [Expr.constsResolve, Bool.and_eq_true] at hr
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      have harg_wf : projBodyWF env lps (nP + 1) (Ix.Kernel.structProjArgP T i) :=
        ⟨rfl, rfl, by simp [Ix.Kernel.structProjArgP, Expr.constsResolve, hT],
          by simp [Ix.Kernel.structProjArgP, Expr.looseBVarsBounded]⟩
      have hbo_wf : projBodyWF env lps (nP + 1)
          (bo.instantiate1Lift (Ix.Kernel.structProjArgP T i)) := by
        simpa using instantiate1Lift_wf harg_wf bo 0 ⟨hf.2, hl.1.2, hr.2, by simpa using hb.2⟩
      obtain ⟨bs', hgo, hlen', hall'⟩ :=
        structProjBodiesGo_wf hT m (i + 1) (by rw [hst₁]; rfl) hbo_wf
      refine ⟨fdom :: bs', by simp [Ix.Kernel.structProjBodiesGo, hgo], by simp [hlen'], ?_⟩
      intro b hb_mem
      rcases List.mem_cons.mp hb_mem with rfl | hb_mem
      · exact ⟨hf.1, hl.1.1, hr.1, hb.1⟩
      · exact hall' b hb_mem
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
    | lit _ | proj _ _ _ => simp [Expr.stripPis] at hst

/-- Forward completeness of `checkStructProjTable` on a well-formed constructor with fresh
auxiliary projection keys. -/
theorem checkStructProjTable_ok {env : Ix.Kernel.Env .anon} {T C : KKey}
    {lps : List LevelParam} {nP nF : Nat} {resSort : KLevel}
    {guards : List KLevel} {off : Nat} {cvCa : KConstantVal}
    (hT : (env.find? T).isSome = true)
    (hstrip : (cvCa.type.stripPis (nP + nF)).isSome = true)
    (hfv : cvCa.type.hasFvar = false)
    (hlps : cvCa.type.allLevelParamsDefined lps = true)
    (hres : cvCa.type.constsResolve env = true)
    (hlbd : cvCa.type.looseBVarsBounded 0 = true)
    (hfn_fresh : ∀ j < nF, env.find? (Ix.Kernel.projFnName T j) = none)
    (htbl_fresh : env.find? (Ix.Kernel.projTableName T) = none) :
    ∃ env₂,
      Ix.Kernel.checkStructProjTable (m := Ix.Kernel.CheckM .anon)
        T C lps nP nF resSort guards off cvCa env = .ok env₂ := by
  have hps_len : (Ix.Kernel.structProjPs nP : List KExpr).length = nP := by
    simp [Ix.Kernel.structProjPs]
  have hps_wf : ∀ a ∈ (Ix.Kernel.structProjPs nP : List KExpr),
      projBodyWF env lps (nP + 1) a := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    have hr_lt : r < nP := List.mem_range.mp hr
    exact ⟨rfl, rfl, rfl, by simp only [Expr.looseBVarsBounded, decide_eq_true_eq]; omega⟩
  have hcv_wf : projBodyWF env lps (nP + 1) cvCa.type :=
    ⟨hfv, hlps, hres, lbb_mono (by omega) hlbd⟩
  obtain ⟨r, hinst, hr_st, hr_wf⟩ :=
    instPisAtLift_wf (Ix.Kernel.structProjPs nP) hps_wf (by rw [hps_len]; exact hstrip) hcv_wf
  obtain ⟨bs, hgo, hbs_len, hbs_wf⟩ := structProjBodiesGo_wf hT nF 0 hr_st hr_wf
  have hbodies : Ix.Kernel.structProjBodies T nP nF cvCa.type = some bs.toArray := by
    simp [Ix.Kernel.structProjBodies, hinst, hgo]
  have hall_arr :
      bs.toArray.size = nF ∧
      bs.toArray.all (fun b => !b.hasFvar && b.allLevelParamsDefined lps &&
        b.constsResolve env && b.looseBVarsBounded (nP + 1)) = true := by
    refine ⟨by simp [hbs_len], ?_⟩
    simp only [← Array.all_toList, List.toList_toArray, List.all_eq_true]
    intro b hb
    obtain ⟨hf', hl', hr', hb'⟩ := hbs_wf b hb
    simp [hf', hl', hr', hb']
  have hfn_all : (List.range nF).all (fun j => (env.find? (Ix.Kernel.projFnName T j)).isNone) = true := by
    rw [List.all_eq_true]
    intro j hj
    rw [hfn_fresh j (List.mem_range.mp hj)]
    rfl
  have htbl_none : (env.find? (Ix.Kernel.projTableName T)).isNone = true := by
    rw [htbl_fresh]; rfl
  refine ⟨⟨.projInfo ⟨T, lps, nP, C, nF, resSort, bs.toArray, guards, off⟩ :: env.consts⟩, ?_⟩
  unfold Ix.Kernel.checkStructProjTable
  rw [hbodies]
  show (do
    unless bs.toArray.size = nF ∧ bs.toArray.all _ do throw _
    unless (List.range nF).all _ do throw _
    unless (env.find? (Ix.Kernel.projTableName T)).isNone do throw _
    pure _ : Ix.Kernel.CheckM .anon _) = .ok _
  dsimp only
  rw [ite_eq_left hall_arr, ite_eq_left hfn_all, ite_eq_left htbl_none]
  rfl

/-- Forward completeness of `checkNativeTable` over an environment `env_base` where `p.cvT.name`
is stored, any single constructor `cA` is well-formed in `env_base`, and the auxiliary projection
keys of `p.cvT.name` are fresh in `env_base`. -/
theorem checkNativeTable_ok {env_base : Ix.Kernel.Env .anon}
    {p : Ix.Kernel.NativeParts .anon} {ctorsA : List (KConstantVal × Nat)}
    {sortss : List (List KLevel)}
    (hT : (env_base.find? p.cvT.name).isSome = true)
    (hc_wf : ∀ cA ∈ ctorsA,
      (cA.1.type.stripPis (p.nP + cA.2)).isSome = true ∧
      cA.1.type.hasFvar = false ∧
      cA.1.type.allLevelParamsDefined p.cvT.levelParams = true ∧
      cA.1.type.constsResolve env_base = true ∧
      cA.1.type.looseBVarsBounded 0 = true)
    (hfn_fresh : ∀ j, env_base.find? (Ix.Kernel.projFnName p.cvT.name j) = none)
    (htbl_fresh : env_base.find? (Ix.Kernel.projTableName p.cvT.name) = none) :
    ∃ env₂,
      Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss env_base =
        .ok env₂ ∧
      (env₂ = env_base ∨
        ∃ tbl : Ix.Kernel.ProjTable .anon,
          env_base.find? (Ix.Kernel.projTableName p.cvT.name) = none ∧
          tbl.structName = p.cvT.name ∧
          env₂ = ⟨.projInfo tbl :: env_base.consts⟩) := by
  unfold Ix.Kernel.checkNativeTable
  split
  · next cA sorts =>
    split
    · obtain ⟨hst, hfv, hlps, hres, hlbd⟩ := hc_wf cA List.mem_cons_self
      obtain ⟨env₂, hok⟩ := checkStructProjTable_ok hT hst hfv hlps hres hlbd
        (fun j _ => hfn_fresh j) htbl_fresh
      obtain ⟨tbl, hfr, hsn, rfl⟩ := Ix.Kernel.Semantics.checkStructProjTable_shape hok
      exact ⟨_, hok, Or.inr ⟨tbl, hfr, hsn, rfl⟩⟩
    · exact ⟨env_base, rfl, Or.inl rfl⟩
  · exact ⟨env_base, rfl, Or.inl rfl⟩

/-- Unified `InstallStep` builder for unpinned `.indDecl block nP` blocks whose stored real
members `new_base` are a permutation of `blockA` (`List.Forall₂ StoredAs blockA block`), optionally
followed by one fresh `.projInfo tbl` entry from `checkNativeTable`. -/
theorem installStep_of_perm_and_optTable {env env₂ : Ix.Kernel.Env .anon}
    {block blockA new_base : List KConstantInfo} {nP : Nat}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hnd : (block.map (·.name)).Nodup)
    (hfresh : ∀ ci₀ ∈ block, env.find? ci₀.name = none)
    (hstored : List.Forall₂ IxVM.Consistency.StoredAs blockA block)
    (hperm : new_base.Perm blockA)
    (henv₂ :
      env₂ = ⟨new_base ++ env.consts⟩ ∨
      ∃ tbl : Ix.Kernel.ProjTable .anon,
        (⟨new_base ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
          (Ix.Kernel.projTableName tbl.structName) = none ∧
        env₂ = ⟨.projInfo tbl :: new_base ++ env.consts⟩) :
    IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ := by
  have hinst : IxVM.Consistency.installs (.indDecl block nP) = block := by
    simp [IxVM.Consistency.installs, hpin]
  have hnames_eq : blockA.map (·.name) = block.map (·.name) := by
    clear hperm henv₂ hnd hfresh hpin hinst
    induction hstored with
    | nil => rfl
    | cons hs _ ih => simp [hs.name_eq, ih]
  have hnd_base : (new_base.map (·.name)).Nodup :=
    (hperm.map (·.name)).nodup_iff.mpr (by rwa [hnames_eq])
  have hmem_block_of_base : ∀ ci ∈ new_base, ∃ ci₀ ∈ block, ci₀.name = ci.name := by
    intro ci hci
    have hci_n : ci.name ∈ block.map (·.name) := by
      rw [← hnames_eq]
      exact List.mem_map_of_mem (hperm.subset hci)
    obtain ⟨ci₀, hmem₀, hn₀⟩ := List.mem_map.mp hci_n
    exact ⟨ci₀, hmem₀, hn₀⟩
  have hfresh_base : ∀ ci ∈ new_base, env.find? ci.name = none := by
    intro ci hci
    obtain ⟨ci₀, hmem₀, hn₀⟩ := hmem_block_of_base ci hci
    rw [← hn₀]
    exact hfresh ci₀ hmem₀
  have hcov_base : ∀ ci₀ ∈ block, ∃ ci ∈ new_base, IxVM.Consistency.StoredAs ci ci₀ := by
    intro ci₀ hci₀
    have hex : ∃ ci ∈ blockA, IxVM.Consistency.StoredAs ci ci₀ := by
      clear hperm henv₂ hnd hfresh hpin hinst hnames_eq hnd_base hmem_block_of_base hfresh_base
      induction hstored with
      | nil => exact nomatch hci₀
      | cons hs _ ih =>
        rcases List.mem_cons.mp hci₀ with rfl | hci₀
        · exact ⟨_, List.mem_cons_self, hs⟩
        · obtain ⟨x, hx, hsx⟩ := ih hci₀
          exact ⟨x, List.mem_cons_of_mem _ hx, hsx⟩
    obtain ⟨ci, hciA, hs⟩ := hex
    exact ⟨ci, hperm.symm.subset hciA, hs⟩
  rcases henv₂ with rfl | ⟨tbl, htbl_none, rfl⟩
  · refine ⟨new_base, rfl, hnd_base, hfresh_base, ?_, ?_⟩
    · rw [hinst]; exact hcov_base
    · rw [hinst]; intro ci hci; exact Or.inl (hmem_block_of_base ci hci)
  · have htbl_name : (.projInfo tbl : KConstantInfo).name =
        Ix.Kernel.projTableName tbl.structName := rfl
    have hfind_split :
        ∀ (xs : List KConstantInfo) (k : KKey),
          (⟨xs ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = none →
          k ∉ xs.map (·.name) ∧ env.find? k = none := by
      intro xs
      induction xs with
      | nil => intro k hf; exact ⟨List.not_mem_nil, hf⟩
      | cons x xs ih =>
        intro k hf
        simp only [Ix.Kernel.Env.find?, List.cons_append, List.find?_cons] at hf
        cases hxk : (x.name == k)
        · rw [hxk] at hf
          obtain ⟨hnm, he⟩ := ih k hf
          refine ⟨?_, he⟩
          intro hm
          rcases List.mem_cons.mp hm with rfl | hm
          · simp at hxk
          · exact hnm hm
        · rw [hxk] at hf; exact nomatch hf
    obtain ⟨htbl_notmem, htbl_env⟩ := hfind_split new_base _ htbl_none
    refine ⟨.projInfo tbl :: new_base, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, htbl_name]
      exact List.nodup_cons.mpr ⟨htbl_notmem, hnd_base⟩
    · intro ci hci
      rcases List.mem_cons.mp hci with rfl | hci
      · rw [htbl_name]; exact htbl_env
      · exact hfresh_base ci hci
    · rw [hinst]
      intro ci₀ hci₀
      obtain ⟨ci, hci, hs⟩ := hcov_base ci₀ hci₀
      exact ⟨ci, List.mem_cons_of_mem _ hci, hs⟩
    · rw [hinst]
      intro ci hci
      rcases List.mem_cons.mp hci with rfl | hci
      · exact Or.inr ⟨tbl.structName, .projTable, rfl⟩
      · exact Or.inl (hmem_block_of_base ci hci)

end IxVM.Refinement.Decl



