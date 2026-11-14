module

public import IxVMRefinement.Decl.NativeCommon
public import IxC.Kernel.Model.Inductives.StructRecKit2
public import IxC.Kernel.Model.Inductives.StructEntryFree
public import IxC.Kernel.Semantics.Inductives.DeclStructEta

@[expose] public section

namespace IxVM.Refinement.Decl

open IxVM
open Ix.Kernel (ConstantInfo ConstantVal RecRule Declaration Level LevelParam Expr)
open Ix.Kernel.Rules (Infer DefEq Red Certs DefEqList EtaProjCerts Grade EnvExt)
open Ix.Kernel.Semantics (rulesJ Judgements ConstantValRunJ ConstantValCheckJ
  FormerStoredJ SumIndRunJ FieldSortsJ StructDomsJ SumCtorRunJ SumCtorsRunJ FormerReadJ
  DeclNativeRunJ DeclNativeNoRecRunJ DeclRecTwinRunJ TwinRuleJ WrapRel WrapDom)

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
    ∀ {e : KExpr}, e.hasFvar = false → fvarNoProjAt T e = true
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .fvar _ _, h => by simp [Expr.hasFvar] at h
  | .app f a, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [fvarNoProjAt, fvarNoProjAt_of_hasFvar_false h.1, fvarNoProjAt_of_hasFvar_false h.2]
  | .lam ty bo _, h | .forallE ty bo _, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [fvarNoProjAt, fvarNoProjAt_of_hasFvar_false h.1, fvarNoProjAt_of_hasFvar_false h.2]
  | .letE ty v bo _, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [fvarNoProjAt, fvarNoProjAt_of_hasFvar_false h.1.1,
      fvarNoProjAt_of_hasFvar_false h.1.2, fvarNoProjAt_of_hasFvar_false h.2]
  | .proj _ _ e, h => fvarNoProjAt_of_hasFvar_false h

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
    ∀ {e : KExpr} (k : Nat), noProjAt T (e.instantiate1 v k) = true → noProjAt T e = true
  | .bvar _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .fvar _ _, _, h => h
  | .app _ _, k, h => by
    simp only [Expr.instantiate1, noProjAt, Bool.and_eq_true] at h ⊢
    exact ⟨noProjAt_of_instantiate1 k h.1, noProjAt_of_instantiate1 k h.2⟩
  | .lam _ _ _, k, h | .forallE _ _ _, k, h => by
    simp only [Expr.instantiate1, noProjAt, Bool.and_eq_true] at h ⊢
    exact ⟨noProjAt_of_instantiate1 k h.1, noProjAt_of_instantiate1 (k + 1) h.2⟩
  | .letE _ _ _ _, k, h => by
    simp only [Expr.instantiate1, noProjAt, Bool.and_eq_true] at h ⊢
    exact ⟨⟨noProjAt_of_instantiate1 k h.1.1, noProjAt_of_instantiate1 k h.1.2⟩,
      noProjAt_of_instantiate1 (k + 1) h.2⟩
  | .proj _ _ _, k, h => by
    simp only [Expr.instantiate1, noProjAt, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, noProjAt_of_instantiate1 k h.2⟩

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

theorem noProjAt_of_annotates {T : KKey} {e' e : KExpr} (ha : IxVM.Consistency.Annotates e' e) :
    noProjAt T e' = noProjAt T e := by
  induction ha with
  | bvar | sort | const | lit | fvar => rfl
  | app _ _ ihf iha => simp [noProjAt, ihf, iha]
  | lam _ _ iht ihb => simp [noProjAt, iht, ihb]
  | forallE _ _ iht ihb => simp [noProjAt, iht, ihb]
  | proj _ ihe => simp [noProjAt, ihe]

theorem noProjAt_stripPis {T : KKey} :
    ∀ {n : Nat} {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {body : KExpr},
      e.stripPis n = some (bs, body) → noProjAt T e = true →
      (∀ b ∈ bs, noProjAt T b.1 = true) ∧ noProjAt T body = true
  | 0, e, bs, body, hst, hnp => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact ⟨(fun _ hb => nomatch hb), hnp⟩
  | n + 1, .forallE dom bo mb, bs, body, hst, hnp => by
    simp only [noProjAt, Bool.and_eq_true] at hnp
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs', body'⟩, hst', heq⟩ := hst
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hbs', hbo'⟩ := noProjAt_stripPis hst' hnp.2
    refine ⟨fun b hb => ?_, hbo'⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hnp.1
    · exact hbs' b hb

private theorem noProjAt_getAppArgsAux {T : KKey} :
    ∀ (e : KExpr) (acc : List KExpr),
      noProjAt T e = true → (∀ a ∈ acc, noProjAt T a = true) →
      noProjAt T e.getAppFn = true ∧ ∀ a ∈ e.getAppArgsAux acc, noProjAt T a = true
  | .app f a, acc, h, hacc => by
    simp only [noProjAt, Bool.and_eq_true] at h
    refine noProjAt_getAppArgsAux f (a :: acc) h.1 (fun x hx => ?_)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.2
    · exact hacc x hx
  | .bvar _, _, h, hacc | .fvar _ _, _, h, hacc | .sort _, _, h, hacc
  | .const _ _, _, h, hacc | .lam _ _ _, _, h, hacc | .forallE _ _ _, _, h, hacc
  | .letE _ _ _ _, _, h, hacc | .lit _, _, h, hacc | .proj _ _ _, _, h, hacc => ⟨h, hacc⟩

theorem noProjAt_getApp {T : KKey} {e : KExpr} (h : noProjAt T e = true) :
    noProjAt T e.getAppFn = true ∧ ∀ a ∈ e.getAppArgs, noProjAt T a = true :=
  noProjAt_getAppArgsAux e [] h (fun _ hx => nomatch hx)

/-! ## `mentionsConst`, `constsResolve`, and `Annotates` combinators -/

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
    (ha : IxVM.Consistency.Annotates e' e) :
    e'.mentionsConst T = e.mentionsConst T := by
  induction ha with
  | bvar | sort | const | lit | fvar => rfl
  | app _ _ ihf iha => simp [Expr.mentionsConst, ihf, iha]
  | lam _ _ iht ihb => simp [Expr.mentionsConst, iht, ihb]
  | forallE _ _ iht ihb => simp [Expr.mentionsConst, iht, ihb]
  | proj _ ihe => simp [Expr.mentionsConst, ihe]

theorem hasLooseBVar_of_annotates {e' e : KExpr} (ha : IxVM.Consistency.Annotates e' e) :
    ∀ (k : Nat), e'.hasLooseBVar k = e.hasLooseBVar k := by
  induction ha with
  | bvar | sort | const | lit | fvar => intro _; rfl
  | app _ _ ihf iha => intro k; simp [Expr.hasLooseBVar, ihf k, iha k]
  | lam _ _ iht ihb => intro k; simp [Expr.hasLooseBVar, iht k, ihb (k + 1)]
  | forallE _ _ iht ihb => intro k; simp [Expr.hasLooseBVar, iht k, ihb (k + 1)]
  | proj _ ihe => intro k; simp [Expr.hasLooseBVar, ihe k]

theorem stripPis_of_annotates_right :
    ∀ {n : Nat} {e' e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {body : KExpr},
      IxVM.Consistency.Annotates e' e →
      e.stripPis n = some (bs, body) →
      ∃ bs' body',
        e'.stripPis n = some (bs', body') ∧
        List.Forall₂ (fun b' b => IxVM.Consistency.Annotates b'.1 b.1) bs' bs ∧
        IxVM.Consistency.Annotates body' body
  | 0, e', _, bs, body, ha, hst => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact ⟨[], e', rfl, .nil, ha⟩
  | n + 1, _, _, bs, body, .forallE hdom hbo, hst => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs₁, body₁⟩, hst₁, heq⟩ := hst
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨bs', body', hst', hbs', hbo'⟩ := stripPis_of_annotates_right hbo hst₁
    exact ⟨(_, _) :: bs', body', by simp [Expr.stripPis, hst'], .cons hdom hbs', hbo'⟩

theorem stripPis_of_annotates_left :
    ∀ {n : Nat} {e' e : KExpr} {bs' : List (KExpr × Ix.Kernel.BinderMeta)} {body' : KExpr},
      IxVM.Consistency.Annotates e' e →
      e'.stripPis n = some (bs', body') →
      ∃ bs body,
        e.stripPis n = some (bs, body) ∧
        List.Forall₂ (fun b' b => IxVM.Consistency.Annotates b'.1 b.1) bs' bs ∧
        IxVM.Consistency.Annotates body' body
  | 0, _, e, bs', body', ha, hst => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact ⟨[], e, rfl, .nil, ha⟩
  | n + 1, _, _, bs', body', .forallE hdom hbo, hst => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs₁, body₁⟩, hst₁, heq⟩ := hst
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨bs, body, hst', hbs, hbo'⟩ := stripPis_of_annotates_left hbo hst₁
    exact ⟨(_, _) :: bs, body, by simp [Expr.stripPis, hst'], .cons hdom hbs, hbo'⟩

theorem structUsedLater_of_annotates {e' e : KExpr} (ha : IxVM.Consistency.Annotates e' e)
    (nP j : Nat) :
    Ix.Kernel.structUsedLater e' nP j = Ix.Kernel.structUsedLater e nP j := by
  unfold Ix.Kernel.structUsedLater
  cases hst : e.stripPis (nP + j + 1) with
  | none =>
    cases hst' : e'.stripPis (nP + j + 1) with
    | none => rfl
    | some p' =>
      obtain ⟨bs, body, h, _, _⟩ := stripPis_of_annotates_left ha hst'
      rw [hst] at h
      exact nomatch h
  | some p =>
    obtain ⟨bs', body', hst', _, hbo⟩ := stripPis_of_annotates_right ha hst
    rw [hst', Expr.hasLooseBVarB_eq, Expr.hasLooseBVarB_eq]
    exact hasLooseBVar_of_annotates hbo 0

/-- If `e` does not mention `ci.name`, consing `ci` onto `env` leaves `constsResolve` unchanged. -/
theorem constsResolve_cons_of_not_mentionsConst {env : Ix.Kernel.Env .anon}
    {ci : KConstantInfo} :
    ∀ {e : KExpr}, e.mentionsConst ci.name = false →
      e.constsResolve ⟨ci :: env.consts⟩ = e.constsResolve env
  | .bvar _, _ | .sort _, _ | .lit _, _ => rfl
  | .const n _, hm => by
    simp only [Expr.mentionsConst, beq_eq_false_iff_ne] at hm
    have hne : (ci.name == n) = false := beq_eq_false_iff_ne.mpr (Ne.symm hm)
    simp [Expr.constsResolve, Ix.Kernel.Env.find?, List.find?, hne]
  | .fvar _ ty, hm => constsResolve_cons_of_not_mentionsConst hm
  | .app f a, hm => by
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm
    simp [Expr.constsResolve,
      constsResolve_cons_of_not_mentionsConst hm.1,
      constsResolve_cons_of_not_mentionsConst hm.2]
  | .lam ty bo _, hm | .forallE ty bo _, hm => by
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm
    simp [Expr.constsResolve,
      constsResolve_cons_of_not_mentionsConst hm.1,
      constsResolve_cons_of_not_mentionsConst hm.2]
  | .letE ty v bo _, hm => by
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hm
    simp [Expr.constsResolve,
      constsResolve_cons_of_not_mentionsConst hm.1.1,
      constsResolve_cons_of_not_mentionsConst hm.1.2,
      constsResolve_cons_of_not_mentionsConst hm.2]
  | .proj s _ e, hm => by
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hm
    have hne : (ci.name == s) = false := beq_eq_false_iff_ne.mpr (Ne.symm hm.1)
    simp [Expr.constsResolve, Ix.Kernel.Env.find?, List.find?, hne,
      constsResolve_cons_of_not_mentionsConst hm.2]

private theorem mentionsConst_getAppArgsAux {T : KKey} :
    ∀ (e : KExpr) (acc : List KExpr),
      e.mentionsConst T = false → (∀ a ∈ acc, a.mentionsConst T = false) →
      e.getAppFn.mentionsConst T = false ∧ ∀ a ∈ e.getAppArgsAux acc, a.mentionsConst T = false
  | .app f a, acc, h, hacc => by
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h
    refine mentionsConst_getAppArgsAux f (a :: acc) h.1 (fun x hx => ?_)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.2
    · exact hacc x hx
  | .bvar _, _, h, hacc | .fvar _ _, _, h, hacc | .sort _, _, h, hacc
  | .const _ _, _, h, hacc | .lam _ _ _, _, h, hacc | .forallE _ _ _, _, h, hacc
  | .letE _ _ _ _, _, h, hacc | .lit _, _, h, hacc | .proj _ _ _, _, h, hacc => ⟨h, hacc⟩

theorem mentionsConst_getApp {T : KKey} {e : KExpr} (h : e.mentionsConst T = false) :
    e.getAppFn.mentionsConst T = false ∧ ∀ a ∈ e.getAppArgs, a.mentionsConst T = false :=
  mentionsConst_getAppArgsAux e [] h (fun _ hx => nomatch hx)

private theorem constsResolve_getAppArgsAux {env : Ix.Kernel.Env .anon} :
    ∀ (e : KExpr) (acc : List KExpr),
      e.constsResolve env = true → (∀ a ∈ acc, a.constsResolve env = true) →
      e.getAppFn.constsResolve env = true ∧ ∀ a ∈ e.getAppArgsAux acc, a.constsResolve env = true
  | .app f a, acc, h, hacc => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    refine constsResolve_getAppArgsAux f (a :: acc) h.1 (fun x hx => ?_)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.2
    · exact hacc x hx
  | .bvar _, _, h, hacc | .fvar _ _, _, h, hacc | .sort _, _, h, hacc
  | .const _ _, _, h, hacc | .lam _ _ _, _, h, hacc | .forallE _ _ _, _, h, hacc
  | .letE _ _ _ _, _, h, hacc | .lit _, _, h, hacc | .proj _ _ _, _, h, hacc => ⟨h, hacc⟩

theorem constsResolve_getApp {env : Ix.Kernel.Env .anon} {e : KExpr}
    (h : e.constsResolve env = true) :
    e.getAppFn.constsResolve env = true ∧ ∀ a ∈ e.getAppArgs, a.constsResolve env = true :=
  constsResolve_getAppArgsAux e [] h (fun _ hx => nomatch hx)

theorem openPisAtFvars_constsResolve {env : Ix.Kernel.Env .anon} :
    ∀ (n : Nat) {e : KExpr} {d : Nat} {fvs : List KExpr} {o : KExpr},
      e.constsResolve env = true →
      Ix.Kernel.openPisAtFvars n e d = some (fvs, o) →
      (∀ x ∈ fvs, x.fvarTypeD.constsResolve env = true) ∧ o.constsResolve env = true
  | 0, e, _, fvs, o, he, hop => by
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨(fun _ hx => nomatch hx), he⟩
  | n + 1, .forallE dom bo mb, d, fvs, o, he, hop => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at he
    simp only [Ix.Kernel.openPisAtFvars] at hop
    split at hop
    · next fvs₁ o₁ hop₁ =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨rfl, rfl⟩ := hop
      have hbo : (bo.instantiate1 (.fvar d dom)).constsResolve env = true :=
        Expr.constsResolve_instantiate1 he.1 bo 0 he.2
      obtain ⟨hfvs₁, ho₁⟩ := openPisAtFvars_constsResolve n hbo hop₁
      refine ⟨fun x hx => ?_, ho₁⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact he.1
      · exact hfvs₁ x hx
    · exact nomatch hop

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
    simp only [Expr.instantiate1, if_neg (Ne.symm hk)]
    split <;> rfl
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

theorem constsResolve_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) :
    ∀ (e : KExpr), e.constsResolve envᵦ = e.constsResolve envₐ
  | .bvar _ | .sort _ | .lit _ => rfl
  | .const n _ => h.find_isSome_eq n
  | .fvar _ ty => h.constsResolve_eq ty
  | .app f a => by simp [Expr.constsResolve, h.constsResolve_eq f, h.constsResolve_eq a]
  | .lam ty bo _ | .forallE ty bo _ => by
    simp [Expr.constsResolve, h.constsResolve_eq ty, h.constsResolve_eq bo]
  | .letE ty v bo _ => by
    simp [Expr.constsResolve, h.constsResolve_eq ty, h.constsResolve_eq v, h.constsResolve_eq bo]
  | .proj s _ e => by simp [Expr.constsResolve, h.find_isSome_eq s, h.constsResolve_eq e]

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
    | @forallE _ dom bo mb sdom u₁ sbo u₂ hty hrty hbo _ _ =>
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
        (Classical.choose_spec (hall (nP + i) (by omega)))).2
    else .zero
  refine ⟨tfvs, (List.range nIdx).map isortOf, hop, by simp, fun i hi => ?_⟩
  have hni : nP + i < nP + nIdx := by omega
  let hspec := hall (nP + i) hni
  let fv := Classical.choose hspec
  let sdom := Classical.choose (Classical.choose_spec hspec)
  let u := Classical.choose (Classical.choose_spec (Classical.choose_spec hspec))
  obtain ⟨hfv, hinf_i, hred_i⟩ := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hspec))
  have hdrop : (tfvs.drop nP)[i]? = some fv := by
    rw [List.getElem?_drop]; exact hfv
  have hisort : ((List.range nIdx).map isortOf)[i]? = some u := by
    rw [List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some, Option.some.injEq, isortOf, dif_pos hi]
    rfl
  rw [Nat.zero_add] at hinf_i hred_i
  exact ⟨fv, sdom, u, hdrop, hisort,
    Infer.weaken hExt hinf_i, Red.weaken hExt hred_i,
    (fun h => nomatch h), (fun _ h => nomatch h)⟩

/-! ## Spine helpers, `instOpen`, and `classifyFixKinds` + `nativeFieldsOk` -/

theorem mkAppN_eq_of_getApp :
    ∀ (e : KExpr) (acc : List KExpr),
      Expr.mkAppN e.getAppFn (e.getAppArgsAux acc) = Expr.mkAppN e acc
  | .app f a, acc => mkAppN_eq_of_getApp f (a :: acc)
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _
  | .lam _ _ _, _ | .forallE _ _ _, _ | .letE _ _ _ _, _ | .lit _, _ | .proj _ _ _, _ => rfl

theorem eq_mkAppN_getApp (e : KExpr) :
    Expr.mkAppN e.getAppFn e.getAppArgs = e :=
  mkAppN_eq_of_getApp e []

theorem getAppFn_mkAppN :
    ∀ (args : List KExpr) (hd : KExpr),
      (Expr.mkAppN hd args).getAppFn = hd.getAppFn
  | [], _ => rfl
  | a :: args, hd => getAppFn_mkAppN args (.app hd a)

private theorem getAppArgsAux_mkAppN :
    ∀ (args : List KExpr) (hd : KExpr) (acc : List KExpr),
      (Expr.mkAppN hd args).getAppArgsAux acc = hd.getAppArgsAux (args ++ acc)
  | [], _, _ => rfl
  | a :: args, hd, acc => getAppArgsAux_mkAppN args (.app hd a) acc

theorem getAppArgs_mkAppN_const (c : KKey) (us : List KLevel) (args : List KExpr) :
    (Expr.mkAppN (.const c us) args).getAppArgs = args := by
  unfold Expr.getAppArgs
  rw [getAppArgsAux_mkAppN, List.append_nil]
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
        fv = .fvar (d + t) (instOpen (fvs.take t) 0 b.1)
  | 0, e, _, bs, body, fvs, o, hst, hop => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hst
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨rfl, (fun _ h => nomatch h), (fun _ _ _ hb _ => nomatch hb)⟩
  | m + 1, .forallE dom bo mb, d, bs, body, fvs, o, hst, hop => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs₀, body₀⟩, hst₀, heq⟩ := hst
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Ix.Kernel.openPisAtFvars] at hop
    split at hop
    · next fvs', o', hop' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨rfl, rfl⟩ := hop
      have hlen' : fvs'.length = m := Ix.Kernel.Model.openPisAtFvars_length m hop'
      have hsome₁ := Expr.stripPis_instantiate1_isSome (v := .fvar d dom) m 0
        (by rw [hst₀]; rfl)
      obtain ⟨⟨bs₁, body₁⟩, hst₁⟩ := Option.isSome_iff_exists.mp hsome₁
      obtain ⟨hb_eq, hdom_eq⟩ := Expr.stripPis_instantiate1_eq (v := .fvar d dom) m 0 hst₀ hst₁
      rw [Nat.zero_add] at hb_eq
      subst hb_eq
      obtain ⟨ho', hall_fvar, hpos'⟩ := openPisAtFvars_eq_instOpen m hst₁ hop'
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
            have := List.getElem?_eq_some_iff.mp hfvt
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
    simpa [show (v :: vs).length - 1 - (r + 1) = vs.length - 1 - r by simp; omega] using heB

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
    ∀ (e : KExpr) (acc : List KExpr),
      OpenFreeAt T vs j e → (∀ a ∈ acc, OpenFreeAt T vs j a) →
      ∀ a ∈ e.getAppArgsAux acc, OpenFreeAt T vs j a
  | .app f a, acc, h, hacc => by
    obtain ⟨hf, ha⟩ := h.app
    refine OpenFreeAt.getAppArgs f (a :: acc) hf (fun x hx => ?_)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact hacc x hx
  | .bvar _, _, _, hacc | .fvar _ _, _, _, hacc | .sort _, _, _, hacc
  | .const _ _, _, _, hacc | .lam _ _ _, _, _, hacc | .forallE _ _ _, _, _, hacc
  | .letE _ _ _ _, _, _, hacc | .lit _, _, _, hacc | .proj _ _ _, _, _, hacc => hacc

private theorem instOpen_bvar_lt :
    ∀ (vs : List KExpr) (j b : Nat),
      b < j → instOpen vs j (.bvar b) = .bvar b
  | [], _, _, _ => rfl
  | v :: vs, j, b, hlt => by
    have hne : b ≠ j + vs.length := by omega
    have hng : ¬ (b > j + vs.length) := by omega
    simp only [instOpen, Expr.instantiate1, if_neg hne, if_neg hng]
    exact instOpen_bvar_lt vs j b hlt

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
    have hidx_lt :
        k + fieldFvs.length + (fvsP'.length + 1) - 1 - (p + 1) <
          k + (fvsP'.length + fieldFvs.length) := by omega
    have hne : k + fieldFvs.length + (fvsP'.length + 1) - 1 - (p + 1) ≠
        k + (fvsP'.length + fieldFvs.length) := by omega
    have hng : ¬ (k + fieldFvs.length + (fvsP'.length + 1) - 1 - (p + 1) >
        k + (fvsP'.length + fieldFvs.length)) := by omega
    simp only [List.cons_append, List.length_cons, instOpen, List.length_append,
      Expr.instantiate1, if_neg hne, if_neg hng,
      show k + fieldFvs.length + (fvsP'.length + 1) - 1 - (p + 1) =
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
        b.1.hasLooseBVar (d + u) = false
  | 0, e, bs, body, d, hst, hb => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact ⟨by simpa using hb, fun _ _ h => nomatch h⟩
  | m + 1, .forallE dom bo mb, bs, body, d, hst, hb => by
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hb
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs', body'⟩, hst', heq⟩ := hst
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hbody, hbs'⟩ := hasLooseBVar_stripPis m (d + 1) hst' hb.2
    refine ⟨by rw [show d + (m + 1) = d + 1 + m by omega]; exact hbody, fun u b hu => ?_⟩
    cases u with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hu
      subst hu; simpa using hb.1
    | succ u' =>
      simp only [List.getElem?_cons_succ] at hu
      rw [show d + (u' + 1) = d + 1 + u' by omega]
      exact hbs' u' b hu

private theorem stripPis_split :
    ∀ (a b : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {body : KExpr},
      e.stripPis (a + b) = some (bs, body) →
      ∃ bs₁ rest bs₂,
        e.stripPis a = some (bs₁, rest) ∧
        rest.stripPis b = some (bs₂, body) ∧
        bs = bs₁ ++ bs₂ ∧ bs₁.length = a
  | 0, b, e, bs, body, hst => by
    rw [Nat.zero_add] at hst
    exact ⟨[], e, bs, rfl, hst, rfl, rfl⟩
  | a + 1, b, .forallE dom bo mb, bs, body, hst => by
    rw [show a + 1 + b = (a + b) + 1 by omega] at hst
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs', body'⟩, hst', heq⟩ := hst
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨bs₁, rest, bs₂, h1, h2, rfl, hlen⟩ := stripPis_split a b hst'
    exact ⟨(dom, mb) :: bs₁, rest, bs₂, by simp [Expr.stripPis, h1], h2, rfl, by simp [hlen]⟩

private theorem recPositivity_recursive_inv {T : KKey} {lps : List LevelParam}
    {nP nIdx o : Nat} {dom : KExpr}
    (h : Ix.Kernel.recPositivity T lps nP nIdx o dom 0 = .recursive) :
    Ix.Kernel.recFamOk T lps nP nIdx o dom = true := by
  unfold Ix.Kernel.recPositivity at h
  split at h
  · next d b _ =>
    split at h
    · exact nomatch h
    · -- k + 1 ≥ 1 can never return `.recursive`
      have hne : ∀ (e : KExpr) (k : Nat),
          Ix.Kernel.recPositivity T lps nP nIdx o e (k + 1) ≠ .recursive := by
        intro e
        induction e with
        | forallE d' b' _ _ ihb =>
          intro k
          unfold Ix.Kernel.recPositivity
          split
          · decide
          · exact ihb (k + 1)
        | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
        | lit _ | proj _ _ _ =>
          intro k
          unfold Ix.Kernel.recPositivity
          split
          · decide
          · split
            · split
              · split
                · simp
                · decide
              · decide
            · split <;> try split <;> decide
      exact absurd h (hne b 0)
  · split at h
    · exact nomatch h
    · split at h
      · split at h
        · split at h
          · assumption
          · exact nomatch h
        · exact nomatch h
      · split at h <;> try split at h <;> exact nomatch h

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
    have hleaf : ∀ (e : KExpr),
        (∀ d bo mb, e ≠ .forallE d bo mb) →
        Ix.Kernel.recPositivity T lps nP nIdx o e k = .reflexive →
        k ≠ 0 ∧ Ix.Kernel.recFamOk T lps nP nIdx (o + k) e = true := by
      intro e hnf hr
      cases e with
      | forallE d bo mb => exact absurd rfl (hnf d bo mb)
      | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
      | lit _ | proj _ _ _ =>
        unfold Ix.Kernel.recPositivity at hr
        split at hr
        · exact nomatch hr
        · split at hr
          · split at hr
            · split at hr
              · next hfam =>
                split at hr
                · exact nomatch hr
                · next hk0 =>
                  exact ⟨beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hk0), hfam⟩
              · exact nomatch hr
            · exact nomatch hr
          · split at hr <;> try split at hr <;> exact nomatch hr
    obtain ⟨hk, hfam⟩ := hleaf _ (fun _ _ _ heq => nomatch heq) h
    simp only [Expr.piBinders, List.length_nil, Nat.add_zero]
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
        rw [List.zipIdx_eq_map_add _ 1, List.map_map]
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
    (hres : (instOpen (fvsP ++ fieldFvs) k abody).constsResolve env₁ = true) :
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
  · rw [hargs, List.take_append_of_le_length (by omega), hfvsP_len, List.take_length]
  · rw [hargs, List.length_append, List.length_map, hfvsP_len, hdrop_len]
  · rw [hargs, ← hfvsP_len, List.drop_left]
    intro e he
    obtain ⟨a, ha_mem, rfl⟩ := List.mem_map.mp he
    have ha_noT : a.mentionsConst T = false := hdrop_noT a ha_mem
    have ha_of : OpenFreeAt T (fvsP ++ fieldFvs) k a :=
      (hof.getAppArgs abody [] (fun _ h => nomatch h)) a (List.mem_of_mem_drop ha_mem)
    have he_noT : (instOpen (fvsP ++ fieldFvs) k a).mentionsConst ci.name = false := by
      rw [hci, ha_of.mentionsConst_instOpen]; exact ha_noT
    have he_res₁ : (instOpen (fvsP ++ fieldFvs) k a).constsResolve env₁ = true :=
      (constsResolve_getApp hres).2 _ (by rw [hargs]; exact List.mem_append_right _ he)
    rw [henv₁, constsResolve_cons_of_not_mentionsConst he_noT] at he_res₁
    exact he_res₁

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
    have hleaf : ∀ (e : KExpr),
        (∀ d bo mb, e ≠ .forallE d bo mb) →
        Ix.Kernel.recPositivity T lps nP nIdx o e k = .ordinary →
        e.mentionsConst T = false := by
      intro e hnf hr
      cases e with
      | forallE d bo mb => exact absurd rfl (hnf d bo mb)
      | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
      | lit _ | proj _ _ _ =>
        unfold Ix.Kernel.recPositivity at hr
        split at hr
        · next hnoT => simpa using hnoT
        · split at hr
          · split at hr
            · split at hr
              · split at hr <;> exact nomatch hr
              · exact nomatch hr
            · exact nomatch hr
          · split at hr <;> try split at hr <;> exact nomatch hr
    exact hleaf _ (fun _ _ _ heq => nomatch heq) h

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
  let cty := cA.1.type
  let nF := cA.2
  let cbody := Expr.mkAppN (.const T (lps.map .param)) (Ix.Kernel.structPsAt nF nP ++ es)
  have hcbs_len : cbs.length = nP + nF := Expr.stripPis_length (nP + nF) hstrip
  have hcbody_args : cbody.getAppArgs = Ix.Kernel.structPsAt nF nP ++ es :=
    getAppArgs_mkAppN_const T (lps.map .param) _
  have hps_len : (Ix.Kernel.structPsAt nF nP : List KExpr).length = nP := by
    simp [Ix.Kernel.structPsAt]
  have hcbody_drop : cbody.getAppArgs.drop nP = es := by
    rw [hcbody_args, ← hps_len, List.drop_left]
  have hcbody_all_noT : (cbody.getAppArgs.drop nP).all (fun a => !a.mentionsConst T) = true := by
    rw [hcbody_drop, List.all_eq_true]
    intro a ha
    simp [hes_noT a ha]
  let ks : List Ix.Kernel.RecFieldKind :=
    (List.range nF).map fun i => Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1
  have hks_eq :
      ((List.range nF).map fun i =>
        match Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 with
        | .recursive => if Ix.Kernel.structUsedLater cty nP i then .unsupported else .recursive
        | .reflexive => if Ix.Kernel.structUsedLater cty nP i then .unsupported else .reflexive
        | k => k) = ks := by
    apply List.map_congr_left
    intro i hi
    have hi_lt : i < nF := List.mem_range.mp hi
    cases hkind : Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 with
    | ordinary | negative | unsupported => rfl
    | recursive => simp [hunused i hi_lt (Or.inl hkind)]
    | reflexive => simp [hunused i hi_lt (Or.inr hkind)]
  have hrck : Ix.Kernel.recCtorKinds T lps nP nIdx cA = some ks := by
    unfold Ix.Kernel.recCtorKinds
    rw [hstrip]
    simp only [hks_eq, hcbody_all_noT, ↓reduceIte]
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
  have hstrip_some : (cty.stripPis (nP + nF)).isSome = true := by rw [hstrip]; rfl
  obtain ⟨fvsAll_tmp, o_tmp, hopAll_tmp⟩ :=
    Ix.Kernel.Model.openPisAtFvars_of_stripPis_isSome (nP + nF) 0 hstrip_some
  -- `openPisAtFvars nF crest nP` must succeed because `openPisAtFvars (nP + nF) cty 0` succeeds
  have hopF_ex : ∃ xFvs xrest, Ix.Kernel.openPisAtFvars nF crest nP = some (xFvs, xrest) := by
    have hsplit_open :
        ∀ (a b : Nat) {e : KExpr} {d : Nat} {fvsA : List KExpr} {oA : KExpr}
          {fvs₁ : List KExpr} {r₁ : KExpr},
          Ix.Kernel.openPisAtFvars (a + b) e d = some (fvsA, oA) →
          Ix.Kernel.openPisAtFvars a e d = some (fvs₁, r₁) →
          ∃ fvs₂ o₂, Ix.Kernel.openPisAtFvars b r₁ (d + a) = some (fvs₂, o₂)
      | 0, b, e, d, fvsA, oA, fvs₁, r₁, hab, ha => by
        simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        rw [Nat.zero_add] at hab
        rw [Nat.add_zero]
        exact ⟨fvsA, oA, hab⟩
      | a + 1, b, .forallE dom bo mb, d, fvsA, oA, fvs₁, r₁, hab, ha => by
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
            obtain ⟨fvs₂, o₂, hb'⟩ := hsplit_open a b h1 h2
            rw [show d + (a + 1) = d + 1 + a by omega]
            exact ⟨fvs₂, o₂, hb'⟩
    simpa using hsplit_open nP nF hopAll_tmp hopP
  obtain ⟨xFvs, xrest, hopF⟩ := hopF_ex
  have hxFvs_len : xFvs.length = nF := Ix.Kernel.Model.openPisAtFvars_length nF hopF
  have hopAll : Ix.Kernel.openPisAtFvars (nP + nF) cty 0 = some (fvsP ++ xFvs, xrest) :=
    Ix.Kernel.Model.openPisAtFvars_add nP hopP (by simpa using hopF)
  obtain ⟨hxrest_eq, hall_fv, hpos_fv⟩ := openPisAtFvars_eq_instOpen (nP + nF) hstrip hopAll
  obtain ⟨hres_all, hxrest_res₁⟩ := openPisAtFvars_constsResolve (nP + nF) hres hopAll
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
        ∀ (t : Nat), nP + m < t → t < nP + nF →
          (cbs[t]'(by omega)).1.hasLooseBVar (t - 1 - (nP + m)) = false := by
    intro m hm hkind
    have hun := hunused m hm hkind
    obtain ⟨cbs_pre, rest_m, cbs_post, hst_m, hst_post, hcbs_app, hpre_len⟩ :=
      stripPis_split (nP + m + 1) (nP + nF - (nP + m + 1))
        (by rw [show nP + m + 1 + (nP + nF - (nP + m + 1)) = nP + nF by omega]; exact hstrip)
    have hrest_lb : rest_m.hasLooseBVar 0 = false := by
      unfold Ix.Kernel.structUsedLater at hun
      rw [hst_m, Expr.hasLooseBVarB_eq] at hun
      exact hun
    obtain ⟨hcbody_lb, hpost_lb⟩ := hasLooseBVar_stripPis _ 0 hst_post hrest_lb
    refine ⟨?_, fun t ht₁ ht₂ => ?_⟩
    · simpa [show 0 + (nP + nF - (nP + m + 1)) = nP + nF - 1 - (nP + m) by omega] using hcbody_lb
    · have hcbs_t : cbs[t]? = some (cbs[t]'(by omega)) := List.getElem?_eq_getElem (by omega)
      rw [hcbs_app, List.getElem?_append_right (by omega), hpre_len] at hcbs_t
      have h := hpost_lb (t - (nP + m + 1)) (cbs[t]'(by omega)) hcbs_t
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
          cases hkr : Ix.Kernel.recFieldKind T lps nP nIdx (r - nP) (cbs.getD r default).1 with
          | ordinary =>
            exact Or.inl ((iht r hr_lt (by omega)).2 (Or.inr hkr))
          | recursive =>
            right
            rw [htake_len, Nat.zero_add, ← hr_eq]
            rw [← hr_eq] at hkr
            exact (hunused_bvar (r - nP) hm_lt (Or.inl hkr)).2 t (by omega) ht
          | reflexive =>
            right
            rw [htake_len, Nat.zero_add, ← hr_eq]
            rw [← hr_eq] at hkr
            exact (hunused_bvar (r - nP) hm_lt (Or.inr hkr)).2 t (by omega) ht
          | negative =>
            rw [← hr_eq] at hkr
            exact absurd hkr (hpos (r - nP) hm_lt).1
          | unsupported =>
            rw [← hr_eq] at hkr
            exact absurd hkr (hpos (r - nP) hm_lt).2
      refine ⟨hof_t, fun hcase => ?_⟩
      have hfv_eq := hpos_fv t (cbs[t]'(by omega))
        ((fvsP ++ xFvs)[t]'(by rw [List.length_append, hfvsP_len, hxFvs_len]; exact ht))
        (List.getElem?_eq_getElem (by omega))
        (List.getElem?_eq_getElem (by rw [List.length_append, hfvsP_len, hxFvs_len]; exact ht))
      have hdom_noT : (cbs[t]'(by omega)).1.mentionsConst T = false := by
        have hgetD : cbs.getD t default = cbs[t]'(by omega) := List.getD_eq_getElem _ _ (by omega)
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
      cases hkr : Ix.Kernel.recFieldKind T lps nP nIdx (r - nP) (cbs.getD r default).1 with
      | ordinary => exact Or.inl ((hslot r hr_lt).2 (Or.inr hkr))
      | recursive =>
        right
        rw [hall_len, Nat.zero_add, ← hr_eq]
        rw [← hr_eq] at hkr
        exact (hunused_bvar (r - nP) hm_lt (Or.inl hkr)).1
      | reflexive =>
        right
        rw [hall_len, Nat.zero_add, ← hr_eq]
        rw [← hr_eq] at hkr
        exact (hunused_bvar (r - nP) hm_lt (Or.inr hkr)).1
      | negative =>
        rw [← hr_eq] at hkr
        exact absurd hkr (hpos (r - nP) hm_lt).1
      | unsupported =>
        rw [← hr_eq] at hkr
        exact absurd hkr (hpos (r - nP) hm_lt).2
  -- Now prove `nativeOpenedOk`
  unfold Ix.Kernel.nativeOpenedOk
  rw [hopP, hopF]
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- Residual index arguments resolve in `env`
    have hcbody_fam : Ix.Kernel.recFamOk T lps nP nIdx (xFvs.length + 0) cbody = true := by
      simp only [Ix.Kernel.recFamOk, Nat.add_zero, hxFvs_len, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hcbody_all_noT⟩
      · show (Expr.mkAppN (.const T (lps.map .param)) _).getAppFn = _
        rw [getAppFn_mkAppN]; rfl
      · rw [hcbody_args, List.length_append, hps_len, hes_len]
      · rw [hcbody_args, List.take_append_of_le_length (by omega), hps_len, List.take_length]
    rw [hxrest_eq] at hxrest_res₁ ⊢
    obtain ⟨_, _, _, hdrop_res⟩ :=
      recFamOk_opened henv₁ hci hfvsP_len hfvsP_fv hcbody_fam hof_cbody hxrest_res₁
    rw [List.all_eq_true]
    exact hdrop_res
  · -- Each field `i < nF`
    rw [List.all_eq_true]
    intro i hi_mem
    have hi : i < nF := List.mem_range.mp hi_mem
    have hxi_some : xFvs[i]? = some (xFvs[i]'hi) := List.getElem?_eq_getElem hi
    have hks_getD : ks.getD i .ordinary =
        Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 := by
      simp [ks, hi]
    rw [hxi_some, hks_getD]
    have htake_eq : (fvsP ++ xFvs).take (nP + i) = fvsP ++ xFvs.take i := by
      rw [List.take_append,
        List.take_of_length_le (by omega),
        show nP + i - fvsP.length = i by omega]
    have hxi_eq :
        xFvs[i]'hi =
          .fvar (nP + i) (instOpen (fvsP ++ xFvs.take i) 0 (cbs[nP + i]'(by omega)).1) := by
      have h := hpos_fv (nP + i) (cbs[nP + i]'(by omega)) (xFvs[i]'hi)
        (List.getElem?_eq_getElem (by omega))
        (by rw [List.getElem?_append_right (by omega),
          show nP + i - fvsP.length = i by omega, List.getElem?_eq_getElem hi])
      rwa [Nat.zero_add, htake_eq] at h
    have hxi_fvarTypeD :
        (xFvs[i]'hi).fvarTypeD = instOpen (fvsP ++ xFvs.take i) 0 (cbs[nP + i]'(by omega)).1 := by
      rw [hxi_eq]; rfl
    have hgetD_i : cbs.getD (nP + i) default = cbs[nP + i]'(by omega) :=
      List.getD_eq_getElem _ _ (by omega)
    have hof_i : OpenFreeAt T (fvsP ++ xFvs.take i) 0 (cbs[nP + i]'(by omega)).1 := by
      rw [← htake_eq]
      exact (hslot (nP + i) (by omega)).1
    have hxi_res₁ : (xFvs[i]'hi).fvarTypeD.constsResolve env₁ = true :=
      hres_all (xFvs[i]'hi) (List.mem_append_right _ (List.getElem_mem hi))
    -- Unused helper for `.recursive` and `.reflexive`
    have hleaf_unused :
        (Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 = .recursive ∨
         Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 = .reflexive) →
        (!(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
          !xrest.mentionsFvar (nP + i)) = true := by
      intro hk_rec
      have hun := hunused i hi hk_rec
      have hsome_st : (cty.stripPis (nP + i + 1)).isSome = true :=
        Ix.Kernel.stripPis_isSome_of_le (by omega) hstrip_some
      obtain ⟨⟨bs_u, rest_u⟩, hst_u⟩ := Option.isSome_iff_exists.mp hsome_st
      have hrest_u : rest_u.hasLooseBVar 0 = false := by
        unfold Ix.Kernel.structUsedLater at hun
        rw [hst_u, Expr.hasLooseBVarB_eq] at hun
        exact hun
      obtain ⟨hleaves_k, hleaves_o⟩ := Ix.Kernel.Model.openPisAtFvars_leaf_free
        (nP + nF) (nP + i) hopAll (by omega) hst_u hrest_u
        (fun l hl => by
          rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv] at hl
          exact absurd hl List.not_mem_nil)
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨?_, not_mentionsFvar_of_leaf_free hleaves_o⟩
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
      refine not_mentionsFvar_of_leaf_free (fun l hl => ?_)
      have hl' : l ∈ ((xFvs.drop (i + 1))[u]).fvarLeaves := by
        rw [hq_eq] at hl ⊢
        exact List.mem_cons_of_mem _ hl
      exact hleaves_k (nP + (i + 1 + u)) (by omega) _ hy_at l hl'
    cases hkind : Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 with
    | ordinary =>
      have hdom_noT := mentionsConst_false_of_recFieldKind_ordinary hkind
      rw [hgetD_i] at hdom_noT
      have hxi_noT : (xFvs[i]'hi).fvarTypeD.mentionsConst ci.name = false := by
        rw [hci, hxi_fvarTypeD, hof_i.mentionsConst_instOpen]
        exact hdom_noT
      rw [henv₁, constsResolve_cons_of_not_mentionsConst hxi_noT] at hxi_res₁
      exact hxi_res₁
    | recursive =>
      have hkind' := hkind
      unfold Ix.Kernel.recFieldKind at hkind'
      have hmc : (cbs.getD (nP + i) default).1.mentionsConst T = true := by
        cases h : (cbs.getD (nP + i) default).1.mentionsConst T
        · rw [h] at hkind'; exact nomatch hkind'
        · rfl
      rw [if_pos hmc] at hkind'
      have hfam := recPositivity_recursive_inv hkind'
      rw [hgetD_i] at hfam
      have htake_i_len : (xFvs.take i).length = i := by
        rw [List.length_take, hxFvs_len]; omega
      have hfam' : Ix.Kernel.recFamOk T lps nP nIdx ((xFvs.take i).length + 0)
          (cbs[nP + i]'(by omega)).1 = true := by
        simpa [htake_i_len] using hfam
      rw [hxi_fvarTypeD] at hxi_res₁ ⊢
      obtain ⟨hfn', htake', hlen', hdrop'⟩ :=
        recFamOk_opened henv₁ hci hfvsP_len hfvsP_fv hfam' hof_i hxi_res₁
      have hun_ok := hleaf_unused (Or.inl hkind)
      simp only [Bool.and_eq_true] at hun_ok
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
      exact ⟨⟨⟨⟨⟨hfn', htake'⟩, hlen'⟩, hdrop'⟩, hun_ok.1⟩, hun_ok.2⟩
    | reflexive =>
      have hkind' := hkind
      unfold Ix.Kernel.recFieldKind at hkind'
      have hmc : (cbs.getD (nP + i) default).1.mentionsConst T = true := by
        cases h : (cbs.getD (nP + i) default).1.mentionsConst T
        · rw [h] at hkind'; exact nomatch hkind'
        · rfl
      rw [if_pos hmc] at hkind'
      rw [hgetD_i] at hkind'
      have hrefl := recPositivity_reflexive_inv (cbs[nP + i]'(by omega)).1 0 hkind'
      cases hpb : (cbs[nP + i]'(by omega)).1.piBinders with
      | mk abs abody =>
        simp only [hpb, Nat.zero_add] at hrefl
        obtain ⟨habs_ne, habs_noT, _, hfam⟩ := hrefl
        have habody_fn : abody.getAppFn = .const T (lps.map .param) := by
          simp only [Ix.Kernel.recFamOk, Bool.and_eq_true, beq_iff_eq] at hfam
          exact hfam.1.1.1
        obtain ⟨hpb_inst, hst_inst⟩ :=
          piBinders_instOpen_of_const_head (cbs[nP + i]'(by omega)).1
            (fvsP ++ xFvs.take i) 0 (by rw [hpb]; exact habody_fn)
        simp only [hpb, Nat.zero_add] at hpb_inst hst_inst
        let m := abs.length
        have hm_eq : ((xFvs[i]'hi).fvarTypeD.piBinders).1.length = m := by
          rw [hxi_fvarTypeD, hpb_inst, List.length_map, List.length_zipIdx]
        rw [hm_eq]
        have hst_xi :
            (xFvs[i]'hi).fvarTypeD.stripPis m =
              some ((abs.zipIdx).map (fun ⟨b, r⟩ =>
                  (instOpen (fvsP ++ xFvs.take i) r b.1, b.2)),
                instOpen (fvsP ++ xFvs.take i) m abody) := by
          rw [hxi_fvarTypeD]; exact hst_inst
        obtain ⟨afvs, body', hopA⟩ :=
          Ix.Kernel.Model.openPisAtFvars_of_stripPis_isSome m (nP + i)
            (by rw [hst_xi]; rfl)
        rw [hopA]
        have hafvs_len : afvs.length = m := Ix.Kernel.Model.openPisAtFvars_length m hopA
        obtain ⟨hbody'_eq, hafvs_fv, hafvs_pos⟩ :=
          openPisAtFvars_eq_instOpen m hst_xi hopA
        obtain ⟨hafvs_res₁, hbody'_res₁⟩ :=
          openPisAtFvars_constsResolve m hxi_res₁ hopA
        obtain ⟨hof_abody, hof_abs⟩ := openFree_piBinders (cbs[nP + i]'(by omega)).1 0 hof_i
        simp only [hpb, Nat.zero_add] at hof_abody hof_abs
        -- Every `a ∈ afvs` has `mentionsConst T = false`
        have hafvs_noT : ∀ (r : Nat) (hr : r < m),
            (afvs[r]'(by omega)).mentionsConst T = false := by
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
            have ha_eq := hafvs_pos r _ (afvs[r]'(by omega)) hzip_r
              (List.getElem?_eq_getElem (by omega))
            have htake_r_len : (afvs.take r).length = r := by
              rw [List.length_take, hafvs_len]; omega
            have hcomb :
                instOpen (afvs.take r) 0 (instOpen (fvsP ++ xFvs.take i) r (abs[r]'hr).1) =
                  instOpen ((fvsP ++ xFvs.take i) ++ afvs.take r) 0 (abs[r]'hr).1 := by
              rw [instOpen_append, Nat.zero_add, htake_r_len]
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
            have := hafvs_noT r (by omega)
            rw [hq, Expr.mentionsConst] at this
            rw [hq, Expr.fvarTypeD, hci]
            exact this
          have hr₁ := hafvs_res₁ _ ha
          rw [henv₁, constsResolve_cons_of_not_mentionsConst hnoT] at hr₁
          exact hr₁
        have hbody'_comb :
            body' = instOpen (fvsP ++ (xFvs.take i ++ afvs)) 0 abody := by
          rw [hbody'_eq, ← List.append_assoc, instOpen_append, Nat.zero_add, hafvs_len]
        have hof_body' :
            OpenFreeAt T (fvsP ++ (xFvs.take i ++ afvs)) 0 abody := by
          rw [← List.append_assoc]
          refine openFreeAt_append_extra afvs (fun w hw => ?_) ?_
          · obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hw
            obtain ⟨q, ty, hq⟩ := hafvs_fv _ hw
            exact ⟨fun k => by rw [hq]; rfl, hafvs_noT r (by omega)⟩
          · rw [hafvs_len]; exact hof_abody
        have htake_i_len : (xFvs.take i).length = i := by
          rw [List.length_take, hxFvs_len]; omega
        have hfam' :
            Ix.Kernel.recFamOk T lps nP nIdx ((xFvs.take i ++ afvs).length + 0) abody = true := by
          simpa [List.length_append, htake_i_len, hafvs_len] using hfam
        rw [hbody'_comb] at hbody'_res₁ ⊢
        obtain ⟨hfn', htake', hlen', hdrop'⟩ :=
          recFamOk_opened henv₁ hci hfvsP_len hfvsP_fv hfam' hof_body' hbody'_res₁
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
    refine ⟨?_, by simp [hks_neg, hneg], by simp [hks_uns, huns]⟩
    show (Ix.Kernel.recCtorKinds T lps nP nIdx cA >>= fun hd =>
      (ctorsA.mapM (Ix.Kernel.recCtorKinds T lps nP nIdx)).map (hd :: ·)) = some (ks :: kinds)
    rw [hrck, Option.bind_some, hmap]
    rfl

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
    have hrel : ∀ {xs : List (KConstantVal × Nat)} {ys : List (List Ix.Kernel.RecFieldKind)},
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
        hrel htl u (Nat.lt_of_succ_lt_succ hu₁) (Nat.lt_of_succ_lt_succ hu₂)
    obtain ⟨hklen, hopen⟩ := hrel hall j hjc hj
    simp [hklen, hopen]

/-! ## `checkStructProjTable`, `checkNativeTable`, and `InstallStep` assembly -/

private def projBodyWF (env : Ix.Kernel.Env .anon) (lps : List LevelParam) (k : Nat)
    (e : KExpr) : Prop :=
  e.hasFvar = false ∧
  e.allLevelParamsDefined lps = true ∧
  e.constsResolve env = true ∧
  e.looseBVarsBounded k = true

private theorem lbb_mono {k₁ k₂ : Nat} (hle : k₁ ≤ k₂) :
    ∀ {e : KExpr}, e.looseBVarsBounded k₁ = true → e.looseBVarsBounded k₂ = true
  | .bvar i, h => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h ⊢; omega
  | .fvar _ ty, h => lbb_mono hle h
  | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨lbb_mono hle h.1, lbb_mono hle h.2⟩
  | .lam t b _, h | .forallE t b _, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨lbb_mono hle h.1, lbb_mono (by omega) h.2⟩
  | .letE t v b _, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨lbb_mono hle h.1.1, lbb_mono hle h.1.2⟩, lbb_mono (by omega) h.2⟩
  | .proj _ _ e, h => lbb_mono hle h

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
  | .sort _, _, _, _ => ⟨rfl, rfl, rfl, rfl⟩
  | .const _ _, _, _, ⟨hf, hl, hr, _⟩ => ⟨hf, hl, hr, rfl⟩
  | .lit _, _, _, _ => ⟨rfl, rfl, rfl, rfl⟩
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
    obtain ⟨hf₁, hl₁, hr₁, hb₁⟩ := liftLooseBVars_wf d t k s ⟨hf.1, hl.1, hr.1, hb.1⟩
    have hb_s : b.looseBVarsBounded (k + (s + 1)) = true := by
      rwa [show k + (s + 1) = k + s + 1 by omega]
    obtain ⟨hf₂, hl₂, hr₂, hb₂⟩ := liftLooseBVars_wf d b k (s + 1) ⟨hf.2, hl.2, hr.2, hb_s⟩
    rw [show k + d + (s + 1) = k + d + s + 1 by omega] at hb₂
    exact ⟨by simp [Expr.liftLooseBVars, Expr.hasFvar, hf₁, hf₂],
      by simp [Expr.liftLooseBVars, Expr.allLevelParamsDefined, hl₁, hl₂],
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
      rwa [show k + (s + 1) = k + s + 1 by omega]
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
  | .sort _, _, _ => ⟨rfl, rfl, rfl, rfl⟩
  | .const _ _, _, ⟨hf, hl, hr, _⟩ => ⟨hf, hl, hr, rfl⟩
  | .lit _, _, _ => ⟨rfl, rfl, rfl, rfl⟩
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
    obtain ⟨hf₁, hl₁, hr₁, hb₁⟩ := instantiate1Lift_wf hv t d ⟨hf.1, hl.1, hr.1, hb.1⟩
    have hb' : b.looseBVarsBounded (k + 1 + (d + 1)) = true := by
      rwa [show k + 1 + (d + 1) = k + 1 + d + 1 by omega]
    obtain ⟨hf₂, hl₂, hr₂, hb₂⟩ := instantiate1Lift_wf hv b (d + 1) ⟨hf.2, hl.2, hr.2, hb'⟩
    rw [show k + (d + 1) = k + d + 1 by omega] at hb₂
    exact ⟨by simp [Expr.instantiate1Lift, Expr.hasFvar, hf₁, hf₂],
      by simp [Expr.instantiate1Lift, Expr.allLevelParamsDefined, hl₁, hl₂],
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
      rwa [show k + 1 + (d + 1) = k + 1 + d + 1 by omega]
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
          ⟨hf.2, hl.2, hr.2, by simpa using hb.2⟩
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
        simpa using instantiate1Lift_wf harg_wf bo 0 ⟨hf.2, hl.2, hr.2, by simpa using hb.2⟩
      obtain ⟨bs', hgo, hlen', hall'⟩ :=
        structProjBodiesGo_wf hT m (i + 1) (by rw [hst₁]; rfl) hbo_wf
      refine ⟨fdom :: bs', by simp [Ix.Kernel.structProjBodiesGo, hgo], by simp [hlen'], ?_⟩
      intro b hb_mem
      rcases List.mem_cons.mp hb_mem with rfl | hb_mem
      · exact ⟨hf.1, hl.1, hr.1, hb.1⟩
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
    rw [Array.all_toArray, List.all_eq_true]
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
  rw [if_pos hall_arr, if_pos hfn_all, if_pos htbl_none]
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
    have hex : ∀ {xs ys : List KConstantInfo},
        List.Forall₂ IxVM.Consistency.StoredAs xs ys →
        ∀ y ∈ ys, ∃ x ∈ xs, IxVM.Consistency.StoredAs x y
      | _, _, .nil, _, hy => nomatch hy
      | x :: _, _ :: _, .cons hs _, _, .head _ => ⟨x, List.mem_cons_self, hs⟩
      | _ :: _, _ :: _, .cons _ htl, y, .tail _ hy => by
        obtain ⟨x, hx, hs⟩ := hex htl y hy
        exact ⟨x, List.mem_cons_of_mem _ hx, hs⟩
    obtain ⟨ci, hciA, hs⟩ := hex hstored ci₀ hci₀
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
          k ∉ xs.map (·.name) ∧ env.find? k = none
      | [], k, hf => ⟨List.not_mem_nil, hf⟩
      | x :: xs, k, hf => by
        simp only [Ix.Kernel.Env.find?, List.cons_append, List.find?_cons] at hf
        cases hxk : (x.name == k)
        · rw [hxk] at hf
          obtain ⟨hnm, he⟩ := hfind_split xs k hf
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



