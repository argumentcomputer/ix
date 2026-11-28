import IxVMRefinement.FamilyAlias.ProjCoherence
import IxCK.Kernel.Model.IndFrame
import IxCK.Kernel.Model.Inductives.StructEntryKit2
import IxCK.Kernel.Model.Inductives.FixStageRec
import IxCK.Kernel.Model.Rules.RedSoundKit
import IxCK.Kernel.Model.Open.StoredFacts

/-! # Evaluation and coherence proofs for modeled structure projections

Builds on `ProjCoherence` to prove the set-model coherence theorem linking a checked modeled
structure projection definition `proj_i` to its level- and parameter-independent graph chain:

* **Section 7**: `denoteMeta` invariance under `FvarTypeIrrel` and `ExprSemEq`, `stripLams` /
  `stripPis` denotation lemmas, `AppChainOk`, `mkLamsAV_appChainOk_pos`, `teleFitPA_of_mkPisAV_*`,
  and `consList` bvar evaluation;
* **Section 8**: `auxRec_fire`, firing a native auxiliary recursor `aux.rec` on pure value spines
  via `mp.rec_rules`, `RecRhsPwNoModel`, and `aux_fibre_disjoint`. -/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Refinement.Core
open IxVM.Consistency (lastBinderDom)
open IxVM.Refinement.Decl (ExprSemEq)
open IxVM.Refinement.KernelLevels (substLevel)
open Ix.Kernel (Expr Level ConstantInfo ConstantVal RecRule LevelParam BinderMeta Key Env SetTheory)
open Ix.Kernel.Semantics
open Ix.Kernel.SetTheory
open Ix.Kernel.SetTheory.Tower
open Ix.Kernel.SetModel
open Ix.Kernel.Model

/-! ## Section 7: `denoteMeta`, `ExprSemEq`, `AppChainOk`, `mkLamsAV`, and `TeleFitPA` -/

theorem denoteMetaSpine_length_eq {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {φ : LevelParam → Nat} {d : Nat} :
    ∀ {as : List KExpr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env φ d as vs → as.length = vs.length
  | _, _, .nil => rfl
  | _, _, .cons _ htl => congrArg Nat.succ (denoteMetaSpine_length_eq htl)

theorem denoteMetaSpine_getElem {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {φ : LevelParam → Nat} {d : Nat}
    {as : List KExpr} {vs : List AnnotTerm} (hsp : DenoteMetaSpine acval env φ d as vs)
    {i : Nat} (hi : i < as.length) :
    denoteMeta acval env φ d as[i] = some (vs[i]'(denoteMetaSpine_length_eq hsp ▸ hi)) := by
  obtain ⟨v, hv, hden⟩ := DenoteMetaSpine.getElem? hsp (List.getElem?_eq_getElem hi)
  rw [List.getElem?_eq_getElem (denoteMetaSpine_length_eq hsp ▸ hi)] at hv
  rw [Option.some.inj hv]; exact hden

theorem forall₂_getElem {α β : Type*} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      ∀ i (h1 : i < xs.length) (h2 : i < ys.length), R xs[i] ys[i]
  | _ :: _, _ :: _, .cons h _, 0, _, _ => h
  | _ :: _, _ :: _, .cons _ htl, i + 1, h1, h2 =>
      forall₂_getElem htl i (by simpa using h1) (by simpa using h2)

theorem substFn_not_mem (ψ : LevelParam → Nat) :
    ∀ (ks : List LevelParam) (us : List KLevel) {p : LevelParam},
      p ∉ ks → Level.substFn ψ ks us p = ψ p
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => by simp [Level.substFn]
  | k :: ks, _ :: us, p, h => by
    have hne : k ≠ p := fun he => h (he ▸ List.mem_cons_self)
    simp [Level.substFn, hne, substFn_not_mem ψ ks us (fun hm => h (List.mem_cons_of_mem _ hm))]

theorem denoteMeta_fvarTypeIrrel {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {φ : LevelParam → Nat}
    {d : Nat} {e₁ e₂ : KExpr} (h : FvarTypeIrrel e₁ e₂) :
    denoteMeta acval env φ d e₁ = denoteMeta acval env φ d e₂ := by
  match h with
  | .bvar _ => rfl
  | .fvar _ _ _ => simp only [denoteMeta]
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app hf ha =>
    simp only [denoteMeta, denoteMeta_fvarTypeIrrel hf, denoteMeta_fvarTypeIrrel ha]
  | .lam ht hb =>
    simp only [denoteMeta]
    rw [denoteMeta_fvarTypeIrrel ht]
    rw [denoteMeta_fvarTypeIrrel (hb.instantiate1 (.fvar d _ _) 0)]
  | .forallE ht hb =>
    simp only [denoteMeta]
    rw [denoteMeta_fvarTypeIrrel ht]
    rw [denoteMeta_fvarTypeIrrel (hb.instantiate1 (.fvar d _ _) 0)]
  | .letE _ _ _ => simp only [denoteMeta]
  | .lit _ => rfl
  | .proj _ _ he =>
    simp only [denoteMeta, denoteMeta_fvarTypeIrrel he]
termination_by e₁.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; done)
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB])

theorem exprSemEq_instantiate1 {e₁ e₂ v₁ v₂ : KExpr}
    (he : ExprSemEq e₁ e₂) (hv : ExprSemEq v₁ v₂) :
    ∀ c : Nat, ExprSemEq (e₁.instantiate1 v₁ c) (e₂.instantiate1 v₂ c) := by
  induction he with
  | bvar i =>
    intro c
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> exact .bvar _
  | fvar ht => intro c; exact .fvar (ht)
  | sort hu => intro c; exact .sort hu
  | const hus => intro c; exact .const hus
  | lit l => intro c; exact .lit l
  | app _ _ ihf iha => intro c; exact .app (ihf c) (iha c)
  | lam hpw _ _ iht ihb => intro c; exact .lam hpw (iht c) (ihb (c + 1))
  | forallE hpw _ _ iht ihb => intro c; exact .forallE hpw (iht c) (ihb (c + 1))
  | letE _ _ _ iht ihv ihb => intro c; exact .letE (iht c) (ihv c) (ihb (c + 1))
  | proj _ ihe => intro c; exact .proj (ihe c)

theorem exprSemEq_openDummiesP {e₁ e₂ : KExpr} (he : ExprSemEq e₁ e₂) :
    ∀ (n d c : Nat), ExprSemEq (openDummiesP n d c e₁) (openDummiesP n d c e₂)
  | 0, _, _ => he
  | n + 1, d, c =>
    exprSemEq_openDummiesP (exprSemEq_instantiate1 he (.fvar (.sort (Core.LvEq.refl _))) (c + n))
      n (d + 1) c

theorem denoteMeta_exprSemEq {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {φ : LevelParam → Nat}
    {d : Nat} {e₁ e₂ : KExpr} (h : ExprSemEq e₁ e₂) :
    denoteMeta acval env φ d e₁ = denoteMeta acval env φ d e₂ := by
  match h with
  | .bvar _ => rfl
  | .fvar _ => simp only [denoteMeta]
  | .sort hu =>
    simp only [denoteMeta]
    exact congrArg (fun k => some (AnnotTerm.sort k)) (hu φ)
  | .const (n := n) (us := us) (us' := us') hus =>
    have hlen : us.length = us'.length := by
      have hgo : ∀ (xs ys : List KLevel), Level.EvalEqList φ xs ys → xs.length = ys.length := by
        intro xs
        induction xs with
        | nil => intro ys h; cases ys with | nil => rfl | cons _ _ => exact h.elim
        | cons _ xs ih =>
          intro ys h; cases ys with | nil => exact h.elim | cons _ ys => exact congrArg Nat.succ (ih ys h.2)
      exact hgo us us' (hus φ)
    simp only [denoteMeta]
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      simp only [hlen]
      split
      · rw [substFn_eq_of_lvEqList hus φ]
      · rfl
  | .lit _ => rfl
  | .app hf ha =>
    simp only [denoteMeta, denoteMeta_exprSemEq hf, denoteMeta_exprSemEq ha]
  | .lam hpw ht hb =>
    simp only [denoteMeta, hpw]
    rw [denoteMeta_exprSemEq ht]
    rw [denoteMeta_exprSemEq (exprSemEq_instantiate1 hb (.fvar ht) 0)]
  | .forallE hpw ht hb =>
    simp only [denoteMeta, hpw]
    rw [denoteMeta_exprSemEq ht]
    rw [denoteMeta_exprSemEq (exprSemEq_instantiate1 hb (.fvar ht) 0)]
  | .letE _ _ _ => simp only [denoteMeta]
  | .proj he =>
    simp only [denoteMeta, denoteMeta_exprSemEq he]
termination_by e₁.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; done)
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB])

theorem stripLams_instantiate1 (v : KExpr) :
    ∀ (n c : Nat) {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.stripLams n = some (bs, rem) →
      ∃ bs', (e.instantiate1 v c).stripLams n = some (bs', rem.instantiate1 v (c + n)) ∧
        bs'.map (·.2.pw) = bs.map (·.2.pw)
  | 0, c, e, rem, bs, h => by
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl⟩
  | n + 1, c, .lam ty b m, rem, bs, h => by
    simp only [Expr.stripLams, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, rem₀⟩, hsb, hpair⟩ := h
    injection hpair with hbs hrem
    subst hbs hrem
    obtain ⟨bs', hbs', hpw⟩ := stripLams_instantiate1 v n (c + 1) hsb
    refine ⟨(ty.instantiate1 v c, m) :: bs', ?_, ?_⟩
    · simp only [Expr.instantiate1, Expr.stripLams, hbs', Option.map_some]
      rw [show c + 1 + n = c + (n + 1) by omega]
    · simp [hpw]
  | _ + 1, _, .bvar _, _, _, h | _ + 1, _, .fvar _ _, _, _, h | _ + 1, _, .sort _, _, _, h
  | _ + 1, _, .const _ _, _, _, h | _ + 1, _, .app _ _, _, _, h | _ + 1, _, .forallE _ _ _, _, _, h
  | _ + 1, _, .letE _ _ _ _, _, _, h | _ + 1, _, .lit _, _, _, h
  | _ + 1, _, .proj _ _ _, _, _, h => nomatch h

theorem stripPis_instantiate1_pw (v : KExpr) :
    ∀ (n c : Nat) {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.stripPis n = some (bs, rem) →
      ∃ bs', (e.instantiate1 v c).stripPis n = some (bs', rem.instantiate1 v (c + n)) ∧
        bs'.map (·.2.pw) = bs.map (·.2.pw)
  | 0, c, e, rem, bs, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl⟩
  | n + 1, c, .forallE ty b m, rem, bs, h => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, rem₀⟩, hsb, hpair⟩ := h
    injection hpair with hbs hrem
    subst hbs hrem
    obtain ⟨bs', hbs', hpw⟩ := stripPis_instantiate1_pw v n (c + 1) hsb
    refine ⟨(ty.instantiate1 v c, m) :: bs', ?_, ?_⟩
    · simp only [Expr.instantiate1, Expr.stripPis, hbs', Option.map_some]
      rw [show c + 1 + n = c + (n + 1) by omega]
    · simp [hpw]
  | _ + 1, _, .bvar _, _, _, h | _ + 1, _, .fvar _ _, _, _, h | _ + 1, _, .sort _, _, _, h
  | _ + 1, _, .const _ _, _, _, h | _ + 1, _, .app _ _, _, _, h | _ + 1, _, .lam _ _ _, _, _, h
  | _ + 1, _, .letE _ _ _ _, _, _, h | _ + 1, _, .lit _, _, _, h
  | _ + 1, _, .proj _ _ _, _, _, h => nomatch h

theorem stripLams_length :
    ∀ {n : Nat} {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.stripLams n = some (bs, rem) → bs.length = n
  | 0, _, _, _, h => by
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | n + 1, .lam _ b _, _, _, h => by
    simp only [Expr.stripLams, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, _⟩, hsb, hpair⟩ := h
    injection hpair with hbs _
    rw [← hbs, List.length_cons, stripLams_length hsb]
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .forallE _ _ _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, h | _ + 1, .lit _, _, _, h
  | _ + 1, .proj _ _ _, _, _, h => nomatch h

theorem stripPis_length_p :
    ∀ {n : Nat} {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.stripPis n = some (bs, rem) → bs.length = n
  | 0, _, _, _, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | n + 1, .forallE _ b _, _, _, h => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, _⟩, hsb, hpair⟩ := h
    injection hpair with hbs _
    rw [← hbs, List.length_cons, stripPis_length_p hsb]
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, h | _ + 1, .lit _, _, _, h
  | _ + 1, .proj _ _ _, _, _, h => nomatch h

theorem denoteMeta_stripLams {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {φ : LevelParam → Nat} :
    ∀ (n d : Nat) {e body : KExpr} {bs : List (KExpr × BinderMeta)} {fa : AnnotTerm},
      e.stripLams n = some (bs, body) →
      denoteMeta acval env φ d e = some fa →
      ∃ (lds : List (Nat × AnnotTerm)) (bodyA : AnnotTerm),
        fa = mkLamsAV lds bodyA ∧
        lds.length = n ∧
        lds.map Prod.fst = bs.map (fun bm => pwBit φ bm.2.pw) ∧
        denoteMeta acval env φ (d + n) (openDummiesP n d 0 body) = some bodyA
  | 0, d, e, body, bs, fa, hst, hden => by
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact ⟨[], fa, rfl, rfl, rfl, by simpa [openDummiesP] using hden⟩
  | n + 1, d, .lam ty b mb, body, bs, fa, hst, hden => by
    simp only [Expr.stripLams, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs₀, body₀⟩, hsb, hpair⟩ := hst
    injection hpair with hbs hbd
    subst hbs hbd
    obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_lam_inv hden
    have hirr : FvarTypeIrrel (b.instantiate1 (.fvar d ty) 0)
        (b.instantiate1 (.fvar d (.sort .zero)) 0) :=
      (FvarTypeIrrel.refl b).instantiate1 (.fvar d ty (.sort .zero)) 0
    rw [denoteMeta_fvarTypeIrrel hirr] at hba
    obtain ⟨bs', hbs', hpw'⟩ := stripLams_instantiate1 (.fvar d (.sort .zero)) n 0 hsb
    simp only [Nat.zero_add] at hbs'
    obtain ⟨lds', bodyA, rfl, hlen', hbits', hbodyA⟩ := denoteMeta_stripLams n (d + 1) hbs' hba
    refine ⟨(pwBit φ mb.pw, ta) :: lds', bodyA, rfl, by simp [hlen'], ?_, ?_⟩
    · simp only [List.map_cons, List.cons.injEq, true_and]
      have hcomp : bs'.map (fun bm => pwBit φ bm.2.pw) = bs₀.map (fun bm => pwBit φ bm.2.pw) := by
        simpa [List.map_map, Function.comp_def] using congrArg (List.map (pwBit φ)) hpw'
      exact hbits'.trans hcomp
    · simp only [openDummiesP, Nat.zero_add]
      rwa [show d + 1 + n = d + (n + 1) by omega] at hbodyA
  | _ + 1, _, .bvar _, _, _, _, hst, _ | _ + 1, _, .fvar _ _, _, _, _, hst, _
  | _ + 1, _, .sort _, _, _, _, hst, _ | _ + 1, _, .const _ _, _, _, _, hst, _
  | _ + 1, _, .app _ _, _, _, _, hst, _ | _ + 1, _, .forallE _ _ _, _, _, _, hst, _
  | _ + 1, _, .letE _ _ _ _, _, _, _, hst, _ | _ + 1, _, .lit _, _, _, _, hst, _
  | _ + 1, _, .proj _ _ _, _, _, _, hst, _ => nomatch hst

theorem denoteMeta_stripPis {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {φ : LevelParam → Nat} :
    ∀ (n d : Nat) {e body : KExpr} {bs : List (KExpr × BinderMeta)} {fa : AnnotTerm},
      e.stripPis n = some (bs, body) →
      denoteMeta acval env φ d e = some fa →
      ∃ (ds : List (Nat × Nat × AnnotTerm)) (bodyA : AnnotTerm),
        fa = mkPisAV ds bodyA ∧
        ds.length = n ∧
        ds.map (fun d => d.2.1) = bs.map (fun bm => pwBit φ bm.2.pw) ∧
        denoteMeta acval env φ (d + n) (openDummiesP n d 0 body) = some bodyA
  | 0, d, e, body, bs, fa, hst, hden => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact ⟨[], fa, rfl, rfl, rfl, by simpa [openDummiesP] using hden⟩
  | n + 1, d, .forallE ty b mb, body, bs, fa, hst, hden => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs₀, body₀⟩, hsb, hpair⟩ := hst
    injection hpair with hbs hbd
    subst hbs hbd
    obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv hden
    have hirr : FvarTypeIrrel (b.instantiate1 (.fvar d ty) 0)
        (b.instantiate1 (.fvar d (.sort .zero)) 0) :=
      (FvarTypeIrrel.refl b).instantiate1 (.fvar d ty (.sort .zero)) 0
    rw [denoteMeta_fvarTypeIrrel hirr] at hba
    obtain ⟨bs', hbs', hpw'⟩ := stripPis_instantiate1_pw (.fvar d (.sort .zero)) n 0 hsb
    simp only [Nat.zero_add] at hbs'
    obtain ⟨ds', bodyA, rfl, hlen', hbits', hbodyA⟩ := denoteMeta_stripPis n (d + 1) hbs' hba
    refine ⟨(0, pwBit φ mb.pw, ta) :: ds', bodyA, rfl, by simp [hlen'], ?_, ?_⟩
    · simp only [List.map_cons, List.cons.injEq, true_and]
      have hcomp : bs'.map (fun bm => pwBit φ bm.2.pw) = bs₀.map (fun bm => pwBit φ bm.2.pw) := by
        simpa [List.map_map, Function.comp_def] using congrArg (List.map (pwBit φ)) hpw'
      exact hbits'.trans hcomp
    · simp only [openDummiesP, Nat.zero_add]
      rwa [show d + 1 + n = d + (n + 1) by omega] at hbodyA
  | _ + 1, _, .bvar _, _, _, _, hst, _ | _ + 1, _, .fvar _ _, _, _, _, hst, _
  | _ + 1, _, .sort _, _, _, _, hst, _ | _ + 1, _, .const _ _, _, _, _, hst, _
  | _ + 1, _, .app _ _, _, _, _, hst, _ | _ + 1, _, .lam _ _ _, _, _, _, hst, _
  | _ + 1, _, .letE _ _ _ _, _, _, _, hst, _ | _ + 1, _, .lit _, _, _, _, hst, _
  | _ + 1, _, .proj _ _ _, _, _, _, hst, _ => nomatch hst

/-! ### `openDummiesP` structural lemmas -/

theorem openDummiesP_fvar (j : Nat) (ty : KExpr) :
    ∀ (n d c : Nat), openDummiesP n d c (.fvar j ty) = .fvar j ty
  | 0, _, _ => rfl
  | n + 1, d, c => by simp only [openDummiesP, Expr.instantiate1, openDummiesP_fvar]

theorem openDummiesP_const (k : KKey) (us : List KLevel) :
    ∀ (n d c : Nat), openDummiesP n d c (.const k us) = .const k us
  | 0, _, _ => rfl
  | n + 1, d, c => by simp only [openDummiesP, Expr.instantiate1, openDummiesP_const]

theorem openDummiesP_app (f a : KExpr) :
    ∀ (n d c : Nat), openDummiesP n d c (.app f a) =
      .app (openDummiesP n d c f) (openDummiesP n d c a)
  | 0, _, _ => rfl
  | n + 1, d, c => by simp only [openDummiesP, Expr.instantiate1, openDummiesP_app]

theorem openDummiesP_mkAppN (f : KExpr) (as : List KExpr) (n d c : Nat) :
    openDummiesP n d c (Expr.mkAppN f as) =
      Expr.mkAppN (openDummiesP n d c f) (as.map (openDummiesP n d c)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih =>
    simp only [Expr.mkAppN, List.map_cons]
    rw [ih (.app f a), openDummiesP_app]

theorem openDummiesP_bvar_lt :
    ∀ (n d c i : Nat), c ≤ i → i < c + n →
      openDummiesP n d c (.bvar i) = .fvar (d + (c + n - 1 - i)) (.sort .zero)
  | 0, _, _, _, _, hlt => by omega
  | n + 1, d, c, i, hle, hlt => by
    simp only [openDummiesP, Expr.instantiate1]
    by_cases heq : i = c + n
    · subst heq
      simp only [↓reduceIte, openDummiesP_fvar]
      congr 1; omega
    · have hgt : ¬ c + n < i := by omega
      simp only [heq, hgt, ↓reduceIte]
      rw [openDummiesP_bvar_lt n (d + 1) c i hle (by omega)]
      congr 1; omega

theorem openDummiesP_bvar_lt0 {n d i : Nat} (hi : i < n) :
    openDummiesP n d 0 (.bvar i) = .fvar (d + n - 1 - i) (.sort .zero) := by
  have h := openDummiesP_bvar_lt n d 0 i (Nat.zero_le _) (by omega)
  simpa [Nat.zero_add, show d + (n - 1 - i) = d + n - 1 - i by omega] using h

theorem denoteMeta_openDummiesP_bvar {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {φ : LevelParam → Nat} {n d i : Nat} (hi : i < n) :
    denoteMeta acval env φ (d + n) (openDummiesP n d 0 (.bvar i)) = some (.bvar i) := by
  rw [openDummiesP_bvar_lt0 hi]
  simp only [denoteMeta]
  congr 2; omega

theorem denoteMeta_openDummiesP_bvar0 {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {φ : LevelParam → Nat} {n i : Nat} (hi : i < n) :
    denoteMeta acval env φ n (openDummiesP n 0 0 (.bvar i)) = some (.bvar i) := by
  have h := denoteMeta_openDummiesP_bvar (acval := acval) (env := env) (φ := φ) (d := 0) (n := n) (i := i) hi
  simpa only [Nat.zero_add] using h

theorem openDummiesP_bvar_ge :
    ∀ (n d c i : Nat), c + n ≤ i →
      openDummiesP n d c (.bvar i) = .bvar (i - n)
  | 0, _, _, i, _ => by simp [openDummiesP]
  | n + 1, d, c, i, hge => by
    simp only [openDummiesP, Expr.instantiate1]
    have hne : i ≠ c + n := by omega
    have hgt : c + n < i := by omega
    simp only [hne, hgt, ↓reduceIte]
    rw [openDummiesP_bvar_ge n (d + 1) c (i - 1) (by omega)]
    congr 1; omega

theorem openDummiesP_add (m n d : Nat) (e : KExpr) :
    openDummiesP (m + n) d 0 e = openDummiesP n (d + m) 0 (openDummiesP m d n e) := by
  induction m generalizing d e with
  | zero => simp [openDummiesP]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [openDummiesP, Nat.zero_add]
    rw [show n + m = m + n by omega]
    rw [ih (d + 1) (e.instantiate1 (.fvar d (.sort .zero)) (m + n))]
    congr 1; omega

theorem consList_ge {V : Type u} :
    ∀ (vs : List V) (ρ : Nat → V) (k : Nat),
      consList vs ρ (vs.length + k) = ρ k
  | [], ρ, k => by simp
  | v :: vs, ρ, k => by
    simp only [consList_cons, List.length_cons]
    rw [show vs.length + 1 + k = vs.length + (k + 1) by omega]
    exact consList_ge vs (cons v ρ) (k + 1)

theorem consList_getElem {V : Type u} :
    ∀ (vs : List V) (ρ : Nat → V) (i : Nat) (hi : i < vs.length),
      consList vs ρ i = vs[vs.length - 1 - i]'(by omega)
  | [], _, _, hi => nomatch hi
  | v :: vs, ρ, i, hi => by
    simp only [consList_cons, List.length_cons]
    by_cases hlt : i < vs.length
    · rw [consList_getElem vs (cons v ρ) i hlt]
      have hidx : vs.length + 1 - 1 - i = (vs.length - 1 - i) + 1 := by omega
      simp only [hidx, List.getElem_cons_succ]
    · have hi_eq : i = vs.length := by simp at hi; omega
      subst hi_eq
      have h0 := consList_ge vs (cons v ρ) 0
      simp only [Nat.add_zero, cons] at h0
      rw [h0]
      simp

theorem consList_bvar_desc {V : Type u} (vs : List V) (ρ : Nat → V) {i : Nat} (hi : i < vs.length) :
    consList vs ρ (vs.length - 1 - i) = vs[i] := by
  rw [consList_getElem vs ρ (vs.length - 1 - i) (by omega)]
  congr 1; omega

/-! ### `AppChainOk` and `mkLamsAV` / `mkPisAV` reduction -/

/-- A function value `F` applied along a list of argument values `xs` satisfies `WellDenoted_app`'s
product-membership condition at every step. -/
def AppChainOk {V : Type u} [SetTheory V] (F : V) : List V → Prop
  | [] => True
  | x :: xs =>
    (∃ (v : Nat) (A : V) (B : V → V),
      F ∈ˢ piR v A B ∧ x ∈ˢ A ∧ (v = 0 → ∀ y, y ∈ˢ A → B y ∈ˢ (univZero : V))) ∧
    AppChainOk (SetTheory.app F x) xs

theorem AppChainOk.append {V : Type u} [SetTheory V] :
    ∀ {F : V} {xs ys : List V},
      AppChainOk F (xs ++ ys) ↔ AppChainOk F xs ∧ AppChainOk (xs.foldl SetTheory.app F) ys
  | _, [], _ => by simp [AppChainOk]
  | F, x :: xs, ys => by
    simp only [List.cons_append, AppChainOk, List.foldl_cons, AppChainOk.append (xs := xs), and_assoc]

theorem interp_mkAppN_foldl {V : Type u} [SetTheory V] (ρ : Nat → V) :
    ∀ (args : List AnnotTerm) (f : AnnotTerm),
      interp V ρ (AnnotTerm.mkAppN f args) =
        (args.map (interp V ρ)).foldl SetTheory.app (interp V ρ f)
  | [], _ => rfl
  | a :: args, f => by
    simp only [AnnotTerm.mkAppN_cons, List.map_cons, List.foldl_cons]
    exact interp_mkAppN_foldl ρ args (.app f a)

theorem appChainOk_of_wellDenotedV {V : Type u} [SetTheory V] {ρ : Nat → V} :
    ∀ (args : List AnnotTerm) {f : AnnotTerm},
      WellDenotedV V ρ (AnnotTerm.mkAppN f args) →
      WellDenotedV V ρ f ∧ (∀ a ∈ args, WellDenotedV V ρ a) ∧
        AppChainOk (interp V ρ f) (args.map (interp V ρ))
  | [], _, h => ⟨h, (fun _ hm => nomatch hm), trivial⟩
  | a :: args, f, h => by
    simp only [AnnotTerm.mkAppN_cons] at h
    obtain ⟨hfa, hargs, hch⟩ := appChainOk_of_wellDenotedV args h
    have hwd := hfa.1
    have hav := hfa.2
    rw [WellDenoted_app] at hwd
    rw [AnnotValid_app] at hav
    obtain ⟨hf1, ha1, v, A, B, hmem, haA, hfib⟩ := hwd
    refine ⟨⟨hf1, hav.1⟩, ?_, ⟨⟨v, A, B, hmem, haA, hfib⟩, hch⟩⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨ha1, hav.2⟩
    · exact hargs x hx'

/-- Reducing a positive-regime λ-chain along an `AppChainOk` argument list yields the body
evaluated in `consList vs ρ`, `SpineFit` against the λ domains, and `WellDenotedV` of the body. -/
theorem mkLamsAV_appChainOk_pos {V : Type u} [SetTheory V] :
    ∀ (lds : List (Nat × AnnotTerm)) (b : AnnotTerm) (vs : List V) (ρ : Nat → V),
      (∀ p ∈ lds, p.1 ≠ 0) →
      vs.length = lds.length →
      WellDenotedV V ρ (mkLamsAV lds b) →
      AppChainOk (interp V ρ (mkLamsAV lds b)) vs →
      vs.foldl SetTheory.app (interp V ρ (mkLamsAV lds b)) = interp V (consList vs ρ) b ∧
      SpineFit ρ (lds.map Prod.snd) vs ∧
      WellDenotedV V (consList vs ρ) b
  | [], b, [], ρ, _, _, hok, _ => ⟨rfl, trivial, hok⟩
  | [], _, _ :: _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, _, [], _, _, hlen, _, _ => by simp at hlen
  | (v, A) :: lds, b, x :: xs, ρ, hnz, hlen, hok, hch => by
    have hv : v ≠ 0 := hnz (v, A) List.mem_cons_self
    have hwd := hok.1
    have hav := hok.2
    simp only [mkLamsAV, WellDenoted_lam] at hwd
    simp only [mkLamsAV, AnnotValid_lam] at hav
    obtain ⟨hAok, hbok, B, hfib, -⟩ := hwd
    obtain ⟨⟨v', A', B', hslot, hxA', -⟩, hch'⟩ := hch
    have hv' : v' ≠ 0 := by
      intro h0; subst h0
      have hpt := eq_pt_of_mem_piR_zero hslot
      simp only [mkLamsAV, interp_lam] at hpt
      exact lamR_ne_pt hv hpt
    have hown : interp V ρ (mkLamsAV ((v, A) :: lds) b) ∈ˢ piR v (interp V ρ A) B := by
      simp only [mkLamsAV, interp_lam]
      exact lamR_mem hfib
    have hAeq : interp V ρ A = A' := piR_dom_unique hv hv' hown hslot
    have hxA : x ∈ˢ interp V ρ A := hAeq ▸ hxA'
    have happ : SetTheory.app (interp V ρ (mkLamsAV ((v, A) :: lds) b)) x =
        interp V (cons x ρ) (mkLamsAV lds b) := by
      simp only [mkLamsAV, interp_lam]
      exact app_lamR_pos hv hxA
    rw [happ] at hch'
    have hok' : WellDenotedV V (cons x ρ) (mkLamsAV lds b) := ⟨hbok x hxA, hav.2 x hxA⟩
    obtain ⟨heval, hsp, hbodyOk⟩ := mkLamsAV_appChainOk_pos lds b xs (cons x ρ)
      (fun p hp => hnz p (List.mem_cons_of_mem _ hp)) (by simpa using hlen) hok' hch'
    refine ⟨?_, ⟨hxA, hsp⟩, hbodyOk⟩
    simp only [List.foldl_cons, happ, consList_cons]
    exact heval

theorem foldl_app_pt {V : Type u} [SetTheory V] :
    ∀ (vs : List V), vs.foldl SetTheory.app (pt : V) = (pt : V)
  | [] => rfl
  | v :: vs => by simp only [List.foldl_cons, app_pt]; exact foldl_app_pt vs

theorem mkLamsAV_zero_head_foldl {V : Type u} [SetTheory V]
    {A b : AnnotTerm} {lds : List (Nat × AnnotTerm)} (ρ : Nat → V) (vs : List V) :
    vs.foldl SetTheory.app (interp V ρ (mkLamsAV ((0, A) :: lds) b)) = (pt : V) := by
  rw [show interp V ρ (mkLamsAV ((0, A) :: lds) b) = (pt : V) from by
    simp [mkLamsAV, interp_lam, lamR_zero]]
  exact foldl_app_pt vs

/-! ### `mkPisAV` and `TeleFitPA` bridges -/

/-- Substitute `a` at cut `k` across a Π-telescope's domain entries. -/
def instDs (a : AnnotTerm) : Nat → List (Nat × Nat × AnnotTerm) → List (Nat × Nat × AnnotTerm)
  | _, [] => []
  | k, (u, v, A) :: ds => (u, v, A.inst a k) :: instDs a (k + 1) ds

theorem instDs_length (a : AnnotTerm) :
    ∀ (k : Nat) (ds : List (Nat × Nat × AnnotTerm)), (instDs a k ds).length = ds.length
  | _, [] => rfl
  | k, _ :: ds => congrArg Nat.succ (instDs_length a (k + 1) ds)

theorem instDs_bits (a : AnnotTerm) :
    ∀ (k : Nat) (ds : List (Nat × Nat × AnnotTerm)),
      (instDs a k ds).map (fun d => d.2.1) = ds.map (fun d => d.2.1)
  | _, [] => rfl
  | k, _ :: ds => congrArg₂ List.cons rfl (instDs_bits a (k + 1) ds)

theorem mkPisAV_inst (a : AnnotTerm) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k : Nat) (R : AnnotTerm),
      (mkPisAV ds R).inst a k = mkPisAV (instDs a k ds) (R.inst a (k + ds.length))
  | [], k, R => by simp [mkPisAV, instDs]
  | (u, v, A) :: ds, k, R => by
    simp only [mkPisAV, AnnotTerm.inst_pi, instDs, List.length_cons]
    rw [mkPisAV_inst a ds (k + 1) R, show k + 1 + ds.length = k + (ds.length + 1) by omega]

theorem interp_inst_consList {V : Type u} [SetTheory V] (e a : AnnotTerm) (ρ : Nat → V) :
    ∀ (pre : List V),
      interp V (consList pre ρ) (e.inst a pre.length) =
        interp V (consList pre (cons (interp V ρ a) ρ)) e := by
  intro pre
  rw [interp_inst]
  have hsh : shiftE pre.length 0 (consList pre ρ) = ρ := by
    funext j
    show consList pre ρ (j + pre.length) = ρ j
    rw [Nat.add_comm, consList_ge]
  rw [hsh]
  congr 1
  funext i
  by_cases hlt : i < pre.length
  · show (if i < pre.length then consList pre ρ i else _) = _
    simp only [hlt, ↓reduceIte, consList_getElem pre ρ i hlt,
      consList_getElem pre (cons (interp V ρ a) ρ) i hlt]
  · by_cases heq : i = pre.length
    · subst heq
      show (if pre.length < pre.length then _ else if pre.length = pre.length then interp V ρ a else _) = _
      simp only [lt_irrefl, ↓reduceIte]
      have h0 := consList_ge pre (cons (interp V ρ a) ρ) 0
      simpa [cons] using h0.symm
    · have hgt : pre.length < i := by omega
      show (if i < pre.length then _ else if i = pre.length then _ else consList pre ρ (i - 1)) = _
      simp only [hlt, heq, ↓reduceIte]
      obtain ⟨k, hk⟩ : ∃ k, i = pre.length + (k + 1) := ⟨i - pre.length - 1, by omega⟩
      rw [hk, show pre.length + (k + 1) - 1 = pre.length + k by omega]
      rw [consList_ge pre ρ k, consList_ge pre (cons (interp V ρ a) ρ) (k + 1)]
      rfl

theorem spineFit_instDs {V : Type u} [SetTheory V] {a : AnnotTerm} {ρ : Nat → V} :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (pre vs : List V),
      SpineFit (consList pre (cons (interp V ρ a) ρ)) (ds.map (·.2.2)) vs →
      SpineFit (consList pre ρ) ((instDs a pre.length ds).map (·.2.2)) vs
  | [], _, [], _ => trivial
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim
  | (_, _, A) :: ds, pre, v :: vs, ⟨hv, hrest⟩ => by
    simp only [instDs, List.map_cons, SpineFit]
    refine ⟨?_, ?_⟩
    · rwa [interp_inst_consList A a ρ pre]
    · have h1 := spineFit_instDs ds (pre ++ [v]) vs (by simpa [consList_append] using hrest)
      simpa [consList_append, List.length_append] using h1

/-- From a `SpineFit` against `ds` and a list of terms `args` whose interpretations are `vs`,
build `TeleFitPA` along `mkPisAV ds R` with exact residual `interp`! -/
theorem teleFitPA_of_mkPisAV_spineFit {V : Type u} [SetTheory V] :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (R : AnnotTerm) (args : List AnnotTerm) (ρ : Nat → V),
      SpineFit ρ (ds.map (·.2.2)) (args.map (interp V ρ)) →
      ∃ rest, TeleFitPA V ρ (mkPisAV ds R) args rest ∧
        interp V ρ rest = interp V (consList (args.map (interp V ρ)) ρ) R ∧
        (∀ f es, R = AnnotTerm.mkAppN f es →
          ∃ f' es', rest = AnnotTerm.mkAppN f' es' ∧ es'.length = es.length ∧
            interp V ρ f' = interp V (consList (args.map (interp V ρ)) ρ) f ∧
            ∀ i, i < es.length →
              interp V ρ (es'.getD i default) =
                interp V (consList (args.map (interp V ρ)) ρ) (es.getD i default))
  | [], R, [], ρ, _ =>
    ⟨R, .nil, rfl, fun f es hR => ⟨f, es, hR, rfl, rfl, fun _ _ => rfl⟩⟩
  | [], _, _ :: _, _, h => h.elim
  | _ :: _, _, [], _, h => h.elim
  | (u, v, A) :: ds, R, a :: args, ρ, ⟨ha, hrest⟩ => by
    have hsp' : SpineFit ρ ((instDs a 0 ds).map (·.2.2)) (args.map (interp V ρ)) :=
      spineFit_instDs ds [] (args.map (interp V ρ)) hrest
    obtain ⟨rest, hfit, hinterp, hmk⟩ :=
      teleFitPA_of_mkPisAV_spineFit (instDs a 0 ds) (R.inst a ds.length) args ρ hsp'
    refine ⟨rest, .cons ha (by rwa [mkPisAV_inst a ds 0 R, Nat.zero_add]), ?_, ?_⟩
    · have hlen : (args.map (interp V ρ)).length = ds.length := by
        simpa using hrest.length_eq
      rw [hinterp, ← hlen, interp_inst_consList R a ρ (args.map (interp V ρ))]
      rfl
    · intro f es hR
      have hlen : (args.map (interp V ρ)).length = ds.length := by
        simpa using hrest.length_eq
      have hR' : R.inst a ds.length =
          AnnotTerm.mkAppN (f.inst a ds.length) (es.map (fun e => e.inst a ds.length)) := by
        rw [hR]
        have hgo : ∀ (xs : List AnnotTerm) (h0 : AnnotTerm),
            (AnnotTerm.mkAppN h0 xs).inst a ds.length =
              AnnotTerm.mkAppN (h0.inst a ds.length) (xs.map (fun e => e.inst a ds.length)) := by
          intro xs
          induction xs with
          | nil => intro h0; rfl
          | cons x xs ih =>
            intro h0
            simp only [AnnotTerm.mkAppN_cons, List.map_cons]
            rw [ih (.app h0 x)]; rfl
        exact hgo es f
      obtain ⟨f', es', hreq, heslen, hf', hes'⟩ := hmk _ _ hR'
      refine ⟨f', es', hreq, by simpa using heslen, ?_, ?_⟩
      · rw [hf', ← hlen, interp_inst_consList f a ρ (args.map (interp V ρ))]; rfl
      · intro i hi
        have hi' := hes' i (by simpa using hi)
        rw [hi']
        have hget : (es.map (fun e => e.inst a ds.length)).getD i default =
            (es.getD i default).inst a ds.length := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
        rw [hget, ← hlen, interp_inst_consList (es.getD i default) a ρ (args.map (interp V ρ))]
        rfl

/-- From `F ∈ˢ interp (mkPisAV ds R)` with every `d.2.1 ≠ 0` and `AppChainOk F (args.map interp)`,
build `TeleFitPA V ρ (mkPisAV ds R) args rest` and `SpineFit`! -/
theorem teleFitPA_of_mkPisAV_appChainOk_pos {V : Type u} [SetTheory V] :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (R : AnnotTerm) (args : List AnnotTerm) (F : V) (ρ : Nat → V),
      (∀ d ∈ ds, d.2.1 ≠ 0) →
      args.length = ds.length →
      F ∈ˢ interp V ρ (mkPisAV ds R) →
      AppChainOk F (args.map (interp V ρ)) →
      ∃ rest, TeleFitPA V ρ (mkPisAV ds R) args rest ∧
        SpineFit ρ (ds.map (·.2.2)) (args.map (interp V ρ)) ∧
        (args.map (interp V ρ)).foldl SetTheory.app F ∈ˢ interp V ρ rest ∧
        interp V ρ rest = interp V (consList (args.map (interp V ρ)) ρ) R
  | [], R, [], F, ρ, _, _, hF, _ => ⟨R, .nil, trivial, hF, rfl⟩
  | [], _, _ :: _, _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, _, [], _, _, _, hlen, _, _ => by simp at hlen
  | (u, v, A) :: ds, R, a :: args, F, ρ, hnz, hlen, hF, hch => by
    have hv : v ≠ 0 := hnz (u, v, A) List.mem_cons_self
    simp only [mkPisAV, interp_pi] at hF
    obtain ⟨⟨v', A', B', hslot, haA', -⟩, hch'⟩ := hch
    have hv' : v' ≠ 0 := by
      intro h0; subst h0
      have hpt := eq_pt_of_mem_piR_zero hslot
      exact not_pt_mem_piR_pos hv (hpt ▸ hF)
    have hAeq : interp V ρ A = A' := piR_dom_unique hv hv' hF hslot
    have haA : interp V ρ a ∈ˢ interp V ρ A := hAeq ▸ haA'
    have hF' : SetTheory.app F (interp V ρ a) ∈ˢ
        interp V ρ (mkPisAV (instDs a 0 ds) (R.inst a ds.length)) := by
      rw [← show ((mkPisAV ds R).inst a 0) = mkPisAV (instDs a 0 ds) (R.inst a ds.length) from by
        simpa using mkPisAV_inst a ds 0 R]
      rw [interp_inst0]
      exact app_mem_piR hF haA (fun h0 => absurd h0 hv)
    have hnz' : ∀ d ∈ instDs a 0 ds, d.2.1 ≠ 0 := by
      intro d hd
      have hmem : d.2.1 ∈ (instDs a 0 ds).map (fun x => x.2.1) := List.mem_map_of_mem hd
      rw [instDs_bits] at hmem
      obtain ⟨d', hd', heq⟩ := List.mem_map.mp hmem
      rw [← heq]
      exact hnz d' (List.mem_cons_of_mem _ hd')
    obtain ⟨rest, hfit, hsp', hmem', hinterp'⟩ :=
      teleFitPA_of_mkPisAV_appChainOk_pos (instDs a 0 ds) (R.inst a ds.length) args
        (SetTheory.app F (interp V ρ a)) ρ hnz'
        (by rw [instDs_length]; simpa using hlen) hF' hch'
    have hsp : SpineFit (cons (interp V ρ a) ρ) (ds.map (·.2.2)) (args.map (interp V ρ)) := by
      have hback : ∀ (ds₀ : List (Nat × Nat × AnnotTerm)) (pre vs : List V),
          SpineFit (consList pre ρ) ((instDs a pre.length ds₀).map (·.2.2)) vs →
          SpineFit (consList pre (cons (interp V ρ a) ρ)) (ds₀.map (·.2.2)) vs := by
        intro ds₀
        induction ds₀ with
        | nil => intro pre vs h; cases vs with | nil => trivial | cons _ _ => exact h.elim
        | cons d₀ ds₀ ih =>
          intro pre vs h
          cases vs with
          | nil => exact h.elim
          | cons w ws =>
            obtain ⟨hw, hws⟩ := h
            refine ⟨by rwa [← interp_inst_consList d₀.2.2 a ρ pre], ?_⟩
            have h2 := ih (pre ++ [w]) ws (by simpa [consList_append, List.length_append] using hws)
            simpa [consList_append] using h2
      exact hback ds [] (args.map (interp V ρ)) hsp'
    refine ⟨rest, .cons haA (by rwa [mkPisAV_inst a ds 0 R, Nat.zero_add]), ⟨haA, hsp⟩, hmem', ?_⟩
    rw [hinterp']
    have hlen' : (args.map (interp V ρ)).length = ds.length := by simpa using hlen
    rw [← hlen', interp_inst_consList R a ρ (args.map (interp V ρ))]
    rfl

/-! ### Closing `WellDenotedV` / `interp` invariance for closed terms -/

theorem bvarsBelow_of_liftN_eq :
    ∀ (e : AnnotTerm) (k : Nat), (∀ j ≥ k, e.liftN 1 j = e) → Ix.Kernel.Term.Term.bvarsBelow k e.erase
  | .bvar i, k, h => by
    by_cases hi : i < k
    · exact hi
    · exfalso
      have h1 := h k (Nat.le_refl k)
      simp only [AnnotTerm.liftN, show ¬ i < k from hi, ↓reduceIte] at h1
      have := AnnotTerm.bvar.inj h1
      omega
  | .sort _, _, _ | .const _ _, _, _ | .prf, _, _ => trivial
  | .app f a, k, h =>
    ⟨bvarsBelow_of_liftN_eq f k fun j hj => by have h1 := h j hj; simp [AnnotTerm.liftN] at h1; exact h1.1,
     bvarsBelow_of_liftN_eq a k fun j hj => by have h1 := h j hj; simp [AnnotTerm.liftN] at h1; exact h1.2⟩
  | .lam _ A b, k, h =>
    ⟨bvarsBelow_of_liftN_eq A k fun j hj => by have h1 := h j hj; simp [AnnotTerm.liftN] at h1; exact h1.1,
     bvarsBelow_of_liftN_eq b (k + 1) fun j hj => by
       have h1 := h (j - 1) (by omega)
       simp only [AnnotTerm.liftN, show j - 1 + 1 = j by omega] at h1
       exact (AnnotTerm.lam.inj h1).2.2⟩
  | .pi _ _ A B, k, h =>
    ⟨bvarsBelow_of_liftN_eq A k fun j hj => by have h1 := h j hj; simp [AnnotTerm.liftN] at h1; exact h1.1,
     bvarsBelow_of_liftN_eq B (k + 1) fun j hj => by
       have h1 := h (j - 1) (by omega)
       simp only [AnnotTerm.liftN, show j - 1 + 1 = j by omega] at h1
       exact (AnnotTerm.pi.inj h1).2.2.2⟩
  | .eqE a b, k, h =>
    ⟨bvarsBelow_of_liftN_eq a k fun j hj => by have h1 := h j hj; simp [AnnotTerm.liftN] at h1; exact h1.1,
     bvarsBelow_of_liftN_eq b k fun j hj => by have h1 := h j hj; simp [AnnotTerm.liftN] at h1; exact h1.2⟩
  | .fst e, k, h =>
    bvarsBelow_of_liftN_eq e k fun j hj => by have h1 := h j hj; simp [AnnotTerm.liftN] at h1; exact h1
  | .snd e, k, h =>
    bvarsBelow_of_liftN_eq e k fun j hj => by have h1 := h j hj; simp [AnnotTerm.liftN] at h1; exact h1
  | .chain fs e, k, h =>
    ⟨fun m => bvarsBelow_of_liftN_eq (fs m) k fun j hj => by
       have h1 := h j hj; simp only [AnnotTerm.liftN] at h1
       exact congrFun (AnnotTerm.chain.inj h1).1 m,
     bvarsBelow_of_liftN_eq e k fun j hj => by
       have h1 := h j hj; simp only [AnnotTerm.liftN] at h1
       exact (AnnotTerm.chain.inj h1).2⟩
  | .bgraph _ f, k, h =>
    bvarsBelow_of_liftN_eq f k fun j hj => by have h1 := h j hj; simp [AnnotTerm.liftN] at h1; exact h1

theorem closed_interp_env {V : Type u} [SetTheory V] {t : AnnotTerm}
    (hcl : ∀ k, t.liftN 1 k = t) (ρ₁ ρ₂ : Nat → V) :
    interp V ρ₁ t = interp V ρ₂ t :=
  Ix.Kernel.Semantics.interp_congr_below V t 0 ρ₁ ρ₂
    (bvarsBelow_of_liftN_eq t 0 fun j _ => hcl j) (fun _ hi => nomatch hi)

theorem closed_wellDenotedV_env {V : Type u} [SetTheory V] {t : AnnotTerm}
    (hcl : ∀ k, t.liftN 1 k = t) {ρ₁ : Nat → V} (ρ₂ : Nat → V)
    (hok : WellDenotedV V ρ₁ t) : WellDenotedV V ρ₂ t :=
  (WellDenotedV_congr_below t 0 ρ₁ ρ₂
    (bvarsBelow_of_liftN_eq t 0 fun j _ => hcl j) (fun _ hi => nomatch hi)).mp hok

/-! ## Section 8: `auxRec_fire` -/

private theorem bvarsDesc_wellDenotedV {V : Type u} [SetTheory V] (ρ : Nat → V) (o n : Nat) :
    ∀ a ∈ ((List.range n).map fun i => AnnotTerm.bvar (o + n - 1 - i)),
      WellDenotedV V ρ a := by
  intro a ha
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
  exact ⟨trivial, trivial⟩

private theorem bvarsDesc_interp_consList {V : Type u} [SetTheory V]
    (xs ys : List V) (ρ : Nat → V) :
    (((List.range xs.length).map fun i => AnnotTerm.bvar (ys.length + xs.length - 1 - i)).map
      (interp V (consList (xs ++ ys) ρ))) = xs := by
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  simp only [List.getElem_map, List.getElem_range, interp]
  have hlt : ys.length + xs.length - 1 - i < (xs ++ ys).length := by simp; omega
  rw [consList_getElem (xs ++ ys) ρ _ hlt]
  have hidx : (xs ++ ys).length - 1 - (ys.length + xs.length - 1 - i) = i := by simp; omega
  simp only [hidx]
  exact List.getElem_append_left hi2

private theorem bvarsDesc0_interp_consList {V : Type u} [SetTheory V]
    (xs ys : List V) (ρ : Nat → V) :
    (((List.range ys.length).map fun i => AnnotTerm.bvar (ys.length - 1 - i)).map
      (interp V (consList (xs ++ ys) ρ))) = ys := by
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  simp only [List.getElem_map, List.getElem_range, interp]
  rw [consList_append, consList_bvar_desc ys (consList xs ρ) hi2]

private theorem stripPis_instantiateLevelParams (ps : List LevelParam) (us : List KLevel) :
    ∀ (n : Nat) {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.stripPis n = some (bs, rem) →
      (e.instantiateLevelParams ps us).stripPis n =
        some (bs.map (fun p => (p.1.instantiateLevelParams ps us, { p.2 with pw := Level.substPW ps us p.2.pw })),
          rem.instantiateLevelParams ps us)
  | 0, e, rem, bs, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | n + 1, .forallE ty b m, rem, bs, h => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, rem₀⟩, hsb, hpair⟩ := h
    injection hpair with hbs hrem
    subst hbs hrem
    simp only [Expr.instantiateLevelParams, Expr.stripPis,
      stripPis_instantiateLevelParams ps us n hsb, Option.map_some, List.map_cons]
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, h | _ + 1, .lit _, _, _, h
  | _ + 1, .proj _ _ _, _, _, h => nomatch h

private theorem stripLams_instantiateLevelParams (ps : List LevelParam) (us : List KLevel) :
    ∀ (n : Nat) {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.stripLams n = some (bs, rem) →
      (e.instantiateLevelParams ps us).stripLams n =
        some (bs.map (fun p => (p.1.instantiateLevelParams ps us, { p.2 with pw := Level.substPW ps us p.2.pw })),
          rem.instantiateLevelParams ps us)
  | 0, e, rem, bs, h => by
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | n + 1, .lam ty b m, rem, bs, h => by
    simp only [Expr.stripLams, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, rem₀⟩, hsb, hpair⟩ := h
    injection hpair with hbs hrem
    subst hbs hrem
    simp only [Expr.instantiateLevelParams, Expr.stripLams,
      stripLams_instantiateLevelParams ps us n hsb, Option.map_some, List.map_cons]
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .forallE _ _ _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, h | _ + 1, .lit _, _, _, h
  | _ + 1, .proj _ _ _, _, _, h => nomatch h

theorem stripPis_posOf_inv {ps : List LevelParam} {n : Nat} {e rem : KExpr}
    {bs : List (KExpr × BinderMeta)}
    (h : (Core.posOf ps e).stripPis n = some (bs, rem)) :
    ∃ bs₀ rem₀, e.stripPis n = some (bs₀, rem₀) ∧
      rem = Core.posOf ps rem₀ := by
  induction n generalizing e bs with
  | zero =>
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], e, rfl, rfl⟩
  | succ n ih =>
    cases e with
    | forallE ty b m =>
      simp only [Core.posOf, Expr.instantiateLevelParams, Expr.stripPis,
        Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', rem'⟩, hsb, hpair⟩ := h
      injection hpair with _ hrem
      subst hrem
      obtain ⟨bs₀, rem₀, hsb₀, hrem₀⟩ := ih hsb
      exact ⟨(ty, m) :: bs₀, rem₀, by simp [Expr.stripPis, hsb₀], hrem₀⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _ | lit _
    | proj _ _ _ =>
      simp [Core.posOf, Expr.instantiateLevelParams, Expr.stripPis] at h

theorem spineFit_append_iff {V : Type u} [SetTheory V]
    {Ds₁ Ds₂ : List AnnotTerm} {ρ : Nat → V} {as₁ as₂ : List V}
    (hlen : Ds₁.length = as₁.length) :
    SpineFit ρ (Ds₁ ++ Ds₂) (as₁ ++ as₂) ↔
      SpineFit ρ Ds₁ as₁ ∧ SpineFit (consList as₁ ρ) Ds₂ as₂ := by
  constructor
  · intro h
    obtain ⟨bs₁, bs₂, heq, h1, h2⟩ := spineFit_append_split h
    have hbs1_len : bs₁.length = as₁.length := h1.length_eq.trans hlen
    have h1eq : as₁ = bs₁ := by
      have := congrArg (List.take as₁.length) heq
      rw [List.take_left] at this
      rw [← hbs1_len, List.take_left] at this
      exact this
    have h2eq : as₂ = bs₂ := by
      have := congrArg (List.drop as₁.length) heq
      rw [List.drop_left] at this
      rw [← hbs1_len, List.drop_left] at this
      exact this
    subst h1eq; subst h2eq
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact h1.append h2

theorem spineFit_of_sat_consList {V : Type u} [SetTheory V]
    {Ds : List AnnotTerm} {vs : List V} {ρ : Nat → V}
    (hlen : Ds.length = vs.length)
    (hsat : Sat V Ds.reverse (consList vs ρ)) :
    SpineFit ρ Ds vs := by
  have h1 := Ix.Kernel.Model.spineFit_of_sat (Δ₀ := []) (by simpa using hsat)
  have hρ : (fun j => consList vs ρ (j + Ds.length)) = ρ := by
    funext j; rw [hlen, Nat.add_comm, consList_ge]
  have hvs : (List.range Ds.length).reverse.map (consList vs ρ) = vs := by
    apply List.ext_getElem (by simp [hlen])
    intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
    rw [consList_getElem vs ρ _ (by omega)]
    congr 1; omega
  rwa [hρ, hvs] at h1

theorem nativeTyAVI_fold_at {V : Type u} [SetTheory V] {u w nP : Nat}
    {pps : List (Nat × Nat × AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}
    {ρ : Nat → V} {ps is : List V}
    (hX : XChainsOk u w (consList ps ρ) ((pps.drop nP).map (·.2.2)) rss tlss Eiss Fss Ess)
    (hsp_p : SpineFit ρ ((pps.take nP).map (·.2.2)) ps)
    (hsp_i : SpineFit (consList ps ρ) ((pps.drop nP).map (·.2.2)) is) :
    (ps ++ is).foldl SetTheory.app
      (interp V ρ (nativeTyAVI u w pps ((pps.drop nP).map (·.2.2)) rss tlss Eiss Fss Ess)) =
      SetTheory.app
        (fixFamI u w (consList ps ρ) ((pps.drop nP).map (·.2.2)) ((pps.drop nP).map (·.2.2)).length
          rss tlss Eiss Fss Ess)
        (tupW u is) := by
  have hsp_all : SpineFit ρ (pps.map (·.2.2)) (ps ++ is) := by
    have hsplit : pps.map (·.2.2) = (pps.take nP).map (·.2.2) ++ (pps.drop nP).map (·.2.2) := by
      rw [← List.map_append, List.take_append_drop]
    rw [hsplit]
    exact hsp_p.append hsp_i
  have hilen : ((pps.drop nP).map (·.2.2)).length = is.length := hsp_i.length_eq.symm
  have hsh : shiftE ((pps.drop nP).map (·.2.2)).length 0 (consList (ps ++ is) ρ) = consList ps ρ := by
    rw [consList_append, hilen]; exact shiftE_consList is (consList ps ρ)
  have hfr : frameIdx ((pps.drop nP).map (·.2.2)).length (consList (ps ++ is) ρ) = is := by
    rw [consList_append, hilen]; exact frameIdx_consList' is (consList ps ρ)
  have hbase : FixBaseI u w (consList (ps ++ is) ρ) ((pps.drop nP).map (·.2.2)) rss tlss Eiss Fss Ess := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hsh]; exact hX.hI
    · rw [hsh]; exact hX.hok
    · rw [hsh, hfr]; exact hsp_i
  rw [nativeTyAVI_fold hsp_all hbase, hsh, hfr]

set_option maxHeartbeats 1600000 in
/-- Fire a native auxiliary recursor `aux.rec` on pure value lists `(xs_v, vs_v, fs_v)` when its
elimination universe `elimLvls[0]` is positive at `ψ_P`, reducing both the recursor step (via
`mp.rec_rules`) and the rule RHS's leading `nP + 1 + anc + rnf` lambdas (via `RecRhsPwNoModel` +
`mkLamsAV_appChainOk_pos`) directly to the `k`-th minor applied to `fs_v ++ ih_vals`. -/
theorem auxRec_fire {V : Type u} [SetTheory V] {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Env .anon} {Reg : NativeFam .anon → Prop}
    (ht : t.check = .ok ())
    (hbasis : ∀ ci ∈ IxVM.Refinement.TableInhabit.basisEnv.consts, env.find? ci.name = some ci)
    (hreg : FamRegistryWith FormerOpenTraceAt t E env Reg)
    (mp : EnvModelM V .verified env)
    (hN : ∀ fam, Reg fam → NativeFamOk mp fam)
    {auxKey auxRecKey : KKey} {cvAuxRec : ConstantVal .anon} {arules : List (RecRule .anon)}
    {nP bnl anc : Nat}
    (auxIndWit : NativeIndWitness t E env auxKey)
    (hauxInd_lvls : auxIndWit.cv.levelParams.length = bnl)
    (hauxInd_idx : auxIndWit.ip.idx.toNat = 0)
    (hauxInd_rec : ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt E auxIndWit.ip.block = some cb ∧ cb.info = .muts ms ∧
      ms[0]? = some (.indc ind) ∧ ind.params.toNat = nP ∧ ind.indices.toNat = 1 ∧
      ind.ctors.size = anc)
    (hauxInd_sort : ∃ bs u, (Core.posOf auxIndWit.cv.levelParams auxIndWit.cv.type).stripPis (nP + 1) =
      some (bs, .sort u) ∧ ∀ φ, (substLevel u ((List.range bnl).map .param)).eval φ > 0)
    (hfindAuxRec : env.find? auxRecKey =
      some (.recInfo cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules))
    (hAuxRec_lvls : cvAuxRec.levelParams.length = bnl + 1)
    (hAuxRec_perm : cvAuxRec.levelParams.Perm (List.range (bnl + 1)))
    (hauxRec_famBlk : ∃ (aR : _root_.Address) (cHost : Ixon.Constant) (rcR : Ixon.Recursor)
        (nf : Nat) (p0 : _root_.Address) (cm0 : Ixon.Constant) (ip0 : Ixon.InductiveProj),
      Core.keyOf t aR = auxRecKey ∧ RecHostAt E aR cHost rcR ∧
      recMotiveCarrierAt cHost rcR 0 nf = some p0 ∧
      Ix.Cert.recordAt E p0 = some cm0 ∧ cm0.info = .iPrj ip0 ∧ ip0.block = auxIndWit.ip.block)
    (hAuxRec_maj : ∃ majBs majDom majBody majBm majLvls majArgs,
      (Core.posOf cvAuxRec.levelParams cvAuxRec.type).stripPis (nP + 1 + anc + 1) =
        some (majBs, .forallE majDom majBody majBm) ∧
      majDom = Expr.mkAppN (.const auxKey majLvls) majArgs ∧
      LvEqList majLvls ((List.range bnl).map fun m => .param (1 + m)) ∧
      majArgs.length = nP + 1 ∧
      List.Forall₂ ExprSemEq (majArgs.take nP)
        ((List.range nP).map fun m => .bvar (nP + 1 + anc + 1 - 1 - m)) ∧
      majArgs[nP]? = some (.bvar 0))
    (hrecCtor : ∀ j rl, arules[j]? = some rl →
      rl.ctor = Core.keyOf t (Core.cprjAddr auxIndWit.ip.block 0 j))
    -- Registered native family `famAux` with its `NativeFamAt` data
    {famAux : NativeFam .anon} {env₀ : Env .anon} {bsT : List (KExpr × BinderMeta)}
    {ppsAll : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {uAV : (LevelParam → Nat) → Nat} {fssZ : (LevelParam → Nat) → List (List AnnotTerm)}
    {idxF : Nat → List KExpr}
    {dsF : Nat → (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (LevelParam → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List Ix.Kernel.RecFieldKind} {fvsPF xFvsF : Nat → List KExpr}
    {xrestF : Nat → KExpr}
    {eissF : Nat → (LevelParam → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hregAux : Reg famAux) (hnameAux : famAux.p.cvT.name = auxKey)
    (hAtAux : NativeFamAt mp famAux.p famAux.cvS famAux.cvTa famAux.ctorsA env₀ bsT ppsAll
      uAV fssZ idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF)
    {k : Nat} (hk : k < anc) {rl : RecRule .anon} (hrl : arules[k]? = some rl)
    {rbs : List (KExpr × BinderMeta)} {rargs : List KExpr}
    (hr_strip : (Core.posOf cvAuxRec.levelParams rl.rhs).stripLams (nP + 1 + anc + rl.nfields) =
      some (rbs, Expr.mkAppN (.bvar (rl.nfields + anc - 1 - k)) rargs))
    (ψ_P : LevelParam → Nat) (elimLvls : List KLevel)
    (h_elim_len : elimLvls.length = bnl + 1)
    (h_elim_drop : LvEqList (elimLvls.drop 1) ((List.range bnl).map .param))
    (h_elim_nz : (elimLvls.getD 0 .zero).eval ψ_P > 0)
    (xs_v vs_v fs_v : List V) (ρ₀ : Nat → V)
    (hxs_len : xs_v.length = nP + 1 + anc + 1)
    (hvs_len : vs_v.length = nP)
    (hfs_len : fs_v.length = rl.nfields)
    (hxs_pref : xs_v.take nP = vs_v)
    (hfitC : SpineFit ρ₀ ((dsF k (origVal famAux.p.cvT.levelParams ψ_P)).map (·.2.2)) (vs_v ++ fs_v))
    (hApp : AppChainOk
      (interp V ρ₀ (mp.base2.acval auxRecKey (origVal cvAuxRec.levelParams (ψ_rec elimLvls bnl ψ_P))))
      (xs_v ++ [inj k (mkTower (fs_v ++ [pt]))])) :
    ∃ (rbodyA : AnnotTerm) (rargsA : List AnnotTerm),
      denoteMeta mp.base2.acval env (ψ_rec elimLvls bnl ψ_P) (nP + 1 + anc + rl.nfields)
        (openDummiesP (nP + 1 + anc + rl.nfields) 0 0
          (Expr.mkAppN (.bvar (rl.nfields + anc - 1 - k)) rargs)) = some rbodyA ∧
      rbodyA = AnnotTerm.mkAppN (.bvar (rl.nfields + anc - 1 - k)) rargsA ∧
      DenoteMetaSpine mp.base2.acval env (ψ_rec elimLvls bnl ψ_P) (nP + 1 + anc + rl.nfields)
        (rargs.map (openDummiesP (nP + 1 + anc + rl.nfields) 0 0)) rargsA ∧
      (xs_v ++ [inj k (mkTower (fs_v ++ [pt]))]).foldl SetTheory.app
        (interp V ρ₀ (mp.base2.acval auxRecKey (origVal cvAuxRec.levelParams (ψ_rec elimLvls bnl ψ_P)))) =
        interp V (consList (xs_v.take (nP + 1 + anc) ++ fs_v) ρ₀) rbodyA ∧
      WellDenotedV V (consList (xs_v.take (nP + 1 + anc) ++ fs_v) ρ₀) rbodyA := by
  -- 1. `auxRecKey` is neither reserved nor modeled, so `RecRhsPwNoModel` applies.
  obtain ⟨majBs, majDom, majBody, majBm, majLvls, majArgs, hmajStrip, hmajDom, hmajLvls,
    hmajArgs_len, hmajArgs_pref, hmajArgs_idx⟩ := hAuxRec_maj
  have hnotResRec : Ix.Kernel.reservedBasisNames.contains auxRecKey = false :=
    auxRec_not_reserved hfindAuxRec auxIndWit.hnotRes hbasis hmajStrip hmajDom
  have hnoModelRec : ¬ HasModel env auxRecKey := by
    intro hm
    obtain ⟨aR, cHost, rcR, nf, p0, cm0, ip0, haR, hrcR, hmc, hcm0, hip0, hblk0⟩ :=
      hauxRec_famBlk
    subst haR
    have hnotNat := hreg.recModelNotNative aR cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules
      cHost rcR nf p0 cm0 ip0 hfindAuxRec hm hrcR hmc hcm0 hip0
    rw [hblk0] at hnotNat
    exact hnotNat auxIndWit.hnat
  -- Recover un-positioned `cvAuxRec.type.stripPis (nP + 1 + anc + 1)`
  obtain ⟨pre0, rem0, hstrip0, hrem0⟩ := stripPis_posOf_inv hmajStrip
  cases rem0 with
  | forallE dom0 body0 majBm0 =>
    -- Obtain `RecRhsPwNoModel` facts at `cvAuxRec`
    obtain ⟨hpre0_pw, hlarge0, hrules0⟩ :=
      hreg.recRhsPw auxRecKey cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules
        hfindAuxRec hnotResRec hnoModelRec pre0 dom0 body0 majBm0 hstrip0
    have hrl_mem : rl ∈ arules := List.mem_of_getElem? hrl
    obtain ⟨hfire_cases, bs0, rbody0, hsl0, hbs0_pw⟩ := hrules0 rl hrl_mem
    have hfire_ne : rl.fire ≠ .inert := (Ix.Kernel.Open.recRules_fire mp.base2.rec_ctors hfindAuxRec hrl_mem).1
    have hfire_plain : rl.fire = .plain := by
      rcases hfire_cases with hp | hi
      · exact hp
      · exact absurd hi hfire_ne
    -- Connect `dom0.getAppFn` to `.const auxKey _` with length `bnl`, so `majBm0.pw = .ifAllZero [elim]`.
    have hdom0_eq : Core.posOf cvAuxRec.levelParams dom0 = majDom := by
      simp only [Core.posOf, Expr.instantiateLevelParams] at hrem0
      exact (Expr.forallE.inj hrem0).1.symm
    have hfn_pos : (Core.posOf cvAuxRec.levelParams dom0).getAppFn = .const auxKey majLvls := by
      rw [hdom0_eq, hmajDom, Expr.getAppFn_mkAppN]; rfl
    have hdom0_fn : ∃ us0, dom0.getAppFn = .const auxKey us0 ∧ us0.length = bnl := by
      have hgo : ∀ (e : KExpr), (Core.posOf cvAuxRec.levelParams e).getAppFn = .const auxKey majLvls →
          ∃ us0, e.getAppFn = .const auxKey us0 ∧ us0.length = majLvls.length := by
        intro e
        induction e with
        | app f a ihf _ =>
          intro h
          simp only [Core.posOf, Expr.instantiateLevelParams, Expr.getAppFn] at h ⊢
          exact ihf h
        | const n us =>
          intro h
          simp only [Core.posOf, Expr.instantiateLevelParams, Expr.getAppFn] at h ⊢
          injection h with hn hus
          subst hn hus
          exact ⟨us, rfl, by simp⟩
        | bvar _ | fvar _ _ | sort _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ _ | lit _
        | proj _ _ _ =>
          intro h; simp [Core.posOf, Expr.instantiateLevelParams, Expr.getAppFn] at h
      obtain ⟨us0, hfn0, hlen0⟩ := hgo dom0 hfn_pos
      have hmlen : majLvls.length = bnl := by
        have h1 := (lvEqList_getElem hmajLvls).1; simpa using h1
      exact ⟨us0, hfn0, hlen0.trans hmlen⟩
    obtain ⟨us0, hdom0_fn, hus0_len⟩ := hdom0_fn
    obtain ⟨elim, restLps, hcvLps_cons, hmaj0_pw, hrec_ctors_lps⟩ :=
      hlarge0 auxKey us0 hdom0_fn (by omega)
    -- 2. Connect `famAux` to `auxIndWit` and `aux.c_k`
    have hreadAux := hreg.fams famAux hregAux
    have hreadAtAux := hreadAux.readAt ht (hnameAux.trans auxIndWit.hkey.symm) auxIndWit.hrec auxIndWit.hinfo
    obtain ⟨-, -, cbA, msA, indA, hcbA, hmsA, hindA, hnPA, hnIdxA, hlenA, hctorNameA⟩ := hreadAtAux
    obtain ⟨cb', ms', ind', hcb', hms', hind', hnP', hnIdx', hanc'⟩ := hauxInd_rec
    have hcb_eq : cbA = cb' := Option.some.inj (hcbA.symm.trans hcb')
    subst hcb_eq
    have hms_eq : msA = ms' := Ixon.ConstantInfo.muts.inj (hmsA.symm.trans hms')
    subst hms_eq
    rw [hauxInd_idx] at hindA hctorNameA
    have hind_eq : indA = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hindA.symm.trans hind'))
    subst hind_eq
    have hfam_nP : famAux.p.nP = nP := hnPA.trans hnP'
    have hfam_nIdx : famAux.p.nIdx = 1 := hnIdxA.trans hnIdx'
    have hfam_ctors_len : famAux.ctorsA.length = anc := hlenA.trans hanc'
    have hfam_lps : famAux.p.cvT.levelParams = List.range bnl :=
      famRead_lps_range hreadAux (by rw [← hreadAux.lps, famRead_cvS_eq hreadAux hnameAux auxIndWit.hfind]; exact hauxInd_lvls)
    have h_origAux : origVal famAux.p.cvT.levelParams ψ_P = ψ_P := by
      unfold origVal
      rw [hfam_lps]
      simpa [Core.posLevels] using substFn_range_param bnl ψ_P
    -- Result sort of `famAux` is positive at every valuation
    have hres_nz : famAux.p.resSort.eval ψ_P > 0 := by
      obtain ⟨bsS, uS, hstS, huS⟩ := hauxInd_sort
      have hcvS_eq : famAux.cvS = auxIndWit.cv := famRead_cvS_eq hreadAux hnameAux auxIndWit.hfind
      rw [← hcvS_eq] at hstS
      obtain ⟨-, hlv⟩ := famRead_resSort_of_stripPisZetaSort mp.base2.wf hreadAux
        (stripPis_to_stripPisZetaSort hstS)
      have h1 := huS ψ_P
      rw [IxVM.Refinement.KernelLevels.eval_substLevel_eq_subst, Ix.Kernel.Level.eval_subst,
        List.length_map, List.length_range, substFn_range_param] at h1
      rwa [← hlv ψ_P]
    have hw_aux : famAux.p.resSort.eval ψ_P ≠ 0 := by omega
    -- Constructor `cA` at index `k`
    have hk_ctors : k < famAux.ctorsA.length := by omega
    obtain ⟨cA, hcA⟩ : ∃ cA, famAux.ctorsA[k]? = some cA := ⟨_, List.getElem?_eq_getElem hk_ctors⟩
    have hcA_name : cA.1.name = Core.keyOf t (Core.cprjAddr auxIndWit.ip.block 0 k) :=
      hctorNameA k cA hcA
    have hrl_ctor : rl.ctor = cA.1.name := (hrecCtor k rl hrl).trans hcA_name.symm
    have hfindC : env.find? cA.1.name = some (.ctorInfo cA.1 famAux.p.nP cA.2) :=
      (hreadAux.stored.ctor k cA hcA).1
    have hrl_arity := Ix.Kernel.Open.ruleCtor_arity mp.base2.rec_ctors hfindAuxRec hrl_mem
      (hrl_ctor ▸ hfindC)
    have hrl_nP : rl.ctorParams = nP := hrl_arity.1.symm.trans hfam_nP
    have hrl_nF : rl.nfields = cA.2 := hrl_arity.2.1.symm
    -- Pin `restLps = List.range bnl` and `elim ∉ List.range bnl`
    have hrestLps_eq : restLps = List.range bnl := by
      obtain ⟨cvC', nP', nF', hfc', hclps'⟩ := hrec_ctors_lps rl hrl_mem
      rw [hrl_ctor, hfindC] at hfc'
      obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfc')
      exact hclps'.symm.trans ((hAtAux.lpsA cA (List.mem_of_getElem? hcA)).trans hfam_lps)
    have helim_not_mem : elim ∉ List.range bnl := by
      have hnd : cvAuxRec.levelParams.Nodup :=
        (List.Perm.nodup_iff hAuxRec_perm).mpr List.nodup_range
      rw [hcvLps_cons, hrestLps_eq, List.nodup_cons] at hnd
      exact hnd.1
    -- 3. Set up `ρ_call := consList (xs_v ++ (vs_v ++ fs_v)) ρ₀` and bvar spines `xs_A`, `ys_A`
    let ys_v := vs_v ++ fs_v
    let ρ_call := consList (xs_v ++ ys_v) ρ₀
    let xs_A : List AnnotTerm :=
      (List.range xs_v.length).map fun i => .bvar (ys_v.length + xs_v.length - 1 - i)
    let ys_A : List AnnotTerm :=
      (List.range ys_v.length).map fun i => .bvar (ys_v.length - 1 - i)
    have hxsA_map : xs_A.map (interp V ρ_call) = xs_v := bvarsDesc_interp_consList xs_v ys_v ρ₀
    have hysA_map : ys_A.map (interp V ρ_call) = ys_v := bvarsDesc0_interp_consList xs_v ys_v ρ₀
    -- 4. Instantiate `mp.rec_rules ψ_P` at `us := elimLvls`
    have hRecLaw := mp.rec_rules ψ_P auxRecKey cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules
      hfindAuxRec rl hrl_mem hfire_ne
    obtain ⟨Ra, hRa_den, hRa_ok, _, hFire⟩ := hRecLaw.2 elimLvls (by omega)
    -- Show `Level.substFn ψ_P cvAuxRec.levelParams elimLvls` agrees with `origVal ... (ψ_rec ...)`
    have hvalEq : ∀ p ∈ cvAuxRec.levelParams,
        Level.substFn ψ_P cvAuxRec.levelParams elimLvls p =
          origVal cvAuxRec.levelParams (ψ_rec elimLvls bnl ψ_P) p :=
      substFn_eq_origVal_rec hAuxRec_lvls hAuxRec_perm h_elim_len h_elim_drop ψ_P
    have hRec_acval_eq :
        mp.base2.acval auxRecKey (Level.substFn ψ_P cvAuxRec.levelParams elimLvls) =
          mp.base2.acval auxRecKey (origVal cvAuxRec.levelParams (ψ_rec elimLvls bnl ψ_P)) :=
      mp.base2.acval_params auxRecKey _ hfindAuxRec _ _ hvalEq
    have hRec_elim_val : Level.substFn ψ_P cvAuxRec.levelParams elimLvls elim =
        (elimLvls.getD 0 .zero).eval ψ_P := by
      rw [hcvLps_cons]
      cases elimLvls with
      | nil => simp at h_elim_len
      | cons e0 rest => simp [Level.substFn]
    have hmaj_bit_pos : pwBit (Level.substFn ψ_P cvAuxRec.levelParams elimLvls) majBm0.pw ≠ 0 := by
      rw [hmaj0_pw]
      simp only [pwBit, Ix.Kernel.PropWhen.holds_ifAllZero, List.all_cons, List.all_nil,
        Bool.and_true, beq_iff_eq, hRec_elim_val]
      have hne : ¬ (elimLvls.getD 0 .zero).eval ψ_P = 0 := Nat.ne_of_gt h_elim_nz
      simp only [hne, ↓reduceIte]
      omega
    -- 5. Read `cvAuxRec.type[elimLvls]` into `TVa = mkPisAV dsRec restRec` with all bits ≠ 0
    have hmemR : ConstantInfo.recInfo cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules ∈ env.consts :=
      Ix.Kernel.Semantics.Env.find?_mem hfindAuxRec
    obtain ⟨TVa, hTVa_base⟩ := mp.type_reads _ hmemR (Level.substFn ψ_P cvAuxRec.levelParams elimLvls)
    have hTVa_den : denoteMeta mp.base2.acval env ψ_P 0
        (cvAuxRec.type.instantiateLevelParams cvAuxRec.levelParams elimLvls) = some TVa := by
      rw [denotePInstLevels mp.base2 ψ_P cvAuxRec.levelParams elimLvls 0 cvAuxRec.type]
      exact hTVa_base
    have hstripInst := stripPis_instantiateLevelParams cvAuxRec.levelParams elimLvls
      (nP + 1 + anc + 1) hstrip0
    have hstripInst2 : (cvAuxRec.type.instantiateLevelParams cvAuxRec.levelParams elimLvls).stripPis
        (nP + 1 + anc + 1 + 1) =
        some ((pre0.map (fun p => (p.1.instantiateLevelParams cvAuxRec.levelParams elimLvls,
          { p.2 with pw := Level.substPW cvAuxRec.levelParams elimLvls p.2.pw }))) ++
          [(dom0.instantiateLevelParams cvAuxRec.levelParams elimLvls,
            { majBm0 with pw := Level.substPW cvAuxRec.levelParams elimLvls majBm0.pw })],
          body0.instantiateLevelParams cvAuxRec.levelParams elimLvls) :=
      Ix.Kernel.stripPis_append (nP + 1 + anc + 1) hstripInst
        (by simp [Expr.instantiateLevelParams, Expr.stripPis])
    obtain ⟨dsRec, bodyRecA, hTVa_eq, hdsRec_len, hdsRec_bits, _⟩ :=
      denoteMeta_stripPis (nP + 1 + anc + 1 + 1) 0 hstripInst2 hTVa_den
    -- All `nP + 1 + anc + 2` bits of `dsRec` are nonzero!
    have hdsRec_nz : ∀ d ∈ dsRec, d.2.1 ≠ 0 := by
      intro d hd
      have hmem : d.2.1 ∈ dsRec.map (fun x => x.2.1) := List.mem_map_of_mem hd
      rw [hdsRec_bits] at hmem
      obtain ⟨bm, hbm, hbit⟩ := List.mem_map.mp hmem
      rw [← hbit]
      rcases List.mem_append.mp hbm with hpre | hmaj
      · obtain ⟨bm0, hbm0, rfl⟩ := List.mem_map.mp hpre
        have hpw : bm0.2.pw = majBm0.pw := hpre0_pw bm0 hbm0
        rw [hpw]
        simpa [pwBit_substPW] using hmaj_bit_pos
      · obtain rfl := List.mem_singleton.mp hmaj
        simpa [pwBit_substPW] using hmaj_bit_pos
    -- 6. Evaluate `aux.c_k` on `ys_A` and build `TeleFitPA` on `TVja` and `TVa`!
    let usj : List KLevel := (List.range bnl).map .param
    have hcA_lps : cA.1.levelParams = List.range bnl := (hAtAux.lpsA cA (List.mem_of_getElem? hcA)).trans hfam_lps
    have hsubst_cA : Level.substFn ψ_P cA.1.levelParams usj = ψ_P := by
      rw [hcA_lps]; exact substFn_range_param bnl ψ_P
    have hctor_read := hAtAux.ctor k cA hcA
    have hTVja_base : denoteMeta mp.base2.acval env ψ_P 0 cA.1.type =
        some (mkPisAV (dsF k ψ_P) (ctorBodyAVI mp.base2 famAux.p.cvT.name famAux.p.nP cA.2 ψ_P (esF k ψ_P))) :=
      hctor_read.read ψ_P
    have hTVja_den : denoteMeta mp.base2.acval env ψ_P 0
        (cA.1.type.instantiateLevelParams cA.1.levelParams usj) =
        some (mkPisAV (dsF k ψ_P) (ctorBodyAVI mp.base2 famAux.p.cvT.name famAux.p.nP cA.2 ψ_P (esF k ψ_P))) := by
      rw [denotePInstLevels mp.base2 ψ_P cA.1.levelParams usj 0 cA.1.type, hsubst_cA]
      exact hTVja_base
    -- Lift `hfitC` from `ρ₀` to `ρ_call` (since `dsF k ψ_P` is closed via `hctor_read.domsBelow`!)
    have hfitC_call : SpineFit ρ_call ((dsF k ψ_P).map (·.2.2)) (ys_A.map (interp V ρ_call)) := by
      rw [hysA_map]
      rw [h_origAux] at hfitC
      -- `DomsBelow 0 (dsF k ψ_P)` gives `SpineFit` environment independence at 0!
      have hgo : ∀ (ds : List (Nat × Nat × AnnotTerm)) (pre vs : List V),
          Ix.Kernel.Semantics.DomsBelow pre.length ds →
          SpineFit (consList pre ρ₀) (ds.map (·.2.2)) vs →
          SpineFit (consList pre ρ_call) (ds.map (·.2.2)) vs := by
        intro ds
        induction ds with
        | nil => intro _ vs _ h; cases vs with | nil => trivial | cons _ _ => exact h.elim
        | cons d ds ih =>
          intro pre vs hdb hsp
          cases vs with
          | nil => exact hsp.elim
          | cons v vs =>
            obtain ⟨hv, hrest⟩ := hsp
            have heq := Ix.Kernel.Semantics.interp_congr_below V d.2.2 pre.length
              (consList pre ρ₀) (consList pre ρ_call) hdb.1 fun i hi => by
                rw [consList_getElem pre ρ₀ i hi, consList_getElem pre ρ_call i hi]
            refine ⟨heq ▸ hv, ?_⟩
            have h2 := ih (pre ++ [v]) vs (by simpa [List.length_append] using hdb.2)
              (by simpa [consList_append] using hrest)
            simpa [consList_append] using h2
      exact hgo (dsF k ψ_P) [] ys_v (hctor_read.below ψ_P) hfitC
    obtain ⟨restC, hfit_TVja, _, hmk_restC⟩ :=
      teleFitPA_of_mkPisAV_spineFit (dsF k ψ_P)
        (ctorBodyAVI mp.base2 famAux.p.cvT.name famAux.p.nP cA.2 ψ_P (esF k ψ_P)) ys_A ρ_call hfitC_call
    -- Evaluate `ctorApp_A = mkAppN (acval cA.1.name ψ_P) ys_A` via `sumMkAV_fold`
    let ctorApp_A := AnnotTerm.mkAppN
      (mp.base2.acval cA.1.name (Level.substFn ψ_P cA.1.levelParams usj)) ys_A
    have hctor_val : interp V ρ_call ctorApp_A = inj k (mkTower (fs_v ++ [pt])) := by
      show interp V ρ_call (AnnotTerm.mkAppN (mp.base2.acval cA.1.name _) ys_A) = _
      rw [interp_mkAppN_foldl, hysA_map, hsubst_cA, hAtAux.leafC k cA hcA ψ_P]
      have hds_split : dsF k ψ_P = (dsF k ψ_P).take nP ++ (dsF k ψ_P).drop nP := (List.take_append_drop nP _).symm
      have hfitC_sp : SpineFit ρ_call ((dsF k ψ_P).map (·.2.2)) (vs_v ++ fs_v) := by
        simpa [hysA_map, ys_v] using hfitC_call
      have hlen_take : ((dsF k ψ_P).take nP).length = nP := by
        have := hctor_read.len ψ_P; rw [List.length_take]; omega
      have hsp1 : SpineFit ρ_call (((dsF k ψ_P).take nP).map (·.2.2)) vs_v := by
        rw [hds_split, List.map_append] at hfitC_sp
        exact ((spineFit_append_iff (by rw [List.length_map, hlen_take, hvs_len])).mp hfitC_sp).1
      have hsp2 : SpineFit (consList vs_v ρ_call) (((dsF k ψ_P).drop nP).map (·.2.2)) fs_v := by
        rw [hds_split, List.map_append] at hfitC_sp
        exact ((spineFit_append_iff (by rw [List.length_map, hlen_take, hvs_len])).mp hfitC_sp).2
      have hsat_p : Sat V (((ppsAll ψ_P).take famAux.p.nP).map (·.2.2)).reverse (consList vs_v ρ_call) := by
        rw [hAtAux.paramsIff k cA hcA ψ_P, hfam_nP]
        have hs := Ix.Kernel.Model.sat_of_spineFit (Δ₀ := []) (Ix.Kernel.Semantics.Sat_nil V ρ_call) hsp1
        simpa using hs
      have hfr := hAtAux.frames ψ_P (consList vs_v ρ_call) hsat_p
      have hokFss : SumFieldsOkB (famAux.p.resSort.eval ψ_P) (consList vs_v ρ_call)
          (Ix.Kernel.Model.fssOfR famAux.p.nP
            (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)) := by
        intro Fs hFs
        obtain ⟨j, hjlt, rfl⟩ := List.mem_iff_getElem.mp hFs
        have hjlt' : j < famAux.ctorsA.length := by
          simpa [Ix.Kernel.Model.fssOfR, Ix.Kernel.Model.fixCtorDataList_length] using hjlt
        have hget : (Ix.Kernel.Model.fssOfR famAux.p.nP
            (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)).getD j [] =
            (Ix.Kernel.Model.fssOfR famAux.p.nP
              (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))[j] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt]
        rw [← hget]
        exact (hfr.2.2.1 j hjlt').1
      have hokU : SumFieldsOkB (famAux.p.resSort.eval ψ_P) (consList vs_v ρ_call)
          (Ix.Kernel.Semantics.uChains (Ix.Kernel.Model.fssOfR famAux.p.nP
            (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))) :=
        Ix.Kernel.Semantics.SumFieldsOkB_uChains hokFss
      have hjU : (Ix.Kernel.Semantics.uChains (Ix.Kernel.Model.fssOfR famAux.p.nP
          (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)))[k]? =
          some (((dsF k ψ_P).drop nP).map (·.2.2) ++ [Ix.Kernel.Semantics.idxEqAV []]) := by
        rw [Ix.Kernel.Semantics.uChains_getElem?, Ix.Kernel.Model.fssOfR_getElem?,
          Ix.Kernel.Model.fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0 k, hcA]
        simp [hfam_nP]
      have hfold := sumMkAV_fold hw_aux hsp1 hsp2 hokU hjU
      rw [List.take_append_drop] at hfold
      rw [hfam_nP] at hfold ⊢
      exact hfold
    -- Build `TeleFitPA` on `TVa` along `xs_A ++ [ctorApp_A]`
    have hF_mem : interp V ρ_call
        (mp.base2.acval auxRecKey (Level.substFn ψ_P cvAuxRec.levelParams elimLvls)) ∈ˢ
        interp V ρ_call TVa := by
      have hnameR := Ix.Kernel.Semantics.Env.find?_name hfindAuxRec
      simpa [hnameR] using mp.mem_type _ hmemR (Level.substFn ψ_P cvAuxRec.levelParams elimLvls) TVa hTVa_base ρ_call
    have hApp_call : AppChainOk
        (interp V ρ_call (mp.base2.acval auxRecKey (Level.substFn ψ_P cvAuxRec.levelParams elimLvls)))
        ((xs_A ++ [ctorApp_A]).map (interp V ρ_call)) := by
      rw [hRec_acval_eq,
        closed_interp_env (mp.base2.acval_closed _ _) ρ_call ρ₀,
        List.map_append, List.map_singleton, hxsA_map, hctor_val]
      exact hApp
    rw [hTVa_eq] at hF_mem
    obtain ⟨restR, hfit_TVa, hsp_TVa, -, -⟩ :=
      teleFitPA_of_mkPisAV_appChainOk_pos dsRec bodyRecA (xs_A ++ [ctorApp_A])
        (interp V ρ_call (mp.base2.acval auxRecKey (Level.substFn ψ_P cvAuxRec.levelParams elimLvls)))
        ρ_call hdsRec_nz (by simp [xs_A, hxs_len, hdsRec_len]) hF_mem hApp_call
    rw [← hTVa_eq] at hfit_TVa
    -- 7. Discharge `IotaIndexPin` via `aux_fibre_disjoint`
    have hPin : IotaIndexPin (V := V) ρ_call restC rl.ctorParams (nP + 1 + anc + 1) (nP + 1 + anc) xs_A := by
      -- Unpack `restC = mkAppN f' es'` from `hmk_restC`
      obtain ⟨f', es', hrestC_eq, hes'_len, hf'_eq, hes'_eq⟩ := hmk_restC
        (mp.base2.acval famAux.p.cvT.name ψ_P)
        (Ix.Kernel.Model.paramBvarsAt famAux.p.nP (famAux.p.nP + cA.2) ++ esF k ψ_P) rfl
      have hesF_len : (esF k ψ_P).length = 1 := by
        rw [hctor_read.lenE ψ_P, hfam_nIdx]
      have hpb_len : (Ix.Kernel.Model.paramBvarsAt famAux.p.nP (famAux.p.nP + cA.2)).length = nP := by
        simp [Ix.Kernel.Model.paramBvarsAt, hfam_nP]
      have hes'_len_eq : es'.length = rl.ctorParams + 1 := by
        rw [hes'_len, List.length_append, hpb_len, hesF_len, hrl_nP]
      refine ⟨f', es', hrestC_eq, Or.inr (by omega), fun i hi => ?_⟩
      have hi0 : i = 0 := by omega
      subst hi0
      -- `idx_c` = `interp ρ_call (es'.getD nP default)` and `idx_r` = `interp ρ_call (xs_A.getD (nP + 1 + anc) default)`
      let idx_c := interp V ρ_call (es'.getD (rl.ctorParams + 0) default)
      let idx_r := interp V ρ_call (xs_A.getD (nP + 1 + anc + 0) default)
      change idx_c = idx_r
      -- Recover parameter fit `hsat_p` and `hfr` at `ρp := consList vs_v ρ_call`
      have hds_split : dsF k ψ_P = (dsF k ψ_P).take nP ++ (dsF k ψ_P).drop nP := (List.take_append_drop nP _).symm
      have hfitC_sp : SpineFit ρ_call ((dsF k ψ_P).map (·.2.2)) (vs_v ++ fs_v) := by
        simpa [hysA_map, ys_v] using hfitC_call
      have hlen_take : ((dsF k ψ_P).take nP).length = nP := by
        have := hctor_read.len ψ_P; rw [List.length_take]; omega
      have hsp1 : SpineFit ρ_call (((dsF k ψ_P).take nP).map (·.2.2)) vs_v := by
        rw [hds_split, List.map_append] at hfitC_sp
        exact ((spineFit_append_iff (by rw [List.length_map, hlen_take, hvs_len])).mp hfitC_sp).1
      have hsp2 : SpineFit (consList vs_v ρ_call) (((dsF k ψ_P).drop nP).map (·.2.2)) fs_v := by
        rw [hds_split, List.map_append] at hfitC_sp
        exact ((spineFit_append_iff (by rw [List.length_map, hlen_take, hvs_len])).mp hfitC_sp).2
      have hsat_p : Sat V (((ppsAll ψ_P).take famAux.p.nP).map (·.2.2)).reverse
          (consList vs_v ρ_call) := by
        rw [hAtAux.paramsIff k cA hcA ψ_P, hfam_nP]
        have hs := Ix.Kernel.Model.sat_of_spineFit (Δ₀ := []) (Ix.Kernel.Semantics.Sat_nil V ρ_call) hsp1
        simpa using hs
      have hsp_pps : SpineFit ρ_call (((ppsAll ψ_P).take famAux.p.nP).map (·.2.2)) vs_v := by
        have hlenP : (((ppsAll ψ_P).take famAux.p.nP).map (·.2.2)).length = vs_v.length := by
          have := hAtAux.former.len ψ_P
          rw [List.length_map, List.length_take, this, hfam_nP, hfam_nIdx, hvs_len]; omega
        exact spineFit_of_sat_consList hlenP hsat_p
      have hfr := hAtAux.frames ψ_P (consList vs_v ρ_call) hsat_p
      have hIds_len : (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)).length = 1 := by
        have := hAtAux.former.len ψ_P
        rw [List.length_map, List.length_drop, this, hfam_nIdx]; omega
      -- 7a. `idx_c` fits `Ids` and `ctorApp_A ∈ˢ fixFamI ... [idx_c]`
      have hidx_c_eq : idx_c = interp V (consList fs_v (consList vs_v ρ_call)) ((esF k ψ_P).getD 0 default) := by
        have h0 := hes'_eq nP (by rw [List.length_append, hpb_len, hesF_len]; omega)
        simp only [idx_c, Nat.add_zero, hrl_nP]
        rw [h0, hysA_map, consList_append]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hpb_len]),
          hpb_len, Nat.sub_self, ← List.getD_eq_getElem?_getD]
      have hidx_c_fit : SpineFit (consList vs_v ρ_call) (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)) [idx_c] := by
        have hfr_k := (hfr.2.2.1 k hk_ctors).2 fs_v (by
          have hget : (Ix.Kernel.Model.fssOfR famAux.p.nP
              (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)).getD k [] =
              ((dsF k ψ_P).drop nP).map (·.2.2) := by
            rw [List.getD_eq_getElem?_getD, Ix.Kernel.Model.fssOfR_getElem?,
              Ix.Kernel.Model.fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0 k, hcA]
            simp [hfam_nP]
          rwa [hget])
        have heget : (Ix.Kernel.Model.essOfR
            (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)).getD k [] =
            esF k ψ_P := by
          rw [List.getD_eq_getElem?_getD, Ix.Kernel.Model.essOfR_getElem?,
            Ix.Kernel.Model.fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0 k, hcA]
          simp
        have hsp_iv := hfr_k.2
        rw [heget] at hsp_iv
        have hiv_eq : idxValsAt (consList vs_v ρ_call) (esF k ψ_P) fs_v = [idx_c] := by
          cases he : esF k ψ_P with
          | nil => rw [he] at hesF_len; cases hesF_len
          | cons e0 er =>
            cases er with
            | cons _ _ => rw [he] at hesF_len; simp at hesF_len
            | nil =>
              simp only [idxValsAt, List.map_cons, List.map_nil, List.cons.injEq, and_true]
              rw [hidx_c_eq, he]; rfl
        rwa [hiv_eq] at hsp_iv
      have hctor_mem_c : interp V ρ_call ctorApp_A ∈ˢ
          SetTheory.app (fixFamI (uAV ψ_P) (famAux.p.resSort.eval ψ_P) (consList vs_v ρ_call)
            (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)) 1
            (Ix.Kernel.Model.rssOfK ksF famAux.ctorsA.length)
            (Ix.Kernel.Model.tlssOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
            (Ix.Kernel.Model.eissOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
            (fssZ ψ_P)
            (Ix.Kernel.Model.essOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)))
            (tupW (uAV ψ_P) [idx_c]) := by
        have hmemC_ci : ConstantInfo.ctorInfo cA.1 famAux.p.nP cA.2 ∈ env.consts :=
          Ix.Kernel.Semantics.Env.find?_mem hfindC
        have hok_TVja : WellDenotedV V ρ_call (mkPisAV (dsF k ψ_P)
            (ctorBodyAVI mp.base2 famAux.p.cvT.name famAux.p.nP cA.2 ψ_P (esF k ψ_P))) :=
          mp.type_wellDenotedV _ hmemC_ci ψ_P _ hTVja_base ρ_call
        have hok_cA : WellDenotedV V ρ_call (mp.base2.acval cA.1.name ψ_P) :=
          ⟨mp.base2.acval_wellDenoted _ ψ_P ρ_call, mp.acval_validV _ ψ_P ρ_call⟩
        have hmem_cA : interp V ρ_call (mp.base2.acval cA.1.name ψ_P) ∈ˢ
            interp V ρ_call (mkPisAV (dsF k ψ_P)
              (ctorBodyAVI mp.base2 famAux.p.cvT.name famAux.p.nP cA.2 ψ_P (esF k ψ_P))) :=
          mp.mem_type _ hmemC_ci ψ_P _ hTVja_base ρ_call
        have hmem_res : interp V ρ_call ctorApp_A ∈ˢ interp V ρ_call restC := by
          have h1 := (Ix.Kernel.Model.Rules.mkAppN_of_fitA ys_A hok_TVja hok_cA
            (by simpa only [Nat.zero_add] using bvarsDesc_wellDenotedV ρ_call 0 ys_v.length)
            hmem_cA hfit_TVja).2
          simpa [ctorApp_A, hsubst_cA] using h1
        have hrestC_val : interp V ρ_call restC =
            (vs_v ++ [idx_c]).foldl SetTheory.app (interp V ρ_call (mp.base2.acval famAux.p.cvT.name ψ_P)) := by
          rw [hrestC_eq, interp_mkAppN_foldl, hf'_eq,
            closed_interp_env (mp.base2.acval_closed _ _) (consList (ys_A.map (interp V ρ_call)) ρ_call) ρ_call]
          congr 1
          apply List.ext_getElem (by simp [hes'_len_eq, hrl_nP, hvs_len])
          intro m hm1 hm2
          simp only [List.getElem_map]
          by_cases hmn : m < nP
          · have hgm := hes'_eq m (by rw [List.length_append, hpb_len, hesF_len]; omega)
            have h1 : interp V ρ_call es'[m] = interp V ρ_call (es'.getD m default) := by
              simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at hm1; omega)]
            rw [h1, hgm, hysA_map, List.getElem_append_left (by omega)]
            have hpb : (Ix.Kernel.Model.paramBvarsAt famAux.p.nP (famAux.p.nP + cA.2) ++ esF k ψ_P).getD m default =
                .bvar (famAux.p.nP + cA.2 - 1 - m) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hpb_len]; exact hmn)]
              simp [Ix.Kernel.Model.paramBvarsAt, hfam_nP, hmn]
            rw [hpb, interp, consList_getElem (vs_v ++ fs_v) ρ_call _ (by simp [hvs_len, hfs_len, hrl_nF, hfam_nP]; omega)]
            have hidx : (vs_v ++ fs_v).length - 1 - (famAux.p.nP + cA.2 - 1 - m) = m := by
              simp [hvs_len, hfs_len, hrl_nF, hfam_nP]; omega
            simp only [hidx]
            exact List.getElem_append_left (by omega : m < vs_v.length)
          · have hm_eq : m = nP := by simp [hes'_len_eq, hrl_nP] at hm1; omega
            subst m
            rw [List.getElem_append_right (by omega)]
            simp only [hvs_len, Nat.sub_self, List.getElem_cons_zero]
            simp only [idx_c, Nat.add_zero, hrl_nP, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show nP < es'.length by rw [hes'_len_eq, hrl_nP]; omega),
              Option.getD_some]
        rw [hrestC_val, hAtAux.leafT ψ_P] at hmem_res
        have hfold := nativeTyAVI_fold_at hfr.1 hsp_pps hidx_c_fit
        rw [hfold, hIds_len] at hmem_res
        exact hmem_res
      -- 7b. `idx_r` fits `Ids` and `ctorApp_A ∈ˢ fixFamI ... [idx_r]` (from `hsp_TVa`'s last slot `majDom`!)
      have hctor_mem_maj : interp V ρ_call ctorApp_A ∈ˢ
          interp V (consList xs_v ρ_call) ((dsRec.getD (nP + 1 + anc + 1) default).2.2) := by
        have hsp' : SpineFit ρ_call
            ((dsRec.take (nP + 1 + anc + 1)).map (·.2.2) ++ (dsRec.drop (nP + 1 + anc + 1)).map (·.2.2))
            (xs_A.map (interp V ρ_call) ++ [ctorApp_A].map (interp V ρ_call)) := by
          rw [← List.map_append, List.take_append_drop, ← List.map_append]
          exact hsp_TVa
        have hlen1 : ((dsRec.take (nP + 1 + anc + 1)).map (·.2.2)).length =
            (xs_A.map (interp V ρ_call)).length := by
          simp [xs_A, hxs_len, hdsRec_len]
        have hlast := ((spineFit_append_iff hlen1).mp hsp').2
        rw [hxsA_map] at hlast
        have hdrop : (dsRec.drop (nP + 1 + anc + 1)).map (·.2.2) =
            [(dsRec.getD (nP + 1 + anc + 1) default).2.2] := by
          have hlt : nP + 1 + anc + 1 < dsRec.length := by omega
          rw [List.drop_eq_getElem_cons hlt, List.drop_eq_nil_of_le (by omega)]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        rw [hdrop, List.map_singleton] at hlast
        exact hlast.1
      -- Identify `(dsRec.getD (nP + 1 + anc + 1) default).2.2` as `denoteMeta` of `majDom`!
      have hmajDom_den : denoteMeta mp.base2.acval env ψ_P (nP + 1 + anc + 1)
          (openDummiesP (nP + 1 + anc + 1) 0 0
            (dom0.instantiateLevelParams cvAuxRec.levelParams elimLvls)) =
          some ((dsRec.getD (nP + 1 + anc + 1) default).2.2) := by
        -- From `denoteMeta_stripPis (nP + 1 + anc + 1) 0 hstripInst hTVa_den`
        obtain ⟨dsPre, majPiA, hTVa_eq1, hdsPre_len, -, hmajPi_den⟩ :=
          denoteMeta_stripPis (nP + 1 + anc + 1) 0 hstripInst hTVa_den
        -- Directly compare `mkPisAV dsRec bodyRecA = mkPisAV dsPre majPiA`!
        have hgo_for : ∀ (n d c : Nat) (t b : KExpr) (m : BinderMeta),
            ∃ b', openDummiesP n d c (.forallE t b m) = .forallE (openDummiesP n d c t) b' m := by
          intro n
          induction n with
          | zero => intro d c t b m; exact ⟨b, rfl⟩
          | succ n ih =>
            intro d c t b m
            simp only [openDummiesP, Expr.instantiate1]
            exact ih (d + 1) c _ _ m
        obtain ⟨b', hb'⟩ := hgo_for (nP + 1 + anc + 1) 0 0
          (dom0.instantiateLevelParams cvAuxRec.levelParams elimLvls)
          (body0.instantiateLevelParams cvAuxRec.levelParams elimLvls)
          { majBm0 with pw := Level.substPW cvAuxRec.levelParams elimLvls majBm0.pw }
        simp only [Expr.instantiateLevelParams, Nat.zero_add] at hmajPi_den
        rw [hb'] at hmajPi_den
        obtain ⟨ta, ba, hta, hmajPi_eq⟩ : ∃ ta ba,
            denoteMeta mp.base2.acval env ψ_P (nP + 1 + anc + 1)
              (openDummiesP (nP + 1 + anc + 1) 0 0 (dom0.instantiateLevelParams cvAuxRec.levelParams elimLvls)) = some ta ∧
            AnnotTerm.pi 0 (pwBit ψ_P (Level.substPW cvAuxRec.levelParams elimLvls majBm0.pw)) ta ba = majPiA := by
          simp only [denoteMeta] at hmajPi_den
          cases hta : denoteMeta mp.base2.acval env ψ_P (nP + 1 + anc + 1)
              (openDummiesP (nP + 1 + anc + 1) 0 0 (dom0.instantiateLevelParams cvAuxRec.levelParams elimLvls)) with
          | none => simp [hta] at hmajPi_den
          | some ta =>
            rw [hta] at hmajPi_den
            cases hba : denoteMeta mp.base2.acval env ψ_P (nP + 1 + anc + 1 + 1)
                (b'.instantiate1 (Expr.fvar (nP + 1 + anc + 1)
                  (openDummiesP (nP + 1 + anc + 1) 0 0 (dom0.instantiateLevelParams cvAuxRec.levelParams elimLvls)))) with
            | none => simp [hba] at hmajPi_den
            | some ba =>
              rw [hba] at hmajPi_den
              exact ⟨ta, ba, rfl, Option.some.inj hmajPi_den⟩
        -- Match `dsRec` with `dsPre ++ [(0, _, ta)]` via `mkPisAV` injectivity
        have hds_eq : (dsRec.getD (nP + 1 + anc + 1) default).2.2 = ta := by
          have heq : mkPisAV dsRec bodyRecA = mkPisAV dsPre majPiA := hTVa_eq.symm.trans hTVa_eq1
          rw [← hmajPi_eq] at heq
          have hgo : ∀ (l1 l2 : List (Nat × Nat × AnnotTerm)) (b1 b2 A : AnnotTerm) (u v : Nat),
              l1.length = l2.length + 1 →
              mkPisAV l1 b1 = mkPisAV l2 (.pi u v A b2) →
              (l1.getD l2.length default).2.2 = A := by
            intro l1 l2
            induction l2 generalizing l1 with
            | nil =>
              intro b1 b2 A u v hlen hmk
              cases l1 with
              | nil => simp at hlen
              | cons d l1' =>
                cases l1' with
                | cons _ _ => simp at hlen
                | nil =>
                  simp only [mkPisAV] at hmk
                  exact (AnnotTerm.pi.inj hmk).2.2.1
            | cons d2 l2 ih =>
              intro b1 b2 A u v hlen hmk
              cases l1 with
              | nil => simp at hlen
              | cons d1 l1' =>
                simp only [mkPisAV] at hmk
                have htail := (AnnotTerm.pi.inj hmk).2.2.2
                simpa using ih l1' b1 b2 A u v (by simpa using hlen) htail
          have h1 := hgo dsRec dsPre bodyRecA ba ta 0 _ (by omega) heq
          rwa [hdsPre_len] at h1
        rwa [hds_eq]
      -- Now evaluate `majDom` via `hmajDom`, `hmajLvls`, `hmajArgs_pref`, `hmajArgs_idx`!
      have hdom0_inst_eq :
          denoteMeta mp.base2.acval env ψ_P (nP + 1 + anc + 1)
            (openDummiesP (nP + 1 + anc + 1) 0 0
              (dom0.instantiateLevelParams cvAuxRec.levelParams elimLvls)) =
          denoteMeta mp.base2.acval env (ψ_rec elimLvls bnl ψ_P) (nP + 1 + anc + 1)
            (openDummiesP (nP + 1 + anc + 1) 0 0 majDom) := by
        -- `openDummiesP` commutes with `instantiateLevelParams` (dummy fvars have `.sort .zero`!)
        have hcomm : ∀ (n d c : Nat) (ps : List LevelParam) (us : List KLevel) (e : KExpr),
            openDummiesP n d c (e.instantiateLevelParams ps us) =
              (openDummiesP n d c e).instantiateLevelParams ps us := by
          intro n
          induction n with
          | zero => intro _ _ _ _ _; rfl
          | succ n ih =>
            intro d c ps us e
            simp only [openDummiesP]
            have hinst : (e.instantiateLevelParams ps us).instantiate1 (.fvar d (.sort .zero)) (c + n) =
                (e.instantiate1 (.fvar d (.sort .zero)) (c + n)).instantiateLevelParams ps us :=
              (Ix.Kernel.Expr.instantiateLevelParams_instantiate1 ps us (d := d) (ty := .sort .zero) e (c + n)).symm
            rw [hinst, ih]
        rw [hcomm, denotePInstLevels mp.base2 ψ_P cvAuxRec.levelParams elimLvls]
        rw [← hdom0_eq, Core.posOf, hcomm, denotePInstLevels mp.base2 (ψ_rec elimLvls bnl ψ_P)
          cvAuxRec.levelParams (Core.posLevels cvAuxRec.levelParams)]
        have hdef_dom0 : (openDummiesP (nP + 1 + anc + 1) 0 0 dom0).allLevelParamsDefined
            cvAuxRec.levelParams = true := by
          have hc := mp.base2.wf _ hmemR
          have hdefT : cvAuxRec.type.allLevelParamsDefined cvAuxRec.levelParams = true := hc.2.1
          have hgo1 : ∀ (n : Nat) {e : KExpr} {bs : List (KExpr × BinderMeta)} {d0 b0 : KExpr} {m0 : BinderMeta},
              e.allLevelParamsDefined cvAuxRec.levelParams = true →
              e.stripPis n = some (bs, .forallE d0 b0 m0) →
              d0.allLevelParamsDefined cvAuxRec.levelParams = true := by
            intro n
            induction n with
            | zero =>
              intro e bs d0 b0 m0 hd hs
              simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
              rw [hs.2] at hd
              simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
              exact hd.1.1
            | succ n ih =>
              intro e bs d0 b0 m0 hd hs
              cases e with
              | forallE t b m =>
                simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
                simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
                obtain ⟨⟨_, rem⟩, hsb, hpair⟩ := hs
                injection hpair with _ hr
                dsimp only at hr
                rw [hr] at hsb
                exact ih hd.1.2 hsb
              | _ => simp [Expr.stripPis] at hs
          have hdef_d0 := hgo1 (nP + 1 + anc + 1) hdefT hstrip0
          have hgo2 : ∀ (n d c : Nat) (e : KExpr),
              e.allLevelParamsDefined cvAuxRec.levelParams = true →
              (openDummiesP n d c e).allLevelParamsDefined cvAuxRec.levelParams = true := by
            intro n
            induction n with
            | zero => intro _ _ _ h; exact h
            | succ n ih =>
              intro d c e h
              simp only [openDummiesP]
              exact ih (d + 1) c _ (Ix.Kernel.Expr.allLevelParamsDefined_instantiate1 (by rfl) (c + n) h)
          exact hgo2 (nP + 1 + anc + 1) 0 0 dom0 hdef_d0
        exact Ix.Kernel.Model.denoteMeta_params_ext mp.base2 hvalEq _ _ hdef_dom0
      rw [hdom0_inst_eq, hmajDom, openDummiesP_mkAppN, openDummiesP_const] at hmajDom_den
      obtain ⟨faM, argsMA, hfaM, hspMA, hmajA_eq⟩ := denoteMeta_mkAppN_inv hmajDom_den
      -- `faM = mp.base2.acval auxKey ψ_P`
      have hfaM_eq : faM = mp.base2.acval famAux.p.cvT.name ψ_P := by
        simp only [denoteMeta, auxIndWit.hfind] at hfaM
        have hmlen : majLvls.length = auxIndWit.cv.levelParams.length := by
          have := (lvEqList_getElem hmajLvls).1; simp [hauxInd_lvls] at this ⊢; exact this
        simp only [ConstantInfo.toConstantVal, hmlen, ↓reduceIte, Option.some.injEq] at hfaM
        rw [← hfaM, hnameAux]
        have hcvS_eq : famAux.cvS = auxIndWit.cv := famRead_cvS_eq hreadAux hnameAux auxIndWit.hfind
        have hlpsA : auxIndWit.cv.levelParams = List.range bnl := by
          rw [← hcvS_eq]; exact hreadAux.lps.trans hfam_lps
        have hsub : ∀ p ∈ auxIndWit.cv.levelParams,
            Level.substFn (ψ_rec elimLvls bnl ψ_P) auxIndWit.cv.levelParams majLvls p = ψ_P p := by
          intro p hp
          rw [substFn_eq_of_lvEqList hmajLvls (ψ_rec elimLvls bnl ψ_P)]
          rw [hlpsA] at hp ⊢
          have hplt : p < bnl := List.mem_range.mp hp
          have hget := substFn_getElem (ψ := ψ_rec elimLvls bnl ψ_P)
            (List.range bnl) ((List.range bnl).map fun m => .param (1 + m))
            List.nodup_range (by simp) p (by simp [hplt])
          have hne0 : (1 + p = 0) = False := eq_false (Nat.one_add p ▸ Nat.succ_ne_zero p)
          have hlt1 : (1 + p < bnl + 1) = True := eq_true (Nat.add_comm 1 p ▸ Nat.add_lt_add_right hplt 1)
          simp only [List.getElem_range, List.getElem_map, Level.eval, ψ_rec,
            hne0, hlt1, ↓reduceIte, Nat.add_sub_cancel_left] at hget
          exact hget
        exact mp.base2.acval_params auxKey _ auxIndWit.hfind _ _ hsub
      -- `argsMA.map (interp (consList xs_v ρ_call)) = vs_v ++ [idx_r]`
      have hargsMA_map : argsMA.map (interp V (consList xs_v ρ_call)) = vs_v ++ [idx_r] := by
        have hlenMA : argsMA.length = nP + 1 := by
          have := denoteMetaSpine_length_eq hspMA; simpa [hmajArgs_len] using this.symm
        apply List.ext_getElem (by simp [hlenMA, hvs_len])
        intro m hm1 hm2
        simp only [List.getElem_map]
        by_cases hmn : m < nP
        · have hsem := forall₂_getElem hmajArgs_pref m (by simp; omega) (by simp; omega)
          simp only [List.getElem_take, List.getElem_map, List.getElem_range] at hsem
          have hm_get : (majArgs.map (openDummiesP (nP + 1 + anc + 1) 0 0))[m]? =
              some (openDummiesP (nP + 1 + anc + 1) 0 0 (majArgs[m]'(by omega))) := by
            simp [List.getElem?_eq_getElem (show m < majArgs.length by omega)]
          obtain ⟨v, hv, hden_m⟩ := DenoteMetaSpine.getElem? hspMA hm_get
          rw [List.getElem?_eq_getElem (by simp at hm1; omega)] at hv
          have hv_eq : argsMA[m]'(by simp at hm1; omega) = v := Option.some.inj hv
          have hbv := denoteMeta_openDummiesP_bvar (acval := mp.base2.acval) (env := env)
            (φ := ψ_rec elimLvls bnl ψ_P) (d := 0) (n := nP + 1 + anc + 1)
            (i := nP + 1 + anc + 1 - 1 - m) (by omega)
          simp only [Nat.zero_add] at hbv
          rw [denoteMeta_exprSemEq (exprSemEq_openDummiesP hsem _ 0 0), hbv] at hden_m
          have ha_eq : argsMA[m]'(by simp at hm1; omega) = .bvar (nP + 1 + anc + 1 - 1 - m) :=
            hv_eq.trans (Option.some.inj hden_m).symm
          rw [ha_eq, interp, consList_getElem xs_v ρ_call _ (by omega)]
          have hidx : xs_v.length - 1 - (nP + 1 + anc + 1 - 1 - m) = m := by omega
          have h3 := congrArg (fun l => l[m]?) hxs_pref
          simp only [List.getElem?_take, hmn, ↓reduceIte,
            List.getElem?_eq_getElem (show m < xs_v.length by omega),
            List.getElem?_eq_getElem (show m < vs_v.length by omega)] at h3
          rw [List.getElem_append_left (by omega)]
          simp only [hidx]
          exact Option.some.inj h3
        · have hm_eq : m = nP := by simp [hlenMA] at hm1; omega
          subst m
          have hm_get : (majArgs.map (openDummiesP (nP + 1 + anc + 1) 0 0))[nP]? =
              some (openDummiesP (nP + 1 + anc + 1) 0 0 (.bvar 0)) := by
            simp [List.getElem?_map, hmajArgs_idx]
          obtain ⟨v, hv, hden_m⟩ := DenoteMetaSpine.getElem? hspMA hm_get
          rw [List.getElem?_eq_getElem (by omega)] at hv
          have hv_eq : argsMA[nP]'(by omega) = v := Option.some.inj hv
          have hbv := denoteMeta_openDummiesP_bvar (acval := mp.base2.acval) (env := env)
            (φ := ψ_rec elimLvls bnl ψ_P) (d := 0) (n := nP + 1 + anc + 1) (i := 0) (by omega)
          simp only [Nat.zero_add] at hbv
          rw [hbv] at hden_m
          have ha_eq : argsMA[nP]'(by omega) = .bvar 0 := hv_eq.trans (Option.some.inj hden_m).symm
          rw [ha_eq, interp, consList_getElem xs_v ρ_call 0 (by omega)]
          rw [List.getElem_append_right (by omega)]
          simp only [hvs_len, Nat.sub_self, List.getElem_cons_zero]
          have hget_last : xs_A.getD (nP + 1 + anc + 0) default =
              xs_A[nP + 1 + anc]'(by simp [xs_A, hxs_len]) := by
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show nP + 1 + anc < xs_A.length by simp [xs_A, hxs_len])]
          have hx_last := congrArg (fun l => l[nP + 1 + anc]?) hxsA_map
          simp only [List.getElem?_map,
            List.getElem?_eq_getElem (show nP + 1 + anc < xs_A.length by simp [xs_A, hxs_len]),
            List.getElem?_eq_getElem (show nP + 1 + anc < xs_v.length by omega),
            Option.map_some, Option.some.injEq] at hx_last
          have hidx_r_eq : idx_r = xs_v[nP + 1 + anc]'(by omega) := by
            show interp V ρ_call (xs_A.getD (nP + 1 + anc + 0) default) = _
            rw [hget_last]; exact hx_last
          rw [hidx_r_eq]
          congr 1; omega
      -- Also obtain `SpineFit` for `idx_r` from `WellDenotedV` of `majDomA` (`dsRec[nP + 1 + anc + 1]`)
      have hok_TVa : WellDenotedV V ρ_call TVa := mp.type_wellDenotedV _ hmemR _ TVa hTVa_base ρ_call
      have hok_maj : WellDenotedV V (consList xs_v ρ_call) (AnnotTerm.mkAppN faM argsMA) := by
        rw [← hmajA_eq]
        -- Extract `WellDenotedV` of the `(nP + 1 + anc + 1)`-th Pi domain from `hok_TVa` + `hsp_TVa`
        have hgo : ∀ (ds : List (Nat × Nat × AnnotTerm)) (R : AnnotTerm) (vs : List V) (σ : Nat → V),
            WellDenotedV V σ (mkPisAV ds R) →
            SpineFit σ (ds.map (·.2.2)) vs →
            ∀ j (hj : j < ds.length),
              WellDenotedV V (consList (vs.take j) σ) ((ds.getD j default).2.2) := by
          intro ds
          induction ds with
          | nil => intro _ _ _ _ _ _ hj; cases hj
          | cons d ds ih =>
            intro R vs σ hok hsp j hj
            cases vs with
            | nil => exact hsp.elim
            | cons v vs =>
              cases j with
              | zero =>
                exact ⟨((WellDenoted_pi V σ d.1 d.2.1 d.2.2 (mkPisAV ds R)).mp hok.1).1,
                       ((AnnotValid_pi V σ d.1 d.2.1 d.2.2 (mkPisAV ds R)).mp hok.2).1⟩
              | succ j' =>
                have hok' : WellDenotedV V (cons v σ) (mkPisAV ds R) :=
                  ⟨((WellDenoted_pi V σ d.1 d.2.1 d.2.2 (mkPisAV ds R)).mp hok.1).2 v hsp.1,
                   ((AnnotValid_pi V σ d.1 d.2.1 d.2.2 (mkPisAV ds R)).mp hok.2).2.1 v hsp.1⟩
                simpa [consList_cons] using ih R vs (cons v σ) hok' hsp.2 j' (by simpa using hj)
        have h1 := hgo dsRec bodyRecA ((xs_A ++ [ctorApp_A]).map (interp V ρ_call)) ρ_call
          (hTVa_eq ▸ hok_TVa) hsp_TVa (nP + 1 + anc + 1) (by omega)
        have htake : ((xs_A ++ [ctorApp_A]).map (interp V ρ_call)).take (nP + 1 + anc + 1) = xs_v := by
          rw [List.map_append, hxsA_map, List.take_left' hxs_len]
        rwa [htake] at h1
      have hidx_r_fit : SpineFit (consList vs_v ρ_call) (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)) [idx_r] := by
        obtain ⟨hokF, -, hchM⟩ := appChainOk_of_wellDenotedV argsMA hok_maj
        rw [hargsMA_map, hfaM_eq, hAtAux.leafT ψ_P] at hchM
        rw [hfaM_eq, hAtAux.leafT ψ_P] at hokF
        have hnz_ty : ∀ p ∈ ((ppsAll ψ_P).map fun d => (famAux.p.resSort.eval ψ_P + 1, d.2.2)), p.1 ≠ 0 := by
          intro p hp; obtain ⟨d, -, rfl⟩ := List.mem_map.mp hp; omega
        have hsp_all := (mkLamsAV_appChainOk_pos
          ((ppsAll ψ_P).map fun d => (famAux.p.resSort.eval ψ_P + 1, d.2.2)) _ (vs_v ++ [idx_r])
          (consList xs_v ρ_call) hnz_ty
          (by have := hAtAux.former.len ψ_P; simp [this, hfam_nP, hfam_nIdx, hvs_len])
          hokF hchM).2.1
        have hmap_eq : (((ppsAll ψ_P).map fun d => (famAux.p.resSort.eval ψ_P + 1, d.2.2)).map Prod.snd) =
            ((ppsAll ψ_P).take famAux.p.nP).map (·.2.2) ++ ((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2) := by
          rw [List.map_map, ← List.map_append, List.take_append_drop]
          rfl
        rw [hmap_eq] at hsp_all
        have hsp_idx := ((spineFit_append_iff
          (by have := hAtAux.former.len ψ_P; rw [List.length_map, List.length_take, this, hfam_nP, hfam_nIdx, hvs_len]; omega)).mp
          hsp_all).2
        -- Transport `SpineFit` from `consList vs_v (consList xs_v ρ_call)` to `consList vs_v ρ_call` via `DomsBelow`!
        have hdb_all := hAtAux.former.below ψ_P
        have hdb_idx : Ix.Kernel.Semantics.DomsBelow nP ((ppsAll ψ_P).drop famAux.p.nP) := by
          have hgo : ∀ (k : Nat) (ds : List (Nat × Nat × AnnotTerm)),
              Ix.Kernel.Semantics.DomsBelow k ds →
              ∀ m, m ≤ ds.length → Ix.Kernel.Semantics.DomsBelow (k + m) (ds.drop m) := by
            intro k ds
            induction ds generalizing k with
            | nil => intro _ m hm; simp [Nat.le_zero.mp hm]; trivial
            | cons d ds ih =>
              intro hdb m hm
              cases m with
              | zero => simpa using hdb
              | succ m' =>
                simpa [show k + (m' + 1) = (k + 1) + m' by omega] using ih (k + 1) hdb.2 m' (by simpa using hm)
          have h1 := hgo 0 (ppsAll ψ_P) hdb_all famAux.p.nP (by have := hAtAux.former.len ψ_P; omega)
          simpa [hfam_nP] using h1
        cases hdrop : (ppsAll ψ_P).drop famAux.p.nP with
        | nil => rw [hdrop] at hIds_len; simp at hIds_len
        | cons d0 dr =>
          cases dr with
          | cons _ _ => rw [hdrop] at hIds_len; simp at hIds_len
          | nil =>
            rw [hdrop] at hsp_idx hdb_idx
            simp only [List.map_cons, List.map_nil, SpineFit] at hsp_idx ⊢
            refine ⟨?_, trivial⟩
            have heq := Ix.Kernel.Semantics.interp_congr_below V d0.2.2 nP
              (consList vs_v (consList xs_v ρ_call)) (consList vs_v ρ_call) hdb_idx.1 fun j hj => by
                rw [consList_getElem vs_v (consList xs_v ρ_call) j (by omega),
                  consList_getElem vs_v ρ_call j (by omega)]
            exact heq ▸ hsp_idx.1
      have hctor_mem_r : interp V ρ_call ctorApp_A ∈ˢ
          SetTheory.app (fixFamI (uAV ψ_P) (famAux.p.resSort.eval ψ_P) (consList vs_v ρ_call)
            (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)) 1
            (Ix.Kernel.Model.rssOfK ksF famAux.ctorsA.length)
            (Ix.Kernel.Model.tlssOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
            (Ix.Kernel.Model.eissOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
            (fssZ ψ_P)
            (Ix.Kernel.Model.essOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)))
            (tupW (uAV ψ_P) [idx_r]) := by
        rw [hmajA_eq] at hctor_mem_maj
        rw [interp_mkAppN_foldl (consList xs_v ρ_call) argsMA faM, hargsMA_map, hfaM_eq,
          closed_interp_env (mp.base2.acval_closed _ _) (consList xs_v ρ_call) ρ_call,
          hAtAux.leafT ψ_P] at hctor_mem_maj
        have hfold := nativeTyAVI_fold_at hfr.1 hsp_pps hidx_r_fit
        rw [hfold, hIds_len] at hctor_mem_maj
        exact hctor_mem_maj
      -- Apply `aux_fibre_disjoint`!
      have hEs_len : ∀ j, j < (fssZ ψ_P).length →
          ((Ix.Kernel.Model.essOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)).getD j []).length =
            (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)).length := by
        intro j hj
        have hlenZ : (fssZ ψ_P).length = famAux.ctorsA.length := by
          have := hfr.2.1.1
          simp [Ix.Kernel.Model.fssOfR, Ix.Kernel.Model.fixCtorDataList_length] at this
          exact this
        have hjlt : j < famAux.ctorsA.length := by omega
        obtain ⟨cAj, hcAj⟩ : ∃ cAj, famAux.ctorsA[j]? = some cAj := ⟨_, List.getElem?_eq_getElem hjlt⟩
        rw [List.getD_eq_getElem?_getD, Ix.Kernel.Model.essOfR_getElem?,
          Ix.Kernel.Model.fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0 j, hcAj]
        simp only [Nat.zero_add, Option.map_some, Option.getD_some,
          (hAtAux.ctor j cAj hcAj).lenE ψ_P, hfam_nIdx, hIds_len]
      exact aux_fibre_disjoint hw_aux hfr.1 hEs_len hIds_len hidx_c_fit hidx_r_fit hctor_mem_c hctor_mem_r
    -- 8. Fire `hFire`!
    have hFire_eq := hFire cA.1 famAux.p.nP cA.2 (hrl_ctor ▸ hfindC) usj ρ_call xs_A ys_A
      TVa (mkPisAV (dsF k ψ_P) (ctorBodyAVI mp.base2 famAux.p.cvT.name famAux.p.nP cA.2 ψ_P (esF k ψ_P)))
      restR restC
      (by simp [xs_A, hxs_len])
      (by simp [ys_A, ys_v, hvs_len, hfs_len, hrl_nP])
      (by simp [usj, hcA_lps])
      (by
        simp only [Ix.Kernel.recFireComparands, hfire_plain, hcA_lps]
        funext p
        by_cases hp : p < bnl
        · have hp_mem : p ∈ List.range bnl := List.mem_range.mpr hp
          have hp_ne : p ≠ elim := fun heq => helim_not_mem (heq ▸ hp_mem)
          rw [substFn_range_param]
          have hget := substFn_getElem (ψ := ψ_P) (List.range bnl)
            ((List.range bnl).map fun q => Level.subst cvAuxRec.levelParams elimLvls (.param q))
            List.nodup_range (by simp) p (by simp [hp])
          simp only [List.getElem_range, List.getElem_map] at hget
          rw [hget, Ix.Kernel.Level.eval_subst, hcvLps_cons, hrestLps_eq]
          cases elimLvls with
          | nil => simp at h_elim_len
          | cons e0 er =>
            simp only [Level.substFn]
            rw [substFn_eq_of_lvEqList (by simpa using h_elim_drop) ψ_P, substFn_range_param]
            simp [Level.eval, Ne.symm hp_ne]
        · have hp_nmem : p ∉ List.range bnl := by simp [hp]
          rw [substFn_not_mem _ _ _ hp_nmem, substFn_not_mem _ _ _ hp_nmem])
      (fun _ _ i hi _ => by
        rw [hrl_nP] at hi
        have h1 : interp V ρ_call (ys_A.getD i default) = ys_v[i]'(by simp [ys_v, hvs_len]; omega) := by
          have hget : ys_A.getD i default = ys_A[i]'(by simp [ys_A, ys_v, hvs_len]; omega) := by
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show i < ys_A.length by simp [ys_A, ys_v, hvs_len]; omega)]
          rw [hget]
          have hmap := congrArg (fun l => l[i]?) hysA_map
          simp only [List.getElem?_map,
            List.getElem?_eq_getElem (show i < ys_A.length by simp [ys_A, ys_v, hvs_len]; omega),
            List.getElem?_eq_getElem (show i < ys_v.length by simp [ys_v, hvs_len]; omega),
            Option.map_some, Option.some.injEq] at hmap
          exact hmap
        have h2 : interp V ρ_call (xs_A.getD i default) = xs_v[i]'(by omega) := by
          have hget : xs_A.getD i default = xs_A[i]'(by simp [xs_A, hxs_len]; omega) := by
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show i < xs_A.length by simp [xs_A, hxs_len]; omega)]
          rw [hget]
          have hmap := congrArg (fun l => l[i]?) hxsA_map
          simp only [List.getElem?_map,
            List.getElem?_eq_getElem (show i < xs_A.length by simp [xs_A, hxs_len]; omega),
            List.getElem?_eq_getElem (show i < xs_v.length by omega),
            Option.map_some, Option.some.injEq] at hmap
          exact hmap
        rw [h1, h2]
        have h3 := congrArg (fun l => l[i]?) hxs_pref
        simp only [List.getElem?_take, show i < nP from hi, ↓reduceIte,
          List.getElem?_eq_getElem (show i < xs_v.length by omega),
          List.getElem?_eq_getElem (show i < vs_v.length by omega)] at h3
        have hv_eq : xs_v[i]'(by omega) = vs_v[i]'(by omega) := Option.some.inj h3
        simp [ys_v, List.getElem_append_left (show i < vs_v.length by omega), hv_eq])
      (fun _ _ hnest => by rw [hfire_plain] at hnest; cases hnest)
      hPin hTVa_den hTVja_den
      (by simpa [hrl_ctor] using hfit_TVa)
      hfit_TVja
    -- 9. Reduce `Ra` via `denoteMeta_stripLams` + `mkLamsAV_appChainOk_pos`!
    have hRa_pos : denoteMeta mp.base2.acval env (ψ_rec elimLvls bnl ψ_P) 0
        (Core.posOf cvAuxRec.levelParams rl.rhs) = some Ra := by
      rw [denotePInstLevels mp.base2 ψ_P cvAuxRec.levelParams elimLvls 0 rl.rhs] at hRa_den
      rw [posOf_denoteMeta mp.base2 cvAuxRec.levelParams (ψ_rec elimLvls bnl ψ_P) 0 rl.rhs]
      have hwf_rec := mp.base2.wf _ hmemR
      have hrl_wf := hwf_rec.2.2.2.2.2.1 cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules rfl rl hrl_mem
      have hdef_rhs : rl.rhs.allLevelParamsDefined cvAuxRec.levelParams = true := hrl_wf.2.1
      rw [← Ix.Kernel.Model.denoteMeta_params_ext mp.base2 hvalEq 0 rl.rhs hdef_rhs]
      exact hRa_den
    obtain ⟨ldsR, rbodyA, hRa_eq, hldsR_len, hldsR_bits, hrbodyA_den⟩ :=
      denoteMeta_stripLams (nP + 1 + anc + rl.nfields) 0 hr_strip hRa_pos
    have hldsR_nz : ∀ p ∈ ldsR, p.1 ≠ 0 := by
      -- Compare `rbs` with `bs0` via `stripLams_instantiateLevelParams`!
      have hsl_pos := stripLams_instantiateLevelParams cvAuxRec.levelParams
        (Core.posLevels cvAuxRec.levelParams) (nP + 1 + anc + rl.nfields) hsl0
      rw [show Core.posOf cvAuxRec.levelParams rl.rhs =
        rl.rhs.instantiateLevelParams cvAuxRec.levelParams (Core.posLevels cvAuxRec.levelParams) from rfl] at hr_strip
      rw [hsl_pos] at hr_strip
      injection Option.some.inj hr_strip with hrbs_eq _
      intro p hp
      have hmem : p.1 ∈ ldsR.map Prod.fst := List.mem_map_of_mem hp
      rw [hldsR_bits, ← hrbs_eq] at hmem
      obtain ⟨bm', hbm', hbit⟩ := List.mem_map.mp hmem
      obtain ⟨bm0, hbm0, rfl⟩ := List.mem_map.mp hbm'
      rw [← hbit, hbs0_pw bm0 hbm0, pwBit_substPW]
      have hsub_eq : Level.substFn (ψ_rec elimLvls bnl ψ_P) cvAuxRec.levelParams
          (Core.posLevels cvAuxRec.levelParams) = origVal cvAuxRec.levelParams (ψ_rec elimLvls bnl ψ_P) := rfl
      rw [hsub_eq, hmaj0_pw]
      simp only [pwBit, Ix.Kernel.PropWhen.holds_ifAllZero, List.all_cons, List.all_nil,
        Bool.and_true, beq_iff_eq]
      rw [← hvalEq elim (hcvLps_cons ▸ List.mem_cons_self), hRec_elim_val]
      have hne : ¬ (elimLvls.getD 0 .zero).eval ψ_P = 0 := Nat.ne_of_gt h_elim_nz
      simp only [hne, ↓reduceIte]
      omega
    have hRa_closed : ∀ m, Ra.liftN 1 m = Ra := by
      have hwf_rec := mp.base2.wf _ hmemR
      have hrl_wf := hwf_rec.2.2.2.2.2.1 cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules rfl rl hrl_mem
      have hfv : (rl.rhs.instantiateLevelParams cvAuxRec.levelParams elimLvls).hasFvar = false := by
        simpa [Ix.Kernel.Expr.hasFvar_instantiateLevelParams] using hrl_wf.1
      have hbd : (rl.rhs.instantiateLevelParams cvAuxRec.levelParams elimLvls).looseBVarsBounded 0 = true := by
        simpa [Ix.Kernel.Expr.looseBVarsBounded_instantiateLevelParams] using hrl_wf.2.2.2.1
      intro m
      exact Ix.Kernel.Model.denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed hfv hbd hRa_den 1 m
    have hwd_RaApp := hFire_eq.2
      (bvarsDesc_wellDenotedV ρ_call ys_v.length xs_v.length)
      (by simpa only [Nat.zero_add] using bvarsDesc_wellDenotedV ρ_call 0 ys_v.length)
    obtain ⟨hRa_wd_call, -, hRa_ch⟩ := appChainOk_of_wellDenotedV _ hwd_RaApp
    have hargs_map : (xs_A.take (nP + 1 + anc) ++ ys_A.drop rl.ctorParams).map (interp V ρ_call) =
        xs_v.take (nP + 1 + anc) ++ fs_v := by
      rw [List.map_append, List.map_take, hxsA_map, List.map_drop, hysA_map, hrl_nP]
      simp [ys_v, List.drop_left' hvs_len]
    rw [hargs_map, closed_interp_env hRa_closed ρ_call ρ₀] at hRa_ch
    have hRa_wd₀ : WellDenotedV V ρ₀ Ra := closed_wellDenotedV_env hRa_closed ρ₀ hRa_wd_call
    rw [hRa_eq] at hRa_ch hRa_wd₀
    obtain ⟨heval_Ra, -, hbody_wd⟩ := mkLamsAV_appChainOk_pos ldsR rbodyA
      (xs_v.take (nP + 1 + anc) ++ fs_v) ρ₀ hldsR_nz
      (by simp [hxs_len, hfs_len, hldsR_len]) hRa_wd₀ hRa_ch
    -- Unpack `rbodyA = mkAppN (.bvar ...) rargsA`
    have hrbody_den' := hrbodyA_den
    rw [openDummiesP_mkAppN] at hrbody_den'
    obtain ⟨fhR, rargsA, hfhR, hspR, hrbodyA_eq⟩ := denoteMeta_mkAppN_inv hrbody_den'
    have hfhR_eq : fhR = .bvar (rl.nfields + anc - 1 - k) := by
      rw [denoteMeta_openDummiesP_bvar (by omega)] at hfhR
      exact (Option.some.inj hfhR).symm
    rw [hfhR_eq] at hrbodyA_eq
    rw [Nat.zero_add] at hrbodyA_den hspR
    refine ⟨rbodyA, rargsA, hrbodyA_den, hrbodyA_eq, hspR, ?_, hbody_wd⟩
    -- Combine `hFire_eq.1` with `heval_Ra`!
    have hfire1 := hFire_eq.1
    simp only [interp_mkAppN_foldl, List.map_append, List.map_singleton, hxsA_map] at hfire1
    have hctor_fold : (ys_A.map (interp V ρ_call)).foldl SetTheory.app
        (interp V ρ_call (mp.base2.acval rl.ctor (Level.substFn ψ_P cA.1.levelParams usj))) =
        inj k (mkTower (fs_v ++ [pt])) := by
      rw [← interp_mkAppN_foldl, hrl_ctor]
      exact hctor_val
    rw [hRec_acval_eq, closed_interp_env (mp.base2.acval_closed _ _) ρ_call ρ₀, hctor_fold] at hfire1
    rw [hfire1]
    have harg_eq : (xs_A.take (nP + 1 + anc)).map (interp V ρ_call) ++
        (ys_A.drop rl.ctorParams).map (interp V ρ_call) = xs_v.take (nP + 1 + anc) ++ fs_v := by
      simpa [List.map_append] using hargs_map
    rw [harg_eq, closed_interp_env hRa_closed ρ_call ρ₀, hRa_eq]
    exact heval_Ra
  | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _ | lit _
  | proj _ _ _ =>
    simp [Core.posOf, Expr.instantiateLevelParams] at hrem0

end IxVM.Refinement.Typing.FamilyAlias

