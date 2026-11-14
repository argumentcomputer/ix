import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.Lib.Lists
import IxVMRefinement.Levels.Bound
import IxVMRefinement.Subst.Steps
import IxVMRefinement.Obs.KernelCheck6
import IxVMRefinement.Obs.KernelCheck7
import IxVMRefinement.Obs.KernelCheck8
import IxVMRefinement.Obs.KernelCheck9
import IxVMRefinement.Obs.KernelCheck11

/-! # Native one-type inductive recursor route

This module refines the native recursor stages of `KernelCheck::check_const` on unpinned
one-type inductive blocks (`is_large_eliminator`, `wrap_rel` / `consume_wrapper` /
`lam_first_arity`, `nat_rec_check` and its recursor-type / rule-RHS generators,
`check_recursor_canonical_full`, and `check_recursor_member`) to `DeclNativeRunJ` +
`InstallStep`. -/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (ConstantInfo ConstantVal Declaration Expr Level LevelParam RecRule)
open Ix.Kernel.Rules (Red DefEq Infer)
open Ix.Kernel.Semantics (Judgements ConstantValRunJ ConstantValCheckJ DeclRunJ IndRoutesJ
  SumIndRunJ FormerStoredJ FormerReadJ SumCtorsRunJ SumCtorRunJ StructDomsJ FieldSortsJ
  NativeRecJ NativeRecRunJ RecStoredJ DeclNativeRunJ ConsumeStar consumeWrapper wrapperArity
  lamFirstArity letFree)
open Ix.Kernel.Model (rulesJ)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

local macro "rec_lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

/-! ## Section 1: `WrapTSem`, `defnAritiesOk`, `WrapRelSem.defeq`, and `posOf` transport -/

/-- Structural counterpart of `Ix.Kernel.Semantics.WrapT` with semantic level equivalence
(`LvEq` on `.sort`, `LvEqList` on `.const`) and fvar types ignored. -/
inductive WrapTSem (find? : KKey → Option (ConstantInfo .anon)) : KExpr → KExpr → Prop
  | bvar (i : Nat) : WrapTSem find? (.bvar i) (.bvar i)
  | fvar (i : Nat) (t t' : KExpr) : WrapTSem find? (.fvar i t) (.fvar i t')
  | sort {u u' : KLevel} : LvEq u u' → WrapTSem find? (.sort u) (.sort u')
  | const {n : KKey} {us us' : List KLevel} :
      LvEqList us us' → WrapTSem find? (.const n us) (.const n us')
  | lit (l : Ix.Kernel.Literal) : WrapTSem find? (.lit l) (.lit l)
  | app {f a f' a' : KExpr} :
      WrapTSem find? f f' → WrapTSem find? a a' → WrapTSem find? (.app f a) (.app f' a')
  | lam {t a t' b b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumeStar find? t a → WrapTSem find? a t' → WrapTSem find? b b' →
      WrapTSem find? (.lam t b m) (.lam t' b' m')
  | forallE {t a t' b b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumeStar find? t a → WrapTSem find? a t' → WrapTSem find? b b' →
      WrapTSem find? (.forallE t b m) (.forallE t' b' m')
  | letE {t v b t' v' b' : KExpr} {l l' : Ix.Kernel.LetMeta} :
      WrapTSem find? t t' → WrapTSem find? v v' → WrapTSem find? b b' →
      WrapTSem find? (.letE t v b l) (.letE t' v' b' l')
  | proj {s : KKey} {i : Nat} {e e' : KExpr} :
      WrapTSem find? e e' → WrapTSem find? (.proj s i e) (.proj s i e')

theorem ExprSemEq.toWrapTSem (find? : KKey → Option (ConstantInfo .anon)) {e e' : KExpr}
    (h : ExprSemEq e e') : WrapTSem find? e e' := by
  induction h with
  | bvar i => exact .bvar i
  | fvar _ _ => exact .fvar _ _ _
  | sort hu => exact .sort hu
  | const hus => exact .const hus
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw _ _ iht ihb => exact .lam hpw (.refl _) iht ihb
  | forallE hpw _ _ iht ihb => exact .forallE hpw (.refl _) iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ihe => exact .proj ihe

theorem WrapRelSem.toWrapTSem {find? : KKey → Option (ConstantInfo .anon)} {g d : KExpr}
    (h : WrapRelSem find? g d) (hd : letFree d = true) : WrapTSem find? g d :=
  WrapRelSem.rec
    (motive_1 := fun g d _ => letFree d = true → WrapTSem find? g d)
    (motive_2 := fun t t' _ => letFree t' = true →
      ∃ a, ConsumeStar find? t a ∧ WrapTSem find? a t')
    (bvar := fun i _ => .bvar i)
    (fvar := fun _ _ _ => .fvar _ _ _)
    (sort := fun hu _ => .sort hu)
    (const := fun hus _ => .const hus)
    (lit := fun l _ => .lit l)
    (app := fun _ _ ihf iha hl => by
      simp only [letFree, Bool.and_eq_true] at hl
      exact .app (ihf hl.1) (iha hl.2))
    (lam := fun hpw _ _ ihd ihb hl => by
      simp only [letFree, Bool.and_eq_true] at hl
      obtain ⟨a, hs, hw⟩ := ihd hl.1
      exact .lam hpw hs hw (ihb hl.2))
    (forallE := fun hpw _ _ ihd ihb hl => by
      simp only [letFree, Bool.and_eq_true] at hl
      obtain ⟨a, hs, hw⟩ := ihd hl.1
      exact .forallE hpw hs hw (ihb hl.2))
    (letE := fun _ _ _ _ _ _ hl => by simp [letFree] at hl)
    (proj := fun _ ih hl => .proj (ih (by simpa only [letFree] using hl)))
    (zeta := fun _ _ hl => by simp [letFree] at hl)
    (keep := fun _ ih hl => ⟨_, .refl _, ih hl⟩)
    (consume := fun hc _ ih hl => by
      obtain ⟨a, hs, hw⟩ := ih hl
      exact ⟨a, .step hc hs, hw⟩)
    h hd

theorem WrapTSem.instantiate1 {find? : KKey → Option (ConstantInfo .anon)} {v v' : KExpr}
    (hv : WrapTSem find? v v') {g d : KExpr} (h : WrapTSem find? g d) :
    ∀ j, WrapTSem find? (g.instantiate1 v j) (d.instantiate1 v' j) := by
  induction h with
  | bvar i =>
    intro j
    show WrapTSem find? (if i = j then v else if i > j then .bvar (i - 1) else .bvar i)
      (if i = j then v' else if i > j then .bvar (i - 1) else .bvar i)
    by_cases h1 : i = j
    · rw [ite_eq_left h1, ite_eq_left h1]; exact hv
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : i > j
      · rw [ite_eq_left h2]; exact .bvar _
      · rw [ite_eq_right h2]; exact .bvar _
  | fvar i t t' => intro _; exact .fvar i t t'
  | sort hu => intro _; exact .sort hu
  | const hus => intro _; exact .const hus
  | lit l => intro _; exact .lit l
  | app _ _ ihf iha => intro j; exact .app (ihf j) (iha j)
  | lam hpw hs _ _ ihw ihb => intro j; exact .lam hpw (hs.instantiate1 v j) (ihw j) (ihb (j + 1))
  | forallE hpw hs _ _ ihw ihb =>
    intro j; exact .forallE hpw (hs.instantiate1 v j) (ihw j) (ihb (j + 1))
  | letE _ _ _ iht ihv ihb =>
    intro j; exact .letE (iht j) (ihv j) (ihb (j + 1))
  | proj _ ih => intro j; exact .proj (ih j)

theorem mkAppN_abstract1 (d : Nat) :
    ∀ (args : List KExpr) (f : KExpr) (k : Nat),
      (Expr.mkAppN f args).abstract1 d k =
        Expr.mkAppN (f.abstract1 d k) (args.map (fun x => x.abstract1 d k))
  | [], f, k => rfl
  | a :: as, f, k => by
    simp only [Expr.mkAppN, List.map_cons]
    exact mkAppN_abstract1 d as (.app f a) k

theorem consumeWrapper_abstract1 {find? : KKey → Option (ConstantInfo .anon)} {t a : KExpr}
    (h : consumeWrapper find? t = some a) (d k : Nat) :
    consumeWrapper find? (t.abstract1 d k) = some (a.abstract1 d k) := by
  obtain ⟨w, us, rest, rfl, hw⟩ := Ix.Kernel.Semantics.consumeWrapper_inv h
  rw [mkAppN_abstract1]
  exact Ix.Kernel.Semantics.consumeWrapper_mkAppN (by simpa using hw)

theorem ConsumeStar.abstract1 {find? : KKey → Option (ConstantInfo .anon)} {t a : KExpr}
    (h : ConsumeStar find? t a) (d k : Nat) :
    ConsumeStar find? (t.abstract1 d k) (a.abstract1 d k) := by
  induction h with
  | refl => exact .refl _
  | step hc _ ih => exact .step (consumeWrapper_abstract1 hc d k) ih

theorem WrapTSem.abstract1 {find? : KKey → Option (ConstantInfo .anon)} {g d_e : KExpr}
    (h : WrapTSem find? g d_e) (d : Nat) :
    ∀ k, WrapTSem find? (g.abstract1 d k) (d_e.abstract1 d k) := by
  induction h with
  | bvar i => intro _; exact .bvar i
  | fvar i t t' =>
    intro k
    simp only [Expr.abstract1]
    by_cases hi : i = d
    · rw [ite_eq_left hi, ite_eq_left hi]; exact .bvar k
    · rw [ite_eq_right hi, ite_eq_right hi]; exact .fvar i t t'
  | sort hu => intro _; exact .sort hu
  | const hus => intro _; exact .const hus
  | lit l => intro _; exact .lit l
  | app _ _ ihf iha => intro k; exact .app (ihf k) (iha k)
  | lam hpw hs _ _ ihw ihb =>
    intro k; exact .lam hpw (ConsumeStar.abstract1 hs d k) (ihw k) (ihb (k + 1))
  | forallE hpw hs _ _ ihw ihb =>
    intro k; exact .forallE hpw (ConsumeStar.abstract1 hs d k) (ihw k) (ihb (k + 1))
  | letE _ _ _ iht ihv ihb =>
    intro k; exact .letE (iht k) (ihv k) (ihb (k + 1))
  | proj _ ih => intro k; exact .proj (ih k)

theorem ConsumeStar.toWrapDomSem {find? : KKey → Option (ConstantInfo .anon)} {t a t' : KExpr}
    (hs : ConsumeStar find? t a) (hd : WrapRelSem find? a t') : WrapDomSem find? t t' := by
  induction hs with
  | refl => exact .keep hd
  | step hc _ ih => exact .consume hc (ih hd)

theorem WrapTSem.toWrapRelSem {find? : KKey → Option (ConstantInfo .anon)} {g d : KExpr}
    (h : WrapTSem find? g d) (hg : g.hasFvar = false) : WrapRelSem find? g d := by
  have hP : ∀ f x : KExpr, (Expr.app f x).hasFvar = false →
      f.hasFvar = false ∧ x.hasFvar = false := by
    intro f x hfx
    simpa [Expr.hasFvar] using hfx
  induction h with
  | bvar i => exact .bvar i
  | fvar _ _ _ => simp [Expr.hasFvar] at hg
  | sort hu => exact .sort hu
  | const hus => exact .const hus
  | lit l => exact .lit l
  | app _ _ ihf iha =>
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hg
    exact .app (ihf hg.1) (iha hg.2)
  | lam hpw hs _ _ ihw ihb =>
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hg
    exact .lam hpw
      (ConsumeStar.toWrapDomSem hs (ihw (hs.of (P := fun e => e.hasFvar = false) hP hg.1)))
      (ihb hg.2)
  | forallE hpw hs _ _ ihw ihb =>
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hg
    exact .forallE hpw
      (ConsumeStar.toWrapDomSem hs (ihw (hs.of (P := fun e => e.hasFvar = false) hP hg.1)))
      (ihb hg.2)
  | letE _ _ _ iht ihv ihb =>
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hg
    exact .letE (iht hg.1.1) (ihv hg.1.2) (ihb hg.2)
  | proj _ ih =>
    simp only [Expr.hasFvar] at hg
    exact .proj (ih hg)

/-- Every `.const n us` in `e` naming a `.defnInfo` in `find?` has matching level-parameter arity
(`us.length == cv.levelParams.length`), ignoring fvar types. -/
def defnAritiesOk (find? : KKey → Option (ConstantInfo .anon)) : KExpr → Bool
  | .const n us =>
    match find? n with
    | some (.defnInfo cv _ _) => us.length == cv.levelParams.length
    | _ => true
  | .app f a => defnAritiesOk find? f && defnAritiesOk find? a
  | .lam t b _ => defnAritiesOk find? t && defnAritiesOk find? b
  | .forallE t b _ => defnAritiesOk find? t && defnAritiesOk find? b
  | .letE t v b _ => defnAritiesOk find? t && defnAritiesOk find? v && defnAritiesOk find? b
  | .proj _ _ e => defnAritiesOk find? e
  | _ => true

theorem defnAritiesOk_congr_defn {find₁ find₂ : KKey → Option (ConstantInfo .anon)}
    (hsub : ∀ n cv v hn, find₂ n = some (.defnInfo cv v hn) → find₁ n = some (.defnInfo cv v hn)) :
    ∀ e : KExpr, defnAritiesOk find₁ e = true → defnAritiesOk find₂ e = true
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .lit _, _ => rfl
  | .const n us, h => by
    simp only [defnAritiesOk] at h ⊢
    cases h₂ : find₂ n with
    | none => rfl
    | some ci =>
      cases ci with
      | defnInfo cv v hn =>
        rw [hsub n cv v hn h₂] at h
        exact h
      | _ => rfl
  | .app f a, h => by
    simp only [defnAritiesOk, Bool.and_eq_true] at h ⊢
    exact ⟨defnAritiesOk_congr_defn hsub f h.1, defnAritiesOk_congr_defn hsub a h.2⟩
  | .lam t b _, h => by
    simp only [defnAritiesOk, Bool.and_eq_true] at h ⊢
    exact ⟨defnAritiesOk_congr_defn hsub t h.1, defnAritiesOk_congr_defn hsub b h.2⟩
  | .forallE t b _, h => by
    simp only [defnAritiesOk, Bool.and_eq_true] at h ⊢
    exact ⟨defnAritiesOk_congr_defn hsub t h.1, defnAritiesOk_congr_defn hsub b h.2⟩
  | .letE t v b _, h => by
    simp only [defnAritiesOk, Bool.and_eq_true] at h ⊢
    exact ⟨⟨defnAritiesOk_congr_defn hsub t h.1.1, defnAritiesOk_congr_defn hsub v h.1.2⟩,
      defnAritiesOk_congr_defn hsub b h.2⟩
  | .proj _ _ e, h => by
    simp only [defnAritiesOk] at h ⊢
    exact defnAritiesOk_congr_defn hsub e h

theorem defnAritiesOk_liftLooseBVars {find? : KKey → Option (ConstantInfo .anon)} :
    ∀ (e : KExpr) (n c : Nat),
      defnAritiesOk find? (e.liftLooseBVars n c) = defnAritiesOk find? e
  | .bvar _, n, c => by simp only [Expr.liftLooseBVars]; split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, n, c => by
    simp [Expr.liftLooseBVars, defnAritiesOk,
      defnAritiesOk_liftLooseBVars f n c, defnAritiesOk_liftLooseBVars a n c]
  | .lam t b _, n, c => by
    simp [Expr.liftLooseBVars, defnAritiesOk,
      defnAritiesOk_liftLooseBVars t n c, defnAritiesOk_liftLooseBVars b n (c + 1)]
  | .forallE t b _, n, c => by
    simp [Expr.liftLooseBVars, defnAritiesOk,
      defnAritiesOk_liftLooseBVars t n c, defnAritiesOk_liftLooseBVars b n (c + 1)]
  | .letE t v b _, n, c => by
    simp [Expr.liftLooseBVars, defnAritiesOk,
      defnAritiesOk_liftLooseBVars t n c, defnAritiesOk_liftLooseBVars v n c,
      defnAritiesOk_liftLooseBVars b n (c + 1)]
  | .proj _ _ e, n, c => by
    simpa [Expr.liftLooseBVars, defnAritiesOk] using defnAritiesOk_liftLooseBVars e n c

theorem defnAritiesOk_instantiate1 {find? : KKey → Option (ConstantInfo .anon)} {v : KExpr}
    (hv : defnAritiesOk find? v = true) :
    ∀ (e : KExpr) (j : Nat), defnAritiesOk find? e = true →
      defnAritiesOk find? (e.instantiate1 v j) = true
  | .bvar i, j, _ => by
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .lit _, _, _ => rfl
  | .const _ _, _, h => h
  | .app f a, j, h => by
    simp only [defnAritiesOk, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, defnAritiesOk, Bool.and_eq_true]
    exact ⟨defnAritiesOk_instantiate1 hv f j h.1, defnAritiesOk_instantiate1 hv a j h.2⟩
  | .lam t b _, j, h => by
    simp only [defnAritiesOk, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, defnAritiesOk, Bool.and_eq_true]
    exact ⟨defnAritiesOk_instantiate1 hv t j h.1, defnAritiesOk_instantiate1 hv b (j + 1) h.2⟩
  | .forallE t b _, j, h => by
    simp only [defnAritiesOk, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, defnAritiesOk, Bool.and_eq_true]
    exact ⟨defnAritiesOk_instantiate1 hv t j h.1, defnAritiesOk_instantiate1 hv b (j + 1) h.2⟩
  | .letE t w b _, j, h => by
    simp only [defnAritiesOk, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, defnAritiesOk, Bool.and_eq_true]
    exact ⟨⟨defnAritiesOk_instantiate1 hv t j h.1.1, defnAritiesOk_instantiate1 hv w j h.1.2⟩,
      defnAritiesOk_instantiate1 hv b (j + 1) h.2⟩
  | .proj _ _ e, j, h => by
    simp only [defnAritiesOk] at h
    simpa [Expr.instantiate1, defnAritiesOk] using defnAritiesOk_instantiate1 hv e j h

theorem defnAritiesOk_of_instantiate1_fvar {find? : KKey → Option (ConstantInfo .anon)}
    (d : Nat) (ty : KExpr) :
    ∀ (e : KExpr) (j : Nat),
      defnAritiesOk find? (e.instantiate1 (.fvar d ty) j) = defnAritiesOk find? e
  | .bvar i, j => by
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, j => by
    simp [Expr.instantiate1, defnAritiesOk,
      defnAritiesOk_of_instantiate1_fvar d ty f j, defnAritiesOk_of_instantiate1_fvar d ty a j]
  | .lam t b _, j => by
    simp [Expr.instantiate1, defnAritiesOk,
      defnAritiesOk_of_instantiate1_fvar d ty t j, defnAritiesOk_of_instantiate1_fvar d ty b (j + 1)]
  | .forallE t b _, j => by
    simp [Expr.instantiate1, defnAritiesOk,
      defnAritiesOk_of_instantiate1_fvar d ty t j, defnAritiesOk_of_instantiate1_fvar d ty b (j + 1)]
  | .letE t v b _, j => by
    simp [Expr.instantiate1, defnAritiesOk,
      defnAritiesOk_of_instantiate1_fvar d ty t j, defnAritiesOk_of_instantiate1_fvar d ty v j,
      defnAritiesOk_of_instantiate1_fvar d ty b (j + 1)]
  | .proj _ _ e, j => by
    simpa [Expr.instantiate1, defnAritiesOk] using defnAritiesOk_of_instantiate1_fvar d ty e j

theorem defnAritiesOk_instantiateLevelParams {find? : KKey → Option (ConstantInfo .anon)}
    (ps : List LevelParam) (ls : List KLevel) :
    ∀ e : KExpr, defnAritiesOk find? (e.instantiateLevelParams ps ls) = defnAritiesOk find? e
  | .bvar _ | .fvar _ _ | .sort _ | .lit _ => rfl
  | .const n us => by
    simp only [Expr.instantiateLevelParams, defnAritiesOk]
    cases find? n with
    | none => rfl
    | some ci =>
      cases ci with
      | defnInfo cv _ _ => simp
      | _ => rfl
  | .app f a => by
    simp [Expr.instantiateLevelParams, defnAritiesOk,
      defnAritiesOk_instantiateLevelParams ps ls f, defnAritiesOk_instantiateLevelParams ps ls a]
  | .lam t b _ => by
    simp [Expr.instantiateLevelParams, defnAritiesOk,
      defnAritiesOk_instantiateLevelParams ps ls t, defnAritiesOk_instantiateLevelParams ps ls b]
  | .forallE t b _ => by
    simp [Expr.instantiateLevelParams, defnAritiesOk,
      defnAritiesOk_instantiateLevelParams ps ls t, defnAritiesOk_instantiateLevelParams ps ls b]
  | .letE t v b _ => by
    simp [Expr.instantiateLevelParams, defnAritiesOk,
      defnAritiesOk_instantiateLevelParams ps ls t, defnAritiesOk_instantiateLevelParams ps ls v,
      defnAritiesOk_instantiateLevelParams ps ls b]
  | .proj _ _ e => by
    simpa [Expr.instantiateLevelParams, defnAritiesOk] using
      defnAritiesOk_instantiateLevelParams ps ls e

theorem defnAritiesOk_mkAppN {find? : KKey → Option (ConstantInfo .anon)} :
    ∀ (args : List KExpr) (f : KExpr),
      defnAritiesOk find? (Expr.mkAppN f args) =
        (defnAritiesOk find? f && args.all (defnAritiesOk find?))
  | [], f => by simp [Expr.mkAppN]
  | a :: as, f => by
    simp only [Expr.mkAppN, List.all_cons, defnAritiesOk_mkAppN as (.app f a), defnAritiesOk,
      Bool.and_assoc]

theorem sizeB_instantiate1_fvar (d : Nat) (ty : KExpr) :
    ∀ (e : KExpr) (j : Nat), (e.instantiate1 (.fvar d ty) j).sizeB = e.sizeB
  | .bvar i, j => by
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, j => by
    simp [Expr.instantiate1, Expr.sizeB, sizeB_instantiate1_fvar d ty f j,
      sizeB_instantiate1_fvar d ty a j]
  | .lam t b _, j => by
    simp [Expr.instantiate1, Expr.sizeB, sizeB_instantiate1_fvar d ty t j,
      sizeB_instantiate1_fvar d ty b (j + 1)]
  | .forallE t b _, j => by
    simp [Expr.instantiate1, Expr.sizeB, sizeB_instantiate1_fvar d ty t j,
      sizeB_instantiate1_fvar d ty b (j + 1)]
  | .letE t v b _, j => by
    simp [Expr.instantiate1, Expr.sizeB, sizeB_instantiate1_fvar d ty t j,
      sizeB_instantiate1_fvar d ty v j, sizeB_instantiate1_fvar d ty b (j + 1)]
  | .proj _ _ e, j => by
    simpa [Expr.instantiate1, Expr.sizeB] using sizeB_instantiate1_fvar d ty e j

private theorem defnAritiesOk_of_infer_go {env : Ix.Kernel.Env .anon} :
    ∀ (sz : Nat) {d : Nat} {e t : KExpr},
      e.sizeB ≤ sz → Infer env .full d e t → defnAritiesOk env.find? e = true
  | 0, _, _, _, hsz, hinf => by
    cases hinf <;> simp [Expr.sizeB] at hsz
  | sz + 1, d, e, t, hsz, hinf => by
    cases hinf with
    | sort | fvar _ | natLit _ | strLit _ => rfl
    | @const _ _ n us ci hfind _ hlen =>
      simp only [defnAritiesOk, hfind]
      cases ci with
      | defnInfo cv _ _ => exact beq_iff_eq.mpr hlen
      | _ => rfl
    | @forallE _ _ ty body _ _ _ _ _ hit _ hib _ _ =>
      simp only [Expr.sizeB] at hsz
      simp only [defnAritiesOk, Bool.and_eq_true]
      refine ⟨defnAritiesOk_of_infer_go sz (by omega) hit, ?_⟩
      rw [← defnAritiesOk_of_instantiate1_fvar d ty body 0]
      exact defnAritiesOk_of_infer_go sz
        (by rw [sizeB_instantiate1_fvar]; omega) hib
    | @lam _ _ ty body _ _ _ _ _ _ hit _ hib _ _ _ _ =>
      simp only [Expr.sizeB] at hsz
      simp only [defnAritiesOk, Bool.and_eq_true]
      refine ⟨defnAritiesOk_of_infer_go sz (by omega) (hit rfl), ?_⟩
      rw [← defnAritiesOk_of_instantiate1_fvar d ty body 0]
      exact defnAritiesOk_of_infer_go sz
        (by rw [sizeB_instantiate1_fvar]; omega) hib
    | @app _ _ f a _ _ _ _ _ hif _ hia _ =>
      simp only [Expr.sizeB] at hsz
      simp only [defnAritiesOk, Bool.and_eq_true]
      exact ⟨defnAritiesOk_of_infer_go sz (by omega) hif,
        defnAritiesOk_of_infer_go sz (by omega) hia⟩
    | @proj _ _ _ _ pe _ _ _ _ hip _ _ _ _ _ _ =>
      simp only [Expr.sizeB] at hsz
      simp only [defnAritiesOk]
      exact defnAritiesOk_of_infer_go sz (by omega) hip

theorem defnAritiesOk_of_infer_full {env : Ix.Kernel.Env .anon} {d : Nat} {e t : KExpr}
    (h : Infer env .full d e t) : defnAritiesOk env.find? e = true :=
  defnAritiesOk_of_infer_go e.sizeB (Nat.le_refl _) h

theorem holds_zero_eq_not_isNever (pw : Ix.Kernel.PropWhen) :
    pw.holds (fun _ => 0) = !pw.isNever :=
  Ix.Kernel.PropWhen.casesZ
    (motive := fun p => p.holds (fun _ => 0) = !p.isNever)
    (by simp)
    (fun ps => by simp)
    pw

theorem substFn_zero_of_params :
    ∀ (ks : List LevelParam) (vs : List KLevel),
      (∀ v ∈ vs, ∃ m, v = .param m) →
      ∀ n, Level.substFn (fun _ => 0) ks vs n = 0
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | k :: ks, v :: vs, hvs, n => by
    simp only [Level.substFn]
    split
    · obtain ⟨m, rfl⟩ := hvs v List.mem_cons_self
      rfl
    · exact substFn_zero_of_params ks vs (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) n

theorem isNever_substPW_of_isNever {pw : Ix.Kernel.PropWhen} (hpw : pw.isNever = true)
    (ks : List LevelParam) (vs : List KLevel) :
    (Level.substPW ks vs pw).isNever = true := by
  rw [Ix.Kernel.PropWhen.isNever_iff] at hpw ⊢
  apply Ix.Kernel.PropWhen.eq_of_holds
  intro φ
  rw [Ix.Kernel.Level.holds_substPW, hpw]
  simp

theorem isNever_substPW_params (ks : List LevelParam) {vs : List KLevel}
    (hvs : ∀ v ∈ vs, ∃ m, v = .param m) (pw : Ix.Kernel.PropWhen) :
    (Level.substPW ks vs pw).isNever = pw.isNever := by
  have h0 : Level.substFn (fun _ => 0) ks vs = (fun _ => 0) := by
    funext n
    exact substFn_zero_of_params ks vs hvs n
  have hh : (Level.substPW ks vs pw).holds (fun _ => 0) = pw.holds (fun _ => 0) := by
    rw [Ix.Kernel.Level.holds_substPW, h0]
  rw [holds_zero_eq_not_isNever, holds_zero_eq_not_isNever] at hh
  exact Bool.not_inj hh

theorem isNever_substPW_posLevels (ks : List LevelParam) (pw : Ix.Kernel.PropWhen) :
    (Level.substPW ks (posLevels ks) pw).isNever = pw.isNever := by
  refine isNever_substPW_params ks (fun v hv => ?_) pw
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hv
  exact ⟨m, rfl⟩

theorem lamFirstArity_posOf (ps : List LevelParam) :
    ∀ (e : KExpr) (n : Nat), lamFirstArity (posOf ps e) n = lamFirstArity e n
  | .lam t b m, n => by
    show (if (Level.substPW ps (posLevels ps) m.pw).isNever then
      lamFirstArity (posOf ps b) (n + 1) else none) =
      (if m.pw.isNever then lamFirstArity b (n + 1) else none)
    rw [isNever_substPW_posLevels, lamFirstArity_posOf ps b (n + 1)]
  | .bvar _, _ => rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ | .app _ _, _
  | .forallE _ _ _, _ | .letE _ _ _ _, _ | .proj _ _ _, _ => rfl

theorem lamFirstArity_instantiateLevelParams_some (ps : List LevelParam) (ls : List KLevel) :
    ∀ (e : KExpr) (n k : Nat),
      lamFirstArity e n = some k →
      lamFirstArity (e.instantiateLevelParams ps ls) n = some k
  | .lam _ b m, n, k, h => by
    simp only [lamFirstArity] at h
    by_cases hpw : m.pw.isNever = true
    · rw [ite_eq_left hpw] at h
      have hpw' : (Level.substPW ps ls m.pw).isNever = true :=
        isNever_substPW_of_isNever hpw ps ls
      show (if (Level.substPW ps ls m.pw).isNever then
        lamFirstArity (b.instantiateLevelParams ps ls) (n + 1) else none) = some k
      rw [ite_eq_left hpw']
      exact lamFirstArity_instantiateLevelParams_some ps ls b (n + 1) k h
    · rw [ite_eq_right hpw] at h
      exact nomatch h
  | .bvar i, n, k, h => h
  | .fvar _ _, _, _, h | .sort _, _, _, h | .const _ _, _, _, h | .lit _, _, _, h
  | .app _ _, _, _, h | .forallE _ _ _, _, _, h | .letE _ _ _ _, _, _, h
  | .proj _ _ _, _, _, h => by simp [lamFirstArity] at h

theorem lamFirstArity_ge :
    ∀ (e : KExpr) (n k : Nat), lamFirstArity e n = some k → n ≤ k
  | .lam _ b m, n, k, h => by
    simp only [lamFirstArity] at h
    by_cases hpw : m.pw.isNever = true
    · rw [ite_eq_left hpw] at h
      have := lamFirstArity_ge b (n + 1) k h
      omega
    · rw [ite_eq_right hpw] at h
      exact nomatch h
  | .bvar i, n, k, h => by
    simp only [lamFirstArity] at h
    split at h
    · obtain rfl := Option.some.inj h
      exact Nat.le_refl _
    · exact nomatch h
  | .fvar _ _, _, _, h | .sort _, _, _, h | .const _ _, _, _, h | .lit _, _, _, h
  | .app _ _, _, _, h | .forallE _ _ _, _, _, h | .letE _ _ _ _, _, _, h
  | .proj _ _ _, _, _, h => by simp [lamFirstArity] at h

private inductive LamChain : Nat → KExpr → KExpr → Prop
  | zero (e : KExpr) : LamChain 0 e e
  | succ {m : Nat} {ty body leaf : KExpr} {mb : Ix.Kernel.BinderMeta} :
      mb.pw.isNever = true → LamChain m body leaf →
      LamChain (m + 1) (.lam ty body mb) leaf

private theorem lamFirstArity_to_chain :
    ∀ (w : KExpr) (n m : Nat),
      lamFirstArity w (n + 1) = some (n + 1 + m) → LamChain m w (.bvar (n + m))
  | .lam ty b mb, n, m, h => by
    simp only [lamFirstArity] at h
    by_cases hpw : mb.pw.isNever = true
    · rw [ite_eq_left hpw] at h
      cases m with
      | zero =>
        have hge := lamFirstArity_ge b (n + 2) (n + 1) (by simpa using h)
        omega
      | succ m' =>
        have h' : lamFirstArity b ((n + 1) + 1) = some ((n + 1) + 1 + m') := by
          rw [show (n + 1) + 1 + m' = n + 1 + (m' + 1) by omega]
          exact h
        have ih := lamFirstArity_to_chain b (n + 1) m' h'
        rw [show n + 1 + m' = n + (m' + 1) by omega] at ih
        exact .succ hpw ih
    · rw [ite_eq_right hpw] at h
      exact nomatch h
  | .bvar i, n, m, h => by
    simp only [lamFirstArity] at h
    split at h
    · next hcond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
      have hm0 : m = 0 := by
        have hk := Option.some.inj h
        omega
      subst hm0
      have hi : i = n := by omega
      subst hi
      simpa using LamChain.zero (.bvar i)
    · exact nomatch h
  | .fvar _ _, _, _, h | .sort _, _, _, h | .const _ _, _, _, h | .lit _, _, _, h
  | .app _ _, _, _, h | .forallE _ _ _, _, _, h | .letE _ _ _ _, _, _, h
  | .proj _ _ _, _, _, h => by simp [lamFirstArity] at h

private theorem LamChain.instantiate1 {m : Nat} {w leaf : KExpr}
    (h : LamChain m w leaf) (x : KExpr) :
    ∀ (j : Nat), LamChain m (w.instantiate1 x j) (leaf.instantiate1 x (j + m)) := by
  induction h with
  | zero e =>
    intro j
    simpa using LamChain.zero (e.instantiate1 x j)
  | @succ m' ty body lf mb hpw _ ih =>
    intro j
    have ih' := ih (j + 1)
    rw [show j + 1 + m' = j + (m' + 1) by omega] at ih'
    exact .succ hpw ih'

private theorem red_mkAppN_fn {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (args : List KExpr) {f f' : KExpr},
      Red env d f f' → Red env d (Expr.mkAppN f args) (Expr.mkAppN f' args)
  | [], _, _, h => h
  | a :: as, _, _, h => red_mkAppN_fn as (.appFn h)

private theorem LamChain.red {env : Ix.Kernel.Env .anon} {d : Nat} {a : KExpr}
    (ha : a.looseBVarsBounded 0 = true) :
    ∀ (rs : List KExpr) {w : KExpr},
      LamChain rs.length w a → Red env d (Expr.mkAppN w rs) a
  | [], w, h => by
    cases h with
    | zero => exact .refl
  | r :: rs, w, h => by
    cases h with
    | @succ _ ty body _ mb hpw hbody =>
      have hstep : Red env d (Expr.mkAppN (.lam ty body mb) (r :: rs))
          (Expr.mkAppN (body.instantiate1 r) rs) :=
        red_mkAppN_fn rs (.betaGate hpw)
      have hinst := hbody.instantiate1 r 0
      simp only [Nat.zero_add] at hinst
      rw [Expr.instantiate1_eq_self (Expr.looseBVarsBounded_mono (Nat.zero_le _) ha)] at hinst
      exact .trans hstep (LamChain.red ha rs hinst)

private theorem lbb_mkAppN :
    ∀ (args : List KExpr) (f : KExpr) (k : Nat),
      (Expr.mkAppN f args).looseBVarsBounded k =
        (f.looseBVarsBounded k && args.all (fun x => x.looseBVarsBounded k))
  | [], f, k => by simp [Expr.mkAppN]
  | a :: as, f, k => by
    rw [Expr.mkAppN, lbb_mkAppN as (.app f a) k]
    simp [Expr.looseBVarsBounded, Bool.and_assoc]

theorem consumeWrapper_red {env : Ix.Kernel.Env .anon} {d : Nat} {t a : KExpr}
    (hc : consumeWrapper env.find? t = some a)
    (hok : defnAritiesOk env.find? t = true)
    (hlbb : t.looseBVarsBounded 0 = true) :
    Red env d t a := by
  obtain ⟨w, us, rest, rfl, hw⟩ := Ix.Kernel.Semantics.consumeWrapper_inv hc
  have ha_lbb : a.looseBVarsBounded 0 = true := by
    rw [lbb_mkAppN, Bool.and_eq_true, List.all_cons, Bool.and_eq_true] at hlbb
    exact hlbb.2.1
  unfold wrapperArity at hw
  cases hfind : env.find? w with
  | none => rw [hfind] at hw; exact nomatch hw
  | some ci =>
    rw [hfind] at hw
    cases ci with
    | defnInfo cv v hn =>
      simp only at hw
      rw [defnAritiesOk_mkAppN, Bool.and_eq_true] at hok
      have hlen : us.length = cv.levelParams.length := by
        have hhd := hok.1
        simp only [defnAritiesOk, hfind, beq_iff_eq] at hhd
        exact hhd
      have hunf := unfold_const_mkAppN (a :: rest) hfind hlen
      have hdelta : Red env d (Expr.mkAppN (.const w us) (a :: rest))
          (Expr.mkAppN (v.instantiateLevelParams cv.levelParams us) (a :: rest)) :=
        .delta hunf
      have hlam :=
        lamFirstArity_instantiateLevelParams_some cv.levelParams us v 0 (rest.length + 1) hw
      cases hv' : v.instantiateLevelParams cv.levelParams us with
      | lam ty₀ b₀ mb₀ =>
        rw [hv'] at hlam hdelta
        simp only [lamFirstArity] at hlam
        by_cases hpw₀ : mb₀.pw.isNever = true
        · rw [ite_eq_left hpw₀] at hlam
          have hch₀ := lamFirstArity_to_chain b₀ 0 rest.length
            (by simpa [Nat.add_comm] using hlam)
          have hch₁ := hch₀.instantiate1 a 0
          simp only [Nat.zero_add, Expr.instantiate1, ite_eq_left rfl] at hch₁
          have hbeta₀ : Red env d (Expr.mkAppN (.lam ty₀ b₀ mb₀) (a :: rest))
              (Expr.mkAppN (b₀.instantiate1 a) rest) :=
            red_mkAppN_fn rest (.betaGate hpw₀)
          exact .trans hdelta (.trans hbeta₀ (LamChain.red ha_lbb rest hch₁))
        · rw [ite_eq_right hpw₀] at hlam
          exact nomatch hlam
      | bvar _ =>
        rw [hv'] at hlam
        simp [lamFirstArity] at hlam
      | _ =>
        rw [hv'] at hlam
        simp [lamFirstArity] at hlam
    | _ => simp at hw

theorem ConsumeStar.red {env : Ix.Kernel.Env .anon} {d : Nat} {t a : KExpr}
    (hs : ConsumeStar env.find? t a) (hok : defnAritiesOk env.find? t = true)
    (hlbb : t.looseBVarsBounded 0 = true) :
    Red env d t a := by
  have hP_ok : ∀ f x : KExpr, defnAritiesOk env.find? (.app f x) = true →
      defnAritiesOk env.find? f = true ∧ defnAritiesOk env.find? x = true := by
    intro f x hfx
    simpa [defnAritiesOk] using hfx
  have hP_lbb : ∀ f x : KExpr, (Expr.app f x).looseBVarsBounded 0 = true →
      f.looseBVarsBounded 0 = true ∧ x.looseBVarsBounded 0 = true := by
    intro f x hfx
    simpa [Expr.looseBVarsBounded] using hfx
  induction hs with
  | refl => exact .refl
  | step hc _ ih =>
    exact .trans (consumeWrapper_red hc hok hlbb)
      (ih
        (Ix.Kernel.Semantics.consumeWrapper_of
          (P := fun e => defnAritiesOk env.find? e = true) hP_ok hc hok)
        (Ix.Kernel.Semantics.consumeWrapper_of
          (P := fun e => e.looseBVarsBounded 0 = true) hP_lbb hc hlbb))

private theorem lbb_instantiate1_fvar (d : Nat) (ty : KExpr) :
    ∀ (e : KExpr) (j : Nat),
      e.looseBVarsBounded (j + 1) = true →
      (e.instantiate1 (.fvar d ty) j).looseBVarsBounded j = true
  | .bvar i, j, hb => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1]
    by_cases hij : i = j
    · simp [hij, Expr.looseBVarsBounded]
    · by_cases hgt : i > j
      · simp only [ite_eq_right hij, ite_eq_left hgt, Expr.looseBVarsBounded, decide_eq_true_eq]
        omega
      · simp only [ite_eq_right hij, ite_eq_right hgt, Expr.looseBVarsBounded, decide_eq_true_eq]
        omega
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, j, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, Expr.looseBVarsBounded,
      lbb_instantiate1_fvar d ty f j hb.1, lbb_instantiate1_fvar d ty a j hb.2]
  | .lam t b _, j, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, Expr.looseBVarsBounded,
      lbb_instantiate1_fvar d ty t j hb.1, lbb_instantiate1_fvar d ty b (j + 1) hb.2]
  | .forallE t b _, j, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, Expr.looseBVarsBounded,
      lbb_instantiate1_fvar d ty t j hb.1, lbb_instantiate1_fvar d ty b (j + 1) hb.2]
  | .letE t v b _, j, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, Expr.looseBVarsBounded,
      lbb_instantiate1_fvar d ty t j hb.1.1, lbb_instantiate1_fvar d ty v j hb.1.2,
      lbb_instantiate1_fvar d ty b (j + 1) hb.2]
  | .proj _ _ e, j, hb => by
    simp only [Expr.looseBVarsBounded] at hb
    simpa [Expr.instantiate1, Expr.looseBVarsBounded] using lbb_instantiate1_fvar d ty e j hb

private theorem letFree_instantiate1_fvar (d : Nat) (ty : KExpr) :
    ∀ (e : KExpr) (j : Nat),
      letFree e = true → letFree (e.instantiate1 (.fvar d ty) j) = true
  | .bvar i, j, _ => by
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, j, h => by
    simp only [letFree, Bool.and_eq_true] at h
    simp [Expr.instantiate1, letFree,
      letFree_instantiate1_fvar d ty f j h.1, letFree_instantiate1_fvar d ty a j h.2]
  | .lam t b _, j, h => by
    simp only [letFree, Bool.and_eq_true] at h
    simp [Expr.instantiate1, letFree,
      letFree_instantiate1_fvar d ty t j h.1, letFree_instantiate1_fvar d ty b (j + 1) h.2]
  | .forallE t b _, j, h => by
    simp only [letFree, Bool.and_eq_true] at h
    simp [Expr.instantiate1, letFree,
      letFree_instantiate1_fvar d ty t j h.1, letFree_instantiate1_fvar d ty b (j + 1) h.2]
  | .letE _ _ _ _, _, h => by simp [letFree] at h
  | .proj _ _ e, j, h => by
    simp only [letFree] at h
    simpa [Expr.instantiate1, letFree] using letFree_instantiate1_fvar d ty e j h

private theorem wrapTSem_defeq_go {env : Ix.Kernel.Env .anon} :
    ∀ (sz : Nat) {depth : Nat} {g d_e : KExpr},
      d_e.sizeB ≤ sz → WrapTSem env.find? g d_e → letFree d_e = true →
      defnAritiesOk env.find? g = true → g.looseBVarsBounded 0 = true →
      DefEq env depth g d_e
  | 0, _, _, _, hsz, hw, _, _, _ => by
    cases hw <;> simp [Expr.sizeB] at hsz
  | sz + 1, depth, g, d_e, hsz, hw, hl, hok, hlbb => by
    have hP_ok : ∀ f x : KExpr, defnAritiesOk env.find? (.app f x) = true →
        defnAritiesOk env.find? f = true ∧ defnAritiesOk env.find? x = true := by
      intro f x hfx
      simpa [defnAritiesOk] using hfx
    have hP_lbb : ∀ f x : KExpr, (Expr.app f x).looseBVarsBounded 0 = true →
        f.looseBVarsBounded 0 = true ∧ x.looseBVarsBounded 0 = true := by
      intro f x hfx
      simpa [Expr.looseBVarsBounded] using hfx
    cases hw with
    | bvar _ => exact .refl
    | fvar _ _ _ => exact .fvar
    | sort hu => exact .sort hu
    | const hus => exact .const hus
    | lit _ => exact .refl
    | app hf ha =>
      simp only [Expr.sizeB] at hsz
      simp only [letFree, defnAritiesOk, Expr.looseBVarsBounded, Bool.and_eq_true] at hl hok hlbb
      exact .app
        (wrapTSem_defeq_go sz (by omega) hf hl.1 hok.1 hlbb.1)
        (wrapTSem_defeq_go sz (by omega) ha hl.2 hok.2 hlbb.2)
    | @lam t a t' b b' m m' hpw hs hw_dom hw_body =>
      simp only [Expr.sizeB] at hsz
      simp only [letFree, defnAritiesOk, Expr.looseBVarsBounded, Bool.and_eq_true] at hl hok hlbb
      have hdom_a : DefEq env depth a t' :=
        wrapTSem_defeq_go sz (by omega) hw_dom hl.1
          (hs.of (P := fun e => defnAritiesOk env.find? e = true) hP_ok hok.1)
          (hs.of (P := fun e => e.looseBVarsBounded 0 = true) hP_lbb hlbb.1)
      have hdom : DefEq env depth t t' := .redL (ConsumeStar.red hs hok.1 hlbb.1) hdom_a
      have hbody_w : WrapTSem env.find?
          (b.instantiate1 (.fvar depth t')) (b'.instantiate1 (.fvar depth t')) :=
        WrapTSem.instantiate1 (.fvar depth t' t') hw_body 0
      have hbody_ok : defnAritiesOk env.find? (b.instantiate1 (.fvar depth t')) = true := by
        rw [defnAritiesOk_of_instantiate1_fvar]; exact hok.2
      have hbody_lbb : (b.instantiate1 (.fvar depth t')).looseBVarsBounded 0 = true :=
        lbb_instantiate1_fvar depth t' b 0 hlbb.2
      have hbody_lf : letFree (b'.instantiate1 (.fvar depth t')) = true :=
        letFree_instantiate1_fvar depth t' b' 0 hl.2
      have hbody : DefEq env (depth + 1)
          (b.instantiate1 (.fvar depth t')) (b'.instantiate1 (.fvar depth t')) :=
        wrapTSem_defeq_go sz (by rw [sizeB_instantiate1_fvar]; omega)
          hbody_w hbody_lf hbody_ok hbody_lbb
      exact .lam hdom hbody hpw
    | @forallE t a t' b b' m m' hpw hs hw_dom hw_body =>
      simp only [Expr.sizeB] at hsz
      simp only [letFree, defnAritiesOk, Expr.looseBVarsBounded, Bool.and_eq_true] at hl hok hlbb
      have hdom_a : DefEq env depth a t' :=
        wrapTSem_defeq_go sz (by omega) hw_dom hl.1
          (hs.of (P := fun e => defnAritiesOk env.find? e = true) hP_ok hok.1)
          (hs.of (P := fun e => e.looseBVarsBounded 0 = true) hP_lbb hlbb.1)
      have hdom : DefEq env depth t t' := .redL (ConsumeStar.red hs hok.1 hlbb.1) hdom_a
      have hbody_w : WrapTSem env.find?
          (b.instantiate1 (.fvar depth t')) (b'.instantiate1 (.fvar depth t')) :=
        WrapTSem.instantiate1 (.fvar depth t' t') hw_body 0
      have hbody_ok : defnAritiesOk env.find? (b.instantiate1 (.fvar depth t')) = true := by
        rw [defnAritiesOk_of_instantiate1_fvar]; exact hok.2
      have hbody_lbb : (b.instantiate1 (.fvar depth t')).looseBVarsBounded 0 = true :=
        lbb_instantiate1_fvar depth t' b 0 hlbb.2
      have hbody_lf : letFree (b'.instantiate1 (.fvar depth t')) = true :=
        letFree_instantiate1_fvar depth t' b' 0 hl.2
      have hbody : DefEq env (depth + 1)
          (b.instantiate1 (.fvar depth t')) (b'.instantiate1 (.fvar depth t')) :=
        wrapTSem_defeq_go sz (by rw [sizeB_instantiate1_fvar]; omega)
          hbody_w hbody_lf hbody_ok hbody_lbb
      exact .forallE hdom hbody hpw
    | letE _ _ _ => simp [letFree] at hl
    | proj he =>
      simp only [Expr.sizeB] at hsz
      simp only [letFree, defnAritiesOk, Expr.looseBVarsBounded] at hl hok hlbb
      exact .proj (wrapTSem_defeq_go sz (by omega) he hl hok hlbb)

/-- `WrapRelSem` on a `let`-free declared term `d_e` and loose-bvar-closed generated term `g`
implies kernel `DefEq env depth d_e g`. -/
theorem WrapRelSem.defeq {env : Ix.Kernel.Env .anon} {depth : Nat} {g d_e : KExpr}
    (h : WrapRelSem env.find? g d_e) (hl : letFree d_e = true)
    (hok : defnAritiesOk env.find? g = true) (hlbb : g.looseBVarsBounded 0 = true) :
    DefEq env depth d_e g :=
  .symm (wrapTSem_defeq_go d_e.sizeB (Nat.le_refl _) (h.toWrapTSem hl) hl hok hlbb)

private theorem substFn_congr (φ : LevelParam → Nat) :
    ∀ (ks : List LevelParam) {us vs : List KLevel},
      LvEqList us vs → ∀ n, Level.substFn φ ks us n = Level.substFn φ ks vs n
  | [], _, _, _, _ => rfl
  | _ :: _, [], [], _, _ => rfl
  | _ :: _, [], _ :: _, h, _ => False.elim (h φ)
  | _ :: _, _ :: _, [], h, _ => False.elim (h φ)
  | _ :: ks, _ :: _, _ :: _, h, n => by
    simp only [Level.substFn]
    split
    · exact (h φ).1
    · exact substFn_congr φ ks (fun ψ => (h ψ).2) n

private theorem lvEq_subst (ks : List LevelParam) {ls : List KLevel} {u u' : KLevel}
    (hu : LvEq u u') : LvEq (Level.subst ks ls u) (Level.subst ks ls u') := by
  intro φ
  rw [Level.eval_subst, Level.eval_subst, hu (Level.substFn φ ks ls)]

private theorem lvEqList_map_subst (ks : List LevelParam) (ls : List KLevel) :
    ∀ {us us' : List KLevel}, LvEqList us us' →
      LvEqList (us.map (Level.subst ks ls)) (us'.map (Level.subst ks ls))
  | [], [], _ => fun _ => trivial
  | [], _ :: _, h => False.elim (h (fun _ => 0))
  | _ :: _, [], h => False.elim (h (fun _ => 0))
  | _ :: _, _ :: _, h =>
    fun φ => ⟨lvEq_subst ks (fun ψ => (h ψ).1) φ,
      lvEqList_map_subst ks ls (fun ψ => (h ψ).2) φ⟩

private theorem liftLooseBVars_instantiateLevelParams (ps : List LevelParam) (ls : List KLevel)
    (amount : Nat) :
    ∀ (e : KExpr) (c : Nat),
      (e.liftLooseBVars amount c).instantiateLevelParams ps ls =
        (e.instantiateLevelParams ps ls).liftLooseBVars amount c
  | .bvar i, c => by
    by_cases hic : i ≥ c
    · simp [Expr.liftLooseBVars, Expr.instantiateLevelParams, hic]
    · simp [Expr.liftLooseBVars, Expr.instantiateLevelParams, hic]
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams ps ls amount f c,
      liftLooseBVars_instantiateLevelParams ps ls amount a c]
  | .lam t b _, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams ps ls amount t c,
      liftLooseBVars_instantiateLevelParams ps ls amount b (c + 1)]
  | .forallE t b _, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams ps ls amount t c,
      liftLooseBVars_instantiateLevelParams ps ls amount b (c + 1)]
  | .letE t v b _, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams ps ls amount t c,
      liftLooseBVars_instantiateLevelParams ps ls amount v c,
      liftLooseBVars_instantiateLevelParams ps ls amount b (c + 1)]
  | .proj _ _ e, c => by
    simpa [Expr.liftLooseBVars, Expr.instantiateLevelParams] using
      liftLooseBVars_instantiateLevelParams ps ls amount e c

private theorem instantiate1Lift_instantiateLevelParams (ps : List LevelParam) (ls : List KLevel)
    (v : KExpr) :
    ∀ (b : KExpr) (j : Nat),
      (b.instantiate1Lift v j).instantiateLevelParams ps ls =
        (b.instantiateLevelParams ps ls).instantiate1Lift (v.instantiateLevelParams ps ls) j
  | .bvar i, j => by
    by_cases hij : i = j
    · subst hij
      simpa [Expr.instantiate1Lift, Expr.instantiateLevelParams] using
        liftLooseBVars_instantiateLevelParams ps ls i v 0
    · by_cases hgt : i > j
      · simp [Expr.instantiate1Lift, Expr.instantiateLevelParams, hij, hgt]
      · simp [Expr.instantiate1Lift, Expr.instantiateLevelParams, hij, hgt]
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, j => by
    simp [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams ps ls v f j,
      instantiate1Lift_instantiateLevelParams ps ls v a j]
  | .lam t b _, j => by
    simp [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams ps ls v t j,
      instantiate1Lift_instantiateLevelParams ps ls v b (j + 1)]
  | .forallE t b _, j => by
    simp [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams ps ls v t j,
      instantiate1Lift_instantiateLevelParams ps ls v b (j + 1)]
  | .letE t w b _, j => by
    simp [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams ps ls v t j,
      instantiate1Lift_instantiateLevelParams ps ls v w j,
      instantiate1Lift_instantiateLevelParams ps ls v b (j + 1)]
  | .proj _ _ e, j => by
    simpa [Expr.instantiate1Lift, Expr.instantiateLevelParams] using
      instantiate1Lift_instantiateLevelParams ps ls v e j

private theorem mkAppN_instantiateLevelParams (ps : List LevelParam) (ls : List KLevel) :
    ∀ (args : List KExpr) (f : KExpr),
      (Expr.mkAppN f args).instantiateLevelParams ps ls =
        Expr.mkAppN (f.instantiateLevelParams ps ls)
          (args.map (fun x => x.instantiateLevelParams ps ls))
  | [], _ => rfl
  | a :: as, f => mkAppN_instantiateLevelParams ps ls as (.app f a)

theorem consumeWrapper_instantiateLevelParams {find? : KKey → Option (ConstantInfo .anon)}
    {t a : KExpr} (h : consumeWrapper find? t = some a)
    (ps : List LevelParam) (ls : List KLevel) :
    consumeWrapper find? (t.instantiateLevelParams ps ls) =
      some (a.instantiateLevelParams ps ls) := by
  obtain ⟨w, us, rest, rfl, hw⟩ := Ix.Kernel.Semantics.consumeWrapper_inv h
  rw [mkAppN_instantiateLevelParams]
  exact Ix.Kernel.Semantics.consumeWrapper_mkAppN (by simpa using hw)

theorem WrapRelSem.instantiateLevelParams {find? : KKey → Option (ConstantInfo .anon)}
    {g d : KExpr} (h : WrapRelSem find? g d) (ps : List LevelParam) (ls : List KLevel) :
    WrapRelSem find? (g.instantiateLevelParams ps ls) (d.instantiateLevelParams ps ls) :=
  WrapRelSem.rec
    (motive_1 := fun g d _ =>
      WrapRelSem find? (g.instantiateLevelParams ps ls) (d.instantiateLevelParams ps ls))
    (motive_2 := fun t t' _ =>
      WrapDomSem find? (t.instantiateLevelParams ps ls) (t'.instantiateLevelParams ps ls))
    (bvar := fun i => .bvar i)
    (fvar := fun _ iht => .fvar iht)
    (sort := fun hu => .sort (lvEq_subst ps hu))
    (const := fun hus => .const (lvEqList_map_subst ps ls hus))
    (lit := fun l => .lit l)
    (app := fun _ _ ihf iha => .app ihf iha)
    (lam := fun hpw _ _ ihd ihb =>
      .lam (show Level.substPW ps ls _ = Level.substPW ps ls _ by rw [hpw]) ihd ihb)
    (forallE := fun hpw _ _ ihd ihb =>
      .forallE (show Level.substPW ps ls _ = Level.substPW ps ls _ by rw [hpw]) ihd ihb)
    (letE := fun _ _ _ iht ihv ihb => .letE iht ihv ihb)
    (proj := fun _ ihe => .proj ihe)
    (zeta := fun _ ihz => by
      rw [instantiate1Lift_instantiateLevelParams] at ihz
      exact .zeta ihz)
    (keep := fun _ ihr => .keep ihr)
    (consume := fun hc _ ihd =>
      .consume (consumeWrapper_instantiateLevelParams hc ps ls) ihd)
    h

theorem WrapRelSem.of_posOf_perm {find? : KKey → Option (ConstantInfo .anon)}
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length)) {g d : KExpr}
    (h : WrapRelSem find? (posOf ps g) (posOf ps d)) :
    WrapRelSem find? g d := by
  have hinst := h.instantiateLevelParams (List.range ps.length) (ps.map .param)
  rwa [posOf_perm_inv hperm g, posOf_perm_inv hperm d] at hinst

/-! ## Section 2: `Tm.close`, local `expr_lift`, and `expr_has_bvar_at = 0` -/

private theorem liftLooseBVars_abstract1 (j d : Nat) :
    ∀ (e : KExpr) (k c : Nat),
      (e.liftLooseBVars j c).abstract1 d (k + j + c) =
        (e.abstract1 d (k + c)).liftLooseBVars j c
  | .bvar m, k, c => by
    by_cases hmc : m ≥ c
    · simp [Expr.liftLooseBVars, Expr.abstract1, hmc]
    · simp [Expr.liftLooseBVars, Expr.abstract1, hmc]
  | .fvar idx ty, k, c => by
    by_cases hidx : idx = d
    · subst hidx
      simp [Expr.liftLooseBVars, Expr.abstract1, show k + c ≥ c by omega]
      omega
    · simp [Expr.liftLooseBVars, Expr.abstract1, hidx]
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, k, c => by
    simp [Expr.liftLooseBVars, Expr.abstract1,
      liftLooseBVars_abstract1 j d f k c, liftLooseBVars_abstract1 j d a k c]
  | .lam t b _, k, c => by
    simp only [Expr.liftLooseBVars, Expr.abstract1]
    rw [liftLooseBVars_abstract1 j d t k c,
      show k + j + c + 1 = k + j + (c + 1) by omega,
      show k + c + 1 = k + (c + 1) by omega,
      liftLooseBVars_abstract1 j d b k (c + 1)]
  | .forallE t b _, k, c => by
    simp only [Expr.liftLooseBVars, Expr.abstract1]
    rw [liftLooseBVars_abstract1 j d t k c,
      show k + j + c + 1 = k + j + (c + 1) by omega,
      show k + c + 1 = k + (c + 1) by omega,
      liftLooseBVars_abstract1 j d b k (c + 1)]
  | .letE t v b _, k, c => by
    simp only [Expr.liftLooseBVars, Expr.abstract1]
    rw [liftLooseBVars_abstract1 j d t k c,
      liftLooseBVars_abstract1 j d v k c,
      show k + j + c + 1 = k + j + (c + 1) by omega,
      show k + c + 1 = k + (c + 1) by omega,
      liftLooseBVars_abstract1 j d b k (c + 1)]
  | .proj _ _ e, k, c => by
    simpa [Expr.liftLooseBVars, Expr.abstract1] using liftLooseBVars_abstract1 j d e k c

private theorem instantiate1Lift_abstract1 (v : KExpr) (d k : Nat) :
    ∀ (b : KExpr) (j : Nat),
      (b.instantiate1Lift v j).abstract1 d (k + j) =
        (b.abstract1 d (k + j + 1)).instantiate1Lift (v.abstract1 d k) j
  | .bvar i, j => by
    by_cases hij : i = j
    · subst i
      simp [Expr.instantiate1Lift, Expr.abstract1]
      simpa using liftLooseBVars_abstract1 j d v k 0
    · by_cases hgt : i > j
      · simp [Expr.instantiate1Lift, Expr.abstract1, hij, hgt]
      · simp [Expr.instantiate1Lift, Expr.abstract1, hij, hgt]
  | .fvar idx ty, j => by
    by_cases hidx : idx = d
    · subst hidx
      simp [Expr.instantiate1Lift, Expr.abstract1,
        show k + j + 1 ≠ j by omega, show k + j + 1 > j by omega]
    · simp [Expr.instantiate1Lift, Expr.abstract1, hidx]
  | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, j => by
    simp [Expr.instantiate1Lift, Expr.abstract1,
      instantiate1Lift_abstract1 v d k f j, instantiate1Lift_abstract1 v d k a j]
  | .lam t b _, j => by
    simp only [Expr.instantiate1Lift, Expr.abstract1]
    rw [instantiate1Lift_abstract1 v d k t j,
      show k + j + 1 = k + (j + 1) by omega,
      instantiate1Lift_abstract1 v d k b (j + 1)]
  | .forallE t b _, j => by
    simp only [Expr.instantiate1Lift, Expr.abstract1]
    rw [instantiate1Lift_abstract1 v d k t j,
      show k + j + 1 = k + (j + 1) by omega,
      instantiate1Lift_abstract1 v d k b (j + 1)]
  | .letE t w b _, j => by
    simp only [Expr.instantiate1Lift, Expr.abstract1]
    rw [instantiate1Lift_abstract1 v d k t j,
      instantiate1Lift_abstract1 v d k w j,
      show k + j + 1 = k + (j + 1) by omega,
      instantiate1Lift_abstract1 v d k b (j + 1)]
  | .proj _ _ e, j => by
    simpa [Expr.instantiate1Lift, Expr.abstract1] using instantiate1Lift_abstract1 v d k e j

/-- Close one opened variable at `d` back into local binder `k`. -/
theorem tm_close {κ : _root_.Address → KKey} {d : Nat} {Γ Γ' : Nat → KExpr} {h : Heap F}
    (hΓ : ∀ j, j < d → Γ' j = Γ j) {k : Nat} {E : KExpr} {p : SourceValue F}
    (rep : Tm κ (d + 1) Γ h k E p) :
    Tm κ d Γ' h (k + 1) (E.abstract1 d k) p := by
  induction rep with
  | @bvarLocal k₁ addr i cell hs hi =>
    exact .bvarLocal cell hs (by omega)
  | @bvarFree k₁ addr i cell hs hk hd =>
    simp only [Expr.abstract1]
    by_cases hik : ZMod.val i = k₁
    · have hf_eq : fvIdx (d + 1) k₁ (ZMod.val i) = d := by unfold fvIdx; omega
      rw [ite_eq_left hf_eq, ← hik]
      exact .bvarLocal cell hs (by omega)
    · have hf_ne : fvIdx (d + 1) k₁ (ZMod.val i) ≠ d := by unfold fvIdx; omega
      rw [ite_eq_right hf_ne]
      have hf_eq : fvIdx (d + 1) k₁ (ZMod.val i) = fvIdx d (k₁ + 1) (ZMod.val i) := by
        unfold fvIdx; omega
      rw [hf_eq, ← hΓ _ (by unfold fvIdx; omega)]
      exact .bvarFree cell hs (by omega) (by omega)
  | sort cell rl hu => exact .sort cell rl hu
  | const cell ra rls hus => exact .const cell ra rls hus
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | @letE k₁ addr tp vp bp T₀ V B cell _ _ _ iht ihv ihb =>
    have hcomm := instantiate1Lift_abstract1 V d k₁ B 0
    simp only [Nat.add_zero] at hcomm
    rw [show (instShift V 0 B).abstract1 d k₁ = (B.instantiate1Lift V 0).abstract1 d k₁ from rfl,
      hcomm]
    exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

/-- Every free variable in `e` has index `< d` (ignoring fvar types). -/
def fvarIdxLt (d : Nat) : KExpr → Bool
  | .fvar idx _ => decide (idx < d)
  | .app f a => fvarIdxLt d f && fvarIdxLt d a
  | .lam t b _ => fvarIdxLt d t && fvarIdxLt d b
  | .forallE t b _ => fvarIdxLt d t && fvarIdxLt d b
  | .letE t v b _ => fvarIdxLt d t && fvarIdxLt d v && fvarIdxLt d b
  | .proj _ _ e => fvarIdxLt d e
  | _ => true

private theorem fvarIdxLt_liftLooseBVars (d : Nat) :
    ∀ (e : KExpr) (n c : Nat), fvarIdxLt d (e.liftLooseBVars n c) = fvarIdxLt d e
  | .bvar _, n, c => by simp only [Expr.liftLooseBVars]; split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, n, c => by
    simp [Expr.liftLooseBVars, fvarIdxLt,
      fvarIdxLt_liftLooseBVars d f n c, fvarIdxLt_liftLooseBVars d a n c]
  | .lam t b _, n, c => by
    simp [Expr.liftLooseBVars, fvarIdxLt,
      fvarIdxLt_liftLooseBVars d t n c, fvarIdxLt_liftLooseBVars d b n (c + 1)]
  | .forallE t b _, n, c => by
    simp [Expr.liftLooseBVars, fvarIdxLt,
      fvarIdxLt_liftLooseBVars d t n c, fvarIdxLt_liftLooseBVars d b n (c + 1)]
  | .letE t v b _, n, c => by
    simp [Expr.liftLooseBVars, fvarIdxLt,
      fvarIdxLt_liftLooseBVars d t n c, fvarIdxLt_liftLooseBVars d v n c,
      fvarIdxLt_liftLooseBVars d b n (c + 1)]
  | .proj _ _ e, n, c => by
    simpa [Expr.liftLooseBVars, fvarIdxLt] using fvarIdxLt_liftLooseBVars d e n c

private theorem fvarIdxLt_instantiate1Lift {d : Nat} {v : KExpr} (hv : fvarIdxLt d v = true) :
    ∀ (e : KExpr) (j : Nat), fvarIdxLt d e = true → fvarIdxLt d (e.instantiate1Lift v j) = true
  | .bvar i, j, _ => by
    simp only [Expr.instantiate1Lift]
    split
    · rw [fvarIdxLt_liftLooseBVars]; exact hv
    · split <;> rfl
  | .fvar _ _, _, h => h
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, fvarIdxLt, Bool.and_eq_true]
    exact ⟨fvarIdxLt_instantiate1Lift hv f j h.1, fvarIdxLt_instantiate1Lift hv a j h.2⟩
  | .lam t b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, fvarIdxLt, Bool.and_eq_true]
    exact ⟨fvarIdxLt_instantiate1Lift hv t j h.1, fvarIdxLt_instantiate1Lift hv b (j + 1) h.2⟩
  | .forallE t b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, fvarIdxLt, Bool.and_eq_true]
    exact ⟨fvarIdxLt_instantiate1Lift hv t j h.1, fvarIdxLt_instantiate1Lift hv b (j + 1) h.2⟩
  | .letE t w b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, fvarIdxLt, Bool.and_eq_true]
    exact ⟨⟨fvarIdxLt_instantiate1Lift hv t j h.1.1, fvarIdxLt_instantiate1Lift hv w j h.1.2⟩,
      fvarIdxLt_instantiate1Lift hv b (j + 1) h.2⟩
  | .proj _ _ e, j, h => by
    simp only [fvarIdxLt] at h
    simpa [Expr.instantiate1Lift, fvarIdxLt] using fvarIdxLt_instantiate1Lift hv e j h

theorem tm_fvarIdxLt {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ d Γ h k E p) :
    fvarIdxLt d E = true := by
  induction rep with
  | bvarLocal _ _ _ | sort _ _ _ | const _ _ _ _ | litNat _ _ _ | litStr _ _ _ => rfl
  | @bvarFree k₁ _ i _ _ hk hd =>
    simp only [fvarIdxLt, decide_eq_true_eq]
    unfold fvIdx; omega
  | app _ _ _ ihf iha => simp [fvarIdxLt, ihf, iha]
  | lam _ _ _ _ iht ihb => simp [fvarIdxLt, iht, ihb]
  | forallE _ _ _ _ iht ihb => simp [fvarIdxLt, iht, ihb]
  | letE _ _ _ _ _ ihv ihb => exact fvarIdxLt_instantiate1Lift ihv _ 0 ihb
  | proj _ _ _ ihe => simpa [fvarIdxLt] using ihe

theorem abstract1_instantiate1_cancel {d : Nat} (ty : KExpr) :
    ∀ {e : KExpr} (k : Nat),
      fvarIdxLt d e = true → e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1 (.fvar d ty) k).abstract1 d k = e
  | .bvar i, k, _, hb => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1]
    by_cases hik : i = k
    · subst hik
      simp [Expr.abstract1]
    · rw [ite_eq_right hik, ite_eq_right (by omega)]
      rfl
  | .fvar idx fty, k, hf, _ => by
    simp only [fvarIdxLt, decide_eq_true_eq] at hf
    simp [Expr.instantiate1, Expr.abstract1, Nat.ne_of_lt hf]
  | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .app f a, k, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_cancel ty k hf.1 hb.1,
      abstract1_instantiate1_cancel ty k hf.2 hb.2]
  | .lam t b _, k, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_cancel ty k hf.1 hb.1,
      abstract1_instantiate1_cancel ty (k + 1) hf.2 hb.2]
  | .forallE t b _, k, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_cancel ty k hf.1 hb.1,
      abstract1_instantiate1_cancel ty (k + 1) hf.2 hb.2]
  | .letE t v b _, k, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_cancel ty k hf.1.1 hb.1.1,
      abstract1_instantiate1_cancel ty k hf.1.2 hb.1.2,
      abstract1_instantiate1_cancel ty (k + 1) hf.2 hb.2]
  | .proj _ _ e, k, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded] at hf hb
    simpa [Expr.instantiate1, Expr.abstract1] using abstract1_instantiate1_cancel ty k hf hb

private def openDummies : Nat → Nat → Nat → KExpr → KExpr
  | 0, _, _, e => e
  | m + 1, d, c, e => openDummies m (d + 1) c (e.instantiate1 (.fvar d (.sort .zero)) (c + m))

private def closeDummies : Nat → Nat → Nat → KExpr → KExpr
  | 0, _, _, e => e
  | m + 1, d, c', e => (closeDummies m (d + 1) c' e).abstract1 d (c' + m)

private theorem tm_openDummies {κ : _root_.Address → KKey} {h : Heap F} :
    ∀ (m d c : Nat) {E : KExpr} {p : SourceValue F},
      Tm κ d (fun _ => .sort .zero) h (c + m) E p →
      Tm κ (d + m) (fun _ => .sort .zero) h c (openDummies m d c E) p
  | 0, d, c, _, _, rep => by simpa [openDummies] using rep
  | m + 1, d, c, E, p, rep => by
    have hop := rep.open (Γ' := fun _ => .sort .zero) (T := .sort .zero)
      rfl (fun _ _ => rfl) (c + m) (by omega)
    have ih := tm_openDummies m (d + 1) c hop
    rwa [show d + 1 + m = d + (m + 1) by omega] at ih

private theorem tm_closeDummies {κ : _root_.Address → KKey} {h : Heap F} :
    ∀ (m d c' : Nat) {E : KExpr} {p : SourceValue F},
      Tm κ (d + m) (fun _ => .sort .zero) h c' E p →
      Tm κ d (fun _ => .sort .zero) h (c' + m) (closeDummies m d c' E) p
  | 0, d, c', _, _, rep => by simpa [closeDummies] using rep
  | m + 1, d, c', E, p, rep => by
    rw [show d + (m + 1) = (d + 1) + m by omega] at rep
    have ih := tm_closeDummies m (d + 1) c' rep
    have hcl := tm_close (Γ' := fun _ => .sort .zero) (fun _ _ => rfl) ih
    simpa [closeDummies, Nat.add_assoc] using hcl

private theorem liftLooseBVars_of_bounded (shift : Nat) :
    ∀ {e : KExpr} (c : Nat),
      e.looseBVarsBounded c = true → e.liftLooseBVars shift c = e
  | .bvar i, c, hb => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.liftLooseBVars, ite_eq_right (show ¬ c ≤ i by omega)]
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, c, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.liftLooseBVars, liftLooseBVars_of_bounded shift c hb.1,
      liftLooseBVars_of_bounded shift c hb.2]
  | .lam t b _, c, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.liftLooseBVars, liftLooseBVars_of_bounded shift c hb.1,
      liftLooseBVars_of_bounded shift (c + 1) hb.2]
  | .forallE t b _, c, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.liftLooseBVars, liftLooseBVars_of_bounded shift c hb.1,
      liftLooseBVars_of_bounded shift (c + 1) hb.2]
  | .letE t v b _, c, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.liftLooseBVars, liftLooseBVars_of_bounded shift c hb.1.1,
      liftLooseBVars_of_bounded shift c hb.1.2,
      liftLooseBVars_of_bounded shift (c + 1) hb.2]
  | .proj _ _ e, c, hb => by
    simp only [Expr.looseBVarsBounded] at hb
    simpa [Expr.liftLooseBVars] using liftLooseBVars_of_bounded shift c hb

private theorem abstract1_lift_instantiate1_step (d shift : Nat) :
    ∀ {e : KExpr} (c m : Nat),
      fvarIdxLt d e = true → e.looseBVarsBounded (c + m + 1) = true →
      ((e.instantiate1 (.fvar d (.sort .zero)) (c + m)).liftLooseBVars shift c).abstract1 d
        (c + shift + m) = e.liftLooseBVars shift c
  | .bvar i, c, m, _, hb => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1]
    by_cases him : i = c + m
    · subst him
      simp [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1, show c + m ≥ c by omega]
      omega
    · rw [ite_eq_right him, ite_eq_right (by omega)]
      by_cases hic : i ≥ c
      · simp [Expr.liftLooseBVars, Expr.abstract1, hic]
      · simp [Expr.liftLooseBVars, Expr.abstract1, hic]
  | .fvar idx ty, c, m, hf, _ => by
    simp only [fvarIdxLt, decide_eq_true_eq] at hf
    simp [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1, Nat.ne_of_lt hf]
  | .sort _, _, _, _, _ | .const _ _, _, _, _, _ | .lit _, _, _, _, _ => rfl
  | .app f a, c, m, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1,
      abstract1_lift_instantiate1_step d shift c m hf.1 hb.1,
      abstract1_lift_instantiate1_step d shift c m hf.2 hb.2]
  | .lam t b _, c, m, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp only [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1]
    rw [abstract1_lift_instantiate1_step d shift c m hf.1 hb.1]
    have hb' : b.looseBVarsBounded ((c + 1) + m + 1) = true := by
      rw [show (c + 1) + m + 1 = c + m + 1 + 1 by omega]; exact hb.2
    have step_b := abstract1_lift_instantiate1_step d shift (c + 1) m hf.2 hb'
    rw [show c + 1 + m = c + m + 1 by omega,
      show c + 1 + shift + m = c + shift + m + 1 by omega] at step_b
    rw [step_b]
  | .forallE t b _, c, m, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp only [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1]
    rw [abstract1_lift_instantiate1_step d shift c m hf.1 hb.1]
    have hb' : b.looseBVarsBounded ((c + 1) + m + 1) = true := by
      rw [show (c + 1) + m + 1 = c + m + 1 + 1 by omega]; exact hb.2
    have step_b := abstract1_lift_instantiate1_step d shift (c + 1) m hf.2 hb'
    rw [show c + 1 + m = c + m + 1 by omega,
      show c + 1 + shift + m = c + shift + m + 1 by omega] at step_b
    rw [step_b]
  | .letE t v b _, c, m, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp only [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1]
    rw [abstract1_lift_instantiate1_step d shift c m hf.1.1 hb.1.1,
      abstract1_lift_instantiate1_step d shift c m hf.1.2 hb.1.2]
    have hb' : b.looseBVarsBounded ((c + 1) + m + 1) = true := by
      rw [show (c + 1) + m + 1 = c + m + 1 + 1 by omega]; exact hb.2
    have step_b := abstract1_lift_instantiate1_step d shift (c + 1) m hf.2 hb'
    rw [show c + 1 + m = c + m + 1 by omega,
      show c + 1 + shift + m = c + shift + m + 1 by omega] at step_b
    rw [step_b]
  | .proj _ _ e, c, m, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded] at hf hb
    simpa [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1] using
      abstract1_lift_instantiate1_step d shift c m hf hb

private theorem fvarIdxLt_mono {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) :
    ∀ {e : KExpr}, fvarIdxLt d₁ e = true → fvarIdxLt d₂ e = true
  | .fvar idx _, h => by
    simp only [fvarIdxLt, decide_eq_true_eq] at h ⊢
    omega
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h ⊢
    exact ⟨fvarIdxLt_mono hle h.1, fvarIdxLt_mono hle h.2⟩
  | .lam t b _, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h ⊢
    exact ⟨fvarIdxLt_mono hle h.1, fvarIdxLt_mono hle h.2⟩
  | .forallE t b _, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h ⊢
    exact ⟨fvarIdxLt_mono hle h.1, fvarIdxLt_mono hle h.2⟩
  | .letE t v b _, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h ⊢
    exact ⟨⟨fvarIdxLt_mono hle h.1.1, fvarIdxLt_mono hle h.1.2⟩, fvarIdxLt_mono hle h.2⟩
  | .proj _ _ e, h => by
    simp only [fvarIdxLt] at h ⊢
    exact fvarIdxLt_mono hle h

private theorem hasFvar_false_of_fvarIdxLt_zero :
    ∀ {e : KExpr}, fvarIdxLt 0 e = true → e.hasFvar = false
  | .fvar _ _, h => by simp [fvarIdxLt] at h
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.hasFvar, hasFvar_false_of_fvarIdxLt_zero h.1, hasFvar_false_of_fvarIdxLt_zero h.2]
  | .lam t b _, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.hasFvar, hasFvar_false_of_fvarIdxLt_zero h.1, hasFvar_false_of_fvarIdxLt_zero h.2]
  | .forallE t b _, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.hasFvar, hasFvar_false_of_fvarIdxLt_zero h.1, hasFvar_false_of_fvarIdxLt_zero h.2]
  | .letE t v b _, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.hasFvar, hasFvar_false_of_fvarIdxLt_zero h.1.1,
      hasFvar_false_of_fvarIdxLt_zero h.1.2, hasFvar_false_of_fvarIdxLt_zero h.2]
  | .proj _ _ e, h => by
    simp only [fvarIdxLt] at h
    simpa [Expr.hasFvar] using hasFvar_false_of_fvarIdxLt_zero h

private theorem fvarIdxLt_instantiate1_fvar {d : Nat} :
    ∀ {e : KExpr} (j : Nat), fvarIdxLt d e = true →
      fvarIdxLt (d + 1) (e.instantiate1 (.fvar d (.sort .zero)) j) = true
  | .bvar i, j, _ => by
    simp only [Expr.instantiate1]
    split
    · simp [fvarIdxLt]
    · split <;> rfl
  | .fvar idx ty, _, h => fvarIdxLt_mono (Nat.le_succ d) h
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarIdxLt,
      fvarIdxLt_instantiate1_fvar j h.1, fvarIdxLt_instantiate1_fvar j h.2]
  | .lam t b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarIdxLt,
      fvarIdxLt_instantiate1_fvar j h.1, fvarIdxLt_instantiate1_fvar (j + 1) h.2]
  | .forallE t b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarIdxLt,
      fvarIdxLt_instantiate1_fvar j h.1, fvarIdxLt_instantiate1_fvar (j + 1) h.2]
  | .letE t v b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarIdxLt,
      fvarIdxLt_instantiate1_fvar j h.1.1, fvarIdxLt_instantiate1_fvar j h.1.2,
      fvarIdxLt_instantiate1_fvar (j + 1) h.2]
  | .proj _ _ e, j, h => by
    simp only [fvarIdxLt] at h
    simpa [Expr.instantiate1, fvarIdxLt] using fvarIdxLt_instantiate1_fvar j h

private theorem closeDummies_openDummies (shift : Nat) :
    ∀ (m d c : Nat) {e : KExpr},
      fvarIdxLt d e = true → e.looseBVarsBounded (c + m) = true →
      closeDummies m d (c + shift) (openDummies m d c e) = e.liftLooseBVars shift c
  | 0, d, c, e, _, hb => by
    simp only [openDummies, closeDummies, Nat.add_zero] at hb ⊢
    exact (liftLooseBVars_of_bounded shift c hb).symm
  | m + 1, d, c, e, hf, hb => by
    simp only [openDummies, closeDummies]
    have hf' : fvarIdxLt (d + 1) (e.instantiate1 (.fvar d (.sort .zero)) (c + m)) = true :=
      fvarIdxLt_instantiate1_fvar (c + m) hf
    have hb' : (e.instantiate1 (.fvar d (.sort .zero)) (c + m)).looseBVarsBounded (c + m) = true :=
      lbb_instantiate1_fvar d (.sort .zero) e (c + m)
        (by rwa [show c + m + 1 = c + (m + 1) by omega])
    rw [closeDummies_openDummies shift m (d + 1) c hf' hb']
    exact abstract1_lift_instantiate1_step d shift c m hf
      (by rwa [show c + m + 1 = c + (m + 1) by omega])

/-- `KernelSubst::expr_lift(pe, shift, cut)` on a `Tm` term at `d = 0` and local binder depth
`k ≥ cut` produces `E.liftLooseBVars shift cut` at local binder depth `k + shift`. -/
theorem expr_lift_local_spec {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {k shift cut : Nat} {E : KExpr} {pe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hcut_le : cut ≤ k)
    (hshift_lt : shift < 4611686018427387904)
    (hcut_lt : cut < 4294967296)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hE : Tm κ 0 Γ₀ h k E pe)
    (ev : ObsFn W "KernelSubst::expr_lift" [pe, .field (shift : F), .field (cut : F)] h r h' cs) :
    Tm κ 0 Γ₀ h' (k + shift) (E.liftLooseBVars shift cut) r := by
  let m := k - cut
  have hk_eq : k = cut + m := by omega
  have hE₀ : Tm κ 0 (fun _ => .sort .zero) h (cut + m) E pe := by
    rw [← hk_eq]
    exact hE.congr_ghost (fun _ hj => by omega)
  have hop : Tm κ m (fun _ => .sort .zero) h cut (openDummies m 0 cut E) pe := by
    simpa using tm_openDummies m 0 cut hE₀
  have hval_s : ZMod.val (shift : F) = shift :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hshift_lt (by decide))
  have hval_c : ZMod.val (cut : F) = cut :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hcut_lt (by decide))
  have hlift := SubstAux.gall κ .expr_lift _ _ _ _ _ ev pe (shift : F) (cut : F) rfl hbnd
    (by rw [hval_s]; exact hshift_lt) shift 0 (by rw [hval_s]; omega) m (fun _ => .sort .zero)
    (openDummies m 0 cut E) (by rwa [hval_c])
  rw [hval_c, Nat.add_zero] at hlift
  have hcl : Tm κ 0 (fun _ => .sort .zero) h' (cut + shift + m)
      (closeDummies m 0 (cut + shift) (openDummies m 0 cut E)) r :=
    tm_closeDummies m 0 (cut + shift) (by simpa using hlift)
  rw [closeDummies_openDummies shift m 0 cut (tm_fvarIdxLt hE₀) hE₀.looseBVarsBounded,
    show cut + shift + m = k + shift by omega] at hcl
  exact hcl.congr_ghost (fun _ hj => by omega)

private theorem hasLooseBVar_lift_false (s : Nat) :
    ∀ (v : KExpr) (c i : Nat),
      c ≤ i → v.hasLooseBVar i = false → (v.liftLooseBVars s c).hasLooseBVar (i + s) = false
  | .bvar k, c, i, hci, hv => by
    simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne] at hv
    by_cases hkc : k ≥ c
    · simp only [Expr.liftLooseBVars, ite_eq_left hkc, Expr.hasLooseBVar, beq_eq_false_iff_ne]
      omega
    · simp only [Expr.liftLooseBVars, ite_eq_right hkc, Expr.hasLooseBVar, beq_eq_false_iff_ne]
      omega
  | .fvar _ _, _, _, _, _ | .sort _, _, _, _, _ | .const _ _, _, _, _, _ | .lit _, _, _, _, _ => rfl
  | .app f a, c, i, hci, hv => by
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hv
    simp [Expr.liftLooseBVars, Expr.hasLooseBVar,
      hasLooseBVar_lift_false s f c i hci hv.1,
      hasLooseBVar_lift_false s a c i hci hv.2]
  | .lam t b _, c, i, hci, hv => by
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hv
    simp only [Expr.liftLooseBVars, Expr.hasLooseBVar, Bool.or_eq_false_iff]
    refine ⟨hasLooseBVar_lift_false s t c i hci hv.1, ?_⟩
    have hb := hasLooseBVar_lift_false s b (c + 1) (i + 1) (by omega) hv.2
    rwa [show i + 1 + s = i + s + 1 by omega] at hb
  | .forallE t b _, c, i, hci, hv => by
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hv
    simp only [Expr.liftLooseBVars, Expr.hasLooseBVar, Bool.or_eq_false_iff]
    refine ⟨hasLooseBVar_lift_false s t c i hci hv.1, ?_⟩
    have hb := hasLooseBVar_lift_false s b (c + 1) (i + 1) (by omega) hv.2
    rwa [show i + 1 + s = i + s + 1 by omega] at hb
  | .letE t w b _, c, i, hci, hv => by
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hv
    simp only [Expr.liftLooseBVars, Expr.hasLooseBVar, Bool.or_eq_false_iff]
    refine ⟨⟨hasLooseBVar_lift_false s t c i hci hv.1.1,
      hasLooseBVar_lift_false s w c i hci hv.1.2⟩, ?_⟩
    have hb := hasLooseBVar_lift_false s b (c + 1) (i + 1) (by omega) hv.2
    rwa [show i + 1 + s = i + s + 1 by omega] at hb
  | .proj _ _ e, c, i, hci, hv => by
    simp only [Expr.hasLooseBVar] at hv
    simpa [Expr.liftLooseBVars, Expr.hasLooseBVar] using hasLooseBVar_lift_false s e c i hci hv

private theorem hasLooseBVar_instantiate1Lift_false (v : KExpr) :
    ∀ (b : KExpr) (j i : Nat),
      j ≤ i → v.hasLooseBVar (i - j) = false → b.hasLooseBVar (i + 1) = false →
      (b.instantiate1Lift v j).hasLooseBVar i = false
  | .bvar k, j, i, hji, hv, hb => by
    simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne] at hb
    simp only [Expr.instantiate1Lift]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_eq_left rfl]
      have hlift := hasLooseBVar_lift_false k v 0 (i - k) (Nat.zero_le _) hv
      rwa [show i - k + k = i by omega] at hlift
    · by_cases hgt : k > j
      · simp only [ite_eq_right hkj, ite_eq_left hgt, Expr.hasLooseBVar, beq_eq_false_iff_ne]
        omega
      · simp only [ite_eq_right hkj, ite_eq_right hgt, Expr.hasLooseBVar, beq_eq_false_iff_ne]
        omega
  | .fvar _ _, _, _, _, _, _ | .sort _, _, _, _, _, _
  | .const _ _, _, _, _, _, _ | .lit _, _, _, _, _, _ => rfl
  | .app f a, j, i, hji, hv, hb => by
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hb
    simp [Expr.instantiate1Lift, Expr.hasLooseBVar,
      hasLooseBVar_instantiate1Lift_false v f j i hji hv hb.1,
      hasLooseBVar_instantiate1Lift_false v a j i hji hv hb.2]
  | .lam t b _, j, i, hji, hv, hb => by
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hb
    simp only [Expr.instantiate1Lift, Expr.hasLooseBVar, Bool.or_eq_false_iff]
    refine ⟨hasLooseBVar_instantiate1Lift_false v t j i hji hv hb.1, ?_⟩
    exact hasLooseBVar_instantiate1Lift_false v b (j + 1) (i + 1) (by omega)
      (by rwa [show i + 1 - (j + 1) = i - j by omega]) hb.2
  | .forallE t b _, j, i, hji, hv, hb => by
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hb
    simp only [Expr.instantiate1Lift, Expr.hasLooseBVar, Bool.or_eq_false_iff]
    refine ⟨hasLooseBVar_instantiate1Lift_false v t j i hji hv hb.1, ?_⟩
    exact hasLooseBVar_instantiate1Lift_false v b (j + 1) (i + 1) (by omega)
      (by rwa [show i + 1 - (j + 1) = i - j by omega]) hb.2
  | .letE t w b _, j, i, hji, hv, hb => by
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hb
    simp only [Expr.instantiate1Lift, Expr.hasLooseBVar, Bool.or_eq_false_iff]
    refine ⟨⟨hasLooseBVar_instantiate1Lift_false v t j i hji hv hb.1.1,
      hasLooseBVar_instantiate1Lift_false v w j i hji hv hb.1.2⟩, ?_⟩
    exact hasLooseBVar_instantiate1Lift_false v b (j + 1) (i + 1) (by omega)
      (by rwa [show i + 1 - (j + 1) = i - j by omega]) hb.2
  | .proj _ _ e, j, i, hji, hv, hb => by
    simp only [Expr.hasLooseBVar] at hb
    simpa [Expr.instantiate1Lift, Expr.hasLooseBVar] using
      hasLooseBVar_instantiate1Lift_false v e j i hji hv hb

private theorem hasLooseBVar_false_of_idxAll {κ : _root_.Address → KKey} {d : Nat}
    {Γ : Nat → KExpr} {h : Heap F} (j : Nat) :
    ∀ {m k : Nat} {E : KExpr} {pe : SourceValue F},
      Tm κ d Γ h k E pe →
      Specs.Subst.IdxAll h (fun m' i => ZMod.val i < j + m' ∨ j + 1 + m' ≤ ZMod.val i) m pe →
      j + m < k →
      E.hasLooseBVar (j + m) = false
  | m, k, _, _, .bvarLocal cell _ _, hidx, _ => by
    cases hidx with
    | bvar cell' hP =>
      obtain ⟨_, hxs⟩ := load_cell cell (loadValue_enum_cell cell')
      injection hxs with hi_eq
      have hval : ZMod.val _ = ZMod.val _ := congrArg ZMod.val (Value.field.inj hi_eq)
      rw [← hval] at hP
      simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne]
      omega
    | sort cell' | const cell' | lit cell' | app cell' _ _ | lam cell' _ _
    | forallE cell' _ _ | letE cell' _ _ _ | proj cell' _ =>
      exact False.elim (load_cell_ne cell (loadValue_enum_cell cell') (by decide))
  | _, _, _, _, .bvarFree _ _ _ _, _, _ => rfl
  | _, _, _, _, .sort _ _ _, _, _ => rfl
  | _, _, _, _, .const _ _ _ _, _, _ => rfl
  | _, _, _, _, .litNat _ _ _, _, _ => rfl
  | _, _, _, _, .litStr _ _ _, _, _ => rfl
  | m, k, _, _, .app cell hf ha, hidx, hjk => by
    cases hidx with
    | app cell' hif hia =>
      obtain ⟨_, hxs⟩ := load_cell cell (loadValue_enum_cell cell')
      injection hxs with h1 hxs; injection hxs with h2 _
      subst h1 h2
      simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
      exact ⟨hasLooseBVar_false_of_idxAll j hf hif hjk,
        hasLooseBVar_false_of_idxAll j ha hia hjk⟩
    | bvar cell' _ | sort cell' | const cell' | lit cell' | lam cell' _ _
    | forallE cell' _ _ | letE cell' _ _ _ | proj cell' _ =>
      exact False.elim (load_cell_ne cell (loadValue_enum_cell cell') (by decide))
  | m, k, _, _, .lam cell ht hb _, hidx, hjk => by
    cases hidx with
    | lam cell' hit hib =>
      obtain ⟨_, hxs⟩ := load_cell cell (loadValue_enum_cell cell')
      injection hxs with h1 hxs; injection hxs with h2 _
      subst h1 h2
      simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
      refine ⟨hasLooseBVar_false_of_idxAll j ht hit hjk, ?_⟩
      have hib' := hasLooseBVar_false_of_idxAll j hb hib (by omega)
      rwa [show j + (m + 1) = j + m + 1 by omega] at hib'
    | bvar cell' _ | sort cell' | const cell' | lit cell' | app cell' _ _
    | forallE cell' _ _ | letE cell' _ _ _ | proj cell' _ =>
      exact False.elim (load_cell_ne cell (loadValue_enum_cell cell') (by decide))
  | m, k, _, _, .forallE cell ht hb _, hidx, hjk => by
    cases hidx with
    | forallE cell' hit hib =>
      obtain ⟨_, hxs⟩ := load_cell cell (loadValue_enum_cell cell')
      injection hxs with h1 hxs; injection hxs with h2 _
      subst h1 h2
      simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
      refine ⟨hasLooseBVar_false_of_idxAll j ht hit hjk, ?_⟩
      have hib' := hasLooseBVar_false_of_idxAll j hb hib (by omega)
      rwa [show j + (m + 1) = j + m + 1 by omega] at hib'
    | bvar cell' _ | sort cell' | const cell' | lit cell' | app cell' _ _
    | lam cell' _ _ | letE cell' _ _ _ | proj cell' _ =>
      exact False.elim (load_cell_ne cell (loadValue_enum_cell cell') (by decide))
  | m, k, _, _, .letE (B := B) cell ht hv hb, hidx, hjk => by
    cases hidx with
    | letE cell' _ hiv hib =>
      obtain ⟨_, hxs⟩ := load_cell cell (loadValue_enum_cell cell')
      injection hxs with _ hxs; injection hxs with h2 hxs; injection hxs with h3 _
      subst h2 h3
      have hv_false := hasLooseBVar_false_of_idxAll j hv hiv hjk
      have hb_false : B.hasLooseBVar (j + m + 1) = false := by
        have := hasLooseBVar_false_of_idxAll j hb hib (by omega)
        rwa [show j + (m + 1) = j + m + 1 by omega] at this
      exact hasLooseBVar_instantiate1Lift_false _ B 0 (j + m) (Nat.zero_le _)
        (by simpa using hv_false) hb_false
    | bvar cell' _ | sort cell' | const cell' | lit cell' | app cell' _ _
    | lam cell' _ _ | forallE cell' _ _ | proj cell' _ =>
      exact False.elim (load_cell_ne cell (loadValue_enum_cell cell') (by decide))
  | m, k, _, _, .proj cell _ he, hidx, hjk => by
    cases hidx with
    | proj cell' hie =>
      obtain ⟨_, hxs⟩ := load_cell cell (loadValue_enum_cell cell')
      injection hxs with _ hxs; injection hxs with _ hxs; injection hxs with h3 _
      subst h3
      simpa [Expr.hasLooseBVar] using hasLooseBVar_false_of_idxAll j he hie hjk
    | bvar cell' _ | sort cell' | const cell' | lit cell' | app cell' _ _
    | lam cell' _ _ | forallE cell' _ _ | letE cell' _ _ _ =>
      exact False.elim (load_cell_ne cell (loadValue_enum_cell cell') (by decide))

/-- `KernelSubst::expr_has_bvar_at(pe, j)` returning `.field 0` on `Tm` at local depth `k > j`
certifies `E.hasLooseBVar j = false` and leaves the heap unchanged. -/
theorem expr_has_bvar_at_zero_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k j : Nat} {E : KExpr} {pe : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hjk : j < k) (hj_lt : j < 4294967296)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hE : Tm κ d Γ h k E pe)
    (ev : ObsFn W "KernelSubst::expr_has_bvar_at" [pe, .field (j : F)] h (.field 0) h' cs) :
    E.hasLooseBVar j = false ∧ h' = h := by
  obtain ⟨hh, _, hno⟩ := SubstAux.gall κ .expr_has_bvar_at _ _ _ _ _ ev pe (j : F) rfl hbnd
  have hval : ZMod.val (j : F) = j :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt (by decide))
  have hidx := hno rfl d Γ k E hE
  rw [hval] at hidx
  exact ⟨by simpa using hasLooseBVar_false_of_idxAll j hE hidx (by omega), hh⟩

/-! ## Section 3: `lam_first_arity`, `consume_wrapper`, and `wrap_rel` specs -/

private theorem tm_lam_descent {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p w20 xb xm : SourceValue F} {steps : Nat}
    (hE : Tm κ d Γ h k E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Lam" [w20, xb, xm]))
    (hdesc : RomBound.HeapDescent h (.enum kexprEnum) xb steps) :
    RomBound.HeapDescent h (.enum kexprEnum) p (steps + 1) := by
  cases hE with
  | @lam _ addr tp bp lp _ _ _ cell _ _ _ =>
    obtain ⟨_, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2 _
    subst h1 h2
    exact .down cell (by simp [Value.type]) (by simp [RomBound.cellArgs]) hdesc
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
  | app cell _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact False.elim (load_cell_ne cell ld (by decide))

private theorem tm_ptr_descent_zero {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F}
    (hE : Tm κ d Γ h k E p) :
    RomBound.HeapDescent h (.enum kexprEnum) p 0 := by
  cases hE with
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
  | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _
  | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact .here cell (by simp [Value.type])

private theorem lam_first_arity_go {κ : _root_.Address → KKey} {Γ : Nat → KExpr} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelCheck::lam_first_arity" →
      ∀ (n : Nat) (E : KExpr) (xv xk : SourceValue F),
        args = [xv, .field (n : F)] → r = .tuple [.field 1, xk] →
        (∀ steps, RomBound.HeapDescent h (.enum kexprEnum) xv steps → n + steps < 549755813888) →
        Tm κ 0 Γ h n E xv →
        ∃ k_out steps : Nat,
          xk = .field (k_out : F) ∧
          k_out = n + steps ∧
          RomBound.HeapDescent h (.enum kexprEnum) xv steps ∧
          lamFirstArity E n = some k_out ∧
          h' = h :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelCheck::lam_first_arity" →
      ∀ (n : Nat) (E : KExpr) (xv xk : SourceValue F),
        args = [xv, .field (n : F)] → r = .tuple [.field 1, xk] →
        (∀ steps, RomBound.HeapDescent h (.enum kexprEnum) xv steps → n + steps < 549755813888) →
        Tm κ 0 Γ h n E xv →
        ∃ k_out steps : Nat,
          xk = .field (k_out : F) ∧
          k_out = n + steps ∧
          RomBound.HeapDescent h (.enum kexprEnum) xv steps ∧
          lamFirstArity E n = some k_out ∧
          h' = h)
    (fun fname args h r h' cs ev ih hfn n E xv xk hargs hr hbnd_desc hE => by
      subst hfn hargs hr
      match Obs.«KernelCheck::lam_first_arity».obs ev with
      | .Lam_Succ_other (he118 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .Lam_other (he141 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .BVar_n0 (he186 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .BVar_other_other (he264 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .other (he287 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .Lam_Succ_Zero (w20 := w20) (x_b := xb) (x_m := xm) (x_z := xz)
          (cs82 := cs82) (v86 := v86)
          (ld12 := ld12) (ld47 := ld47) (ld71 := ld71)
          (op107 := op107) (ev84 := ev84) (hc109 := hc109) =>
        subst hc109
        obtain ⟨T, B, ℓ, rfl, _, hB, hℓ⟩ := hE.lam_of_load ld12
        obtain ⟨u, rfl, hu⟩ := Levels.rep_succ_of_load hℓ ld47
        obtain rfl := Levels.rep_zero_of_load hu ld71
        have hv86 : v86 = .field ((n + 1 : Nat) : F) := evalBinOp_add_one n op107
        rw [hv86] at ev84
        have hbnd_b : ∀ steps, RomBound.HeapDescent h (.enum kexprEnum) xb steps →
            (n + 1) + steps < 549755813888 := by
          intro steps hdb
          have hdp := tm_lam_descent hE ld12 hdb
          have hlt := hbnd_desc (steps + 1) hdp
          omega
        obtain ⟨k_out, steps, hxk, hk_eq, hdb, hlam, hh⟩ :=
          ih _ _ _ _ _ _ (by rec_lt_calls) ev84 rfl (n + 1) B xb xk rfl rfl hbnd_b hB
        refine ⟨k_out, steps + 1, hxk, by omega, tm_lam_descent hE ld12 hdb, ?_, hh⟩
        simpa [lamFirstArity, bmeta, Level.zeronessOf] using hlam
      | .BVar_other_n0 (x_i := xi) (y215 := y215)
          (ld12 := ld12) (hne201 := hne201) (op230 := op230) (op221 := op221)
          (he240 := he240) (he254 := he254) .. =>
        injection he240 with hxs; injection hxs with _ hxs; injection hxs with hxk _
        have hxk' : xk = .field (n : F) := hxk
        have hn_pos : 0 < n := by
          cases n with
          | zero => exact absurd rfl hne201
          | succ _ => omega
        cases n with
        | zero => omega
        | succ m =>
          have hy215 : y215 = .field (m : F) := evalBinOp_sub_succ m op230
          obtain ⟨i_f, rfl, _, hbvar⟩ := hE.bvar_of_load ld12
          rcases hbvar with ⟨hi_lt, rfl⟩ | ⟨_, hbad, _⟩
          · rw [hy215] at op221
            simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
              Except.ok.injEq, Value.field.injEq] at op221
            have hif : i_f = (m : F) := sub_eq_zero.mp op221
            have hn_lt : m + 1 < 549755813888 := by
              have := hbnd_desc 0 (tm_ptr_descent_zero hE)
              omega
            have hval_i : ZMod.val i_f = m := by
              rw [hif]
              exact ZMod.val_natCast_of_lt (Nat.lt_trans (by omega : m < 549755813888) (by decide))
            refine ⟨m + 1, 0, hxk', by omega, tm_ptr_descent_zero hE, ?_, he254⟩
            simp [lamFirstArity, hval_i]
          · omega)

/-- Soundness of `KernelCheck::consume_wrapper` returning `(.field 1, x_a)` under `Good c cs`. -/
theorem consume_wrapper_one_spec {c : Ctx} {d : Nat} {Γ : Nat → KExpr}
    {T : KExpr} {xt xa : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hlf : LoadFacts c) (hgood : Good c cs)
    (hT : Tm c.κ d Γ h 0 T xt)
    (ev : ObsFn W "KernelCheck::consume_wrapper" [xt] h (.tuple [.field 1, xa]) h' cs) :
    ∃ A : KExpr, consumeWrapper c.env.find? T = some A ∧ Tm c.κ d Γ h' 0 A xa := by
  match Obs.«KernelCheck::consume_wrapper».obsx ev with
  | .Const_Cons_Defn_n1_bind_other (he276 := he) .. =>
    injection he with hxs; injection hxs with h10 _
    exact absurd (Value.field.inj h10) one_ne_zero
  | .Const_Cons_Defn_other (he299 := he) .. =>
    injection he with hxs; injection hxs with h10 _
    exact absurd (Value.field.inj h10) one_ne_zero
  | .Const_Cons_other (he323 := he) .. =>
    injection he with hxs; injection hxs with h10 _
    exact absurd (Value.field.inj h10) one_ne_zero
  | .Const_other (he347 := he) .. =>
    injection he with hxs; injection hxs with h10 _
    exact absurd (Value.field.inj h10) one_ne_zero
  | .other (he371 := he) .. =>
    injection he with hxs; injection hxs with h10 _
    exact absurd (Value.field.inj h10) one_ne_zero
  | .Const_Cons_Defn_n1_bind_n0 (m2 := m2) (cs12 := cs12) (x_h := xh) (x_args := xargs)
      (x_w := xw) (w55 := w55) (x_a := xa') (x_rest := xrest) (m96 := m96) (p104 := p104)
      (cs110 := cs110) (w127 := w127) (w128 := w128) (x_v := xv) (w129 := w129) (w130 := w130)
      (m157 := m157) (cs168 := cs168) (x_k := xk) (y214 := y214) (x222 := x222)
      (m224 := m224) (cs233 := cs233)
      (ev14 := ev14) (ld47 := ld47) (ld77 := ld77) (ev112 := ev112) (ld106 := ld106)
      (ev170 := ev170) (ev235 := ev235) (op229 := op229) (op220 := op220)
      (he252 := he252) (he266 := he266) (hc267 := hc267) =>
    subst hc267 he266
    injection he252 with hxs; injection hxs with _ hxs; injection hxs with hxa_eq _
    subst hxa_eq
    have hbnd_sp : IxVM.Consistency.Bounded cs12 :=
      RomBound.bounded_mono hgood.2 (fun z hz => by simp [hz])
    obtain ⟨hd, sp, H, As, hpair, hH, hAs, rfl⟩ :=
      SubstAux.gall c.κ .collect_spine _ _ _ _ _ ev14 xt rfl hbnd_sp d Γ 0 T hT
    injection hpair with hlist; injection hlist with hhd hlist; injection hlist with hsp _
    subst hhd hsp
    obtain ⟨aw, us, rfl, haw, _, _, _⟩ := hH.const_of_load ld47
    obtain ⟨A, rest, rfl, hA, hrest⟩ := RepList.cons_of_load hAs ld77
    have hg_ci : Good c cs110 := hgood.sub (fun z hz => by simp [hz])
    obtain ⟨ci, hfind, p_v, hp_ld, hci_rep⟩ := hlf.getCI xw p104 m2 m96 cs110 aw ev112 hg_ci haw
    rw [hp_ld] at ld106
    injection ld106 with hv_eq
    subst hv_eq
    obtain ⟨cv, V, hn, rfl, _, hV⟩ := CIRep.defn_inv hci_rep
    have e_ci := ev112.heap_extends
    have hbnd_call_lfa :
        ∀ steps, RomBound.HeapDescent m96 (.enum kexprEnum) xv steps →
          0 + steps < 549755813888 := by
      intro steps hdesc
      have hlt := RomBound.bounded_descent_lt hgood.2
        (c := ⟨"KernelCheck::lam_first_arity", [xv, .field 0], m96⟩)
        (by simp) List.mem_cons_self hdesc
      simpa using hlt
    obtain ⟨k_out, steps_v, hxk, hk_steps, hdesc_xv, hlam_pos, hm157⟩ :=
      lam_first_arity_go _ _ _ _ _ _ ev170 rfl 0 (posOf cv.levelParams V) xv xk
        rfl rfl hbnd_call_lfa (hV 0 (fun _ => default))
    subst m157
    rw [lamFirstArity_posOf] at hlam_pos
    have hrest_m96 : RepList kexprListEnum (fun h E p => Tm c.κ d Γ h 0 E p) m96 rest xrest :=
      repList_heapMono₂ kexprListEnum (fun _ _ _ _ ext r => r.mono ext) e_ci hrest
    have hlen_rest_lt : rest.length < 549755813888 :=
      RomBound.bounded_length_lt hgood.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [xrest], m96⟩)
        (by simp) List.mem_cons_self hrest_m96
    obtain ⟨hx222, rfl⟩ :=
      Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
        (R := fun h E p => Tm c.κ d Γ h 0 E p)
        (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev235)
        (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hrest_m96)
    rw [hx222] at op229
    have hy214 : y214 = .field ((rest.length + 1 : Nat) : F) :=
      evalBinOp_add_one rest.length op229
    rw [hxk, hy214] at op220
    simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
      Except.ok.injEq, Value.field.injEq] at op220
    have hk_lt : k_out < 549755813888 := by
      have := hbnd_call_lfa steps_v hdesc_xv
      omega
    have hk_eq : k_out = rest.length + 1 := by
      have hf : (k_out : F) = ((rest.length + 1 : Nat) : F) := sub_eq_zero.mp op220
      have hv1 : ((k_out : F)).val = k_out :=
        ZMod.val_natCast_of_lt (Nat.lt_trans hk_lt (by decide))
      have hv2 : (((rest.length + 1 : Nat) : F)).val = rest.length + 1 :=
        ZMod.val_natCast_of_lt (Nat.lt_trans (show rest.length + 1 < 549755813889 by omega) (by decide))
      have hv := congrArg ZMod.val hf
      omega
    subst hk_eq
    have hwrap : wrapperArity c.env.find? (c.κ (ixAddr aw)) = some (rest.length + 1) := by
      simp [wrapperArity, hfind, hlam_pos]
    exact ⟨A, Ix.Kernel.Semantics.consumeWrapper_mkAppN hwrap, hA.mono e_ci⟩

private theorem wrap_rel_family {c : Ctx} (hlf : LoadFacts c) :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → r = .field 1 → Good c cs →
      ((fname = "KernelCheck::wrap_rel" →
        ∀ (d : Nat) (Γ : Nat → KExpr) (G D : KExpr) (xg xd : SourceValue F),
          args = [xg, xd] → Tm c.κ d Γ h 0 G xg → Tm c.κ d Γ h 0 D xd →
          WrapTSem c.env.find? G D) ∧
       (fname = "KernelCheck::wrap_dom" →
        ∀ (d : Nat) (Γ : Nat → KExpr) (T T2 : KExpr) (xt xt2 : SourceValue F),
          args = [xt, xt2] → Tm c.κ d Γ h 0 T xt → Tm c.κ d Γ h 0 T2 xt2 →
          ∃ A : KExpr, ConsumeStar c.env.find? T A ∧ WrapTSem c.env.find? A T2) ∧
       (fname = "KernelCheck::wrap_binder" →
        ∀ (d : Nat) (Γ : Nat → KExpr) (T B T2 B2 : KExpr) (ℓ ℓ2 : KLevel)
          (xt xb xm xt2 xb2 xm2 : SourceValue F),
          args = [xt, xb, xm, xt2, xb2, xm2] →
          Tm c.κ d Γ h 0 T xt → Tm c.κ d Γ h 1 B xb → RepKLevel h ℓ xm →
          Tm c.κ d Γ h 0 T2 xt2 → Tm c.κ d Γ h 1 B2 xb2 → RepKLevel h ℓ2 xm2 →
          (bmeta ℓ).pw = (bmeta ℓ2).pw ∧
          (∃ A : KExpr, ConsumeStar c.env.find? T A ∧ WrapTSem c.env.find? A T2) ∧
          WrapTSem c.env.find? B B2)) :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => r = .field 1 → Good c cs →
      ((fname = "KernelCheck::wrap_rel" →
        ∀ (d : Nat) (Γ : Nat → KExpr) (G D : KExpr) (xg xd : SourceValue F),
          args = [xg, xd] → Tm c.κ d Γ h 0 G xg → Tm c.κ d Γ h 0 D xd →
          WrapTSem c.env.find? G D) ∧
       (fname = "KernelCheck::wrap_dom" →
        ∀ (d : Nat) (Γ : Nat → KExpr) (T T2 : KExpr) (xt xt2 : SourceValue F),
          args = [xt, xt2] → Tm c.κ d Γ h 0 T xt → Tm c.κ d Γ h 0 T2 xt2 →
          ∃ A : KExpr, ConsumeStar c.env.find? T A ∧ WrapTSem c.env.find? A T2) ∧
       (fname = "KernelCheck::wrap_binder" →
        ∀ (d : Nat) (Γ : Nat → KExpr) (T B T2 B2 : KExpr) (ℓ ℓ2 : KLevel)
          (xt xb xm xt2 xb2 xm2 : SourceValue F),
          args = [xt, xb, xm, xt2, xb2, xm2] →
          Tm c.κ d Γ h 0 T xt → Tm c.κ d Γ h 1 B xb → RepKLevel h ℓ xm →
          Tm c.κ d Γ h 0 T2 xt2 → Tm c.κ d Γ h 1 B2 xb2 → RepKLevel h ℓ2 xm2 →
          (bmeta ℓ).pw = (bmeta ℓ2).pw ∧
          (∃ A : KExpr, ConsumeStar c.env.find? T A ∧ WrapTSem c.env.find? A T2) ∧
          WrapTSem c.env.find? B B2)))
    (fun fname args h r h' cs ev ih hr hgood => by
      subst hr
      refine ⟨fun hfn d Γ G D xg xd hargs hG hD => ?_,
        fun hfn d Γ T T2 xt xt2 hargs hT hT2 => ?_,
        fun hfn d Γ T B T2 B2 ℓ ℓ2 xt xb xm xt2 xb2 xm2 hargs hT hB hℓ hT2 hB2 hℓ2 => ?_⟩
      · subst hfn hargs
        match Obs.«KernelCheck::wrap_rel».obs ev with
        | .other_other_App_App_other (he301 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_App_other (he308 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_Lam_other (he426 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_Forall_other (he544 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_Proj_Proj_other (he696 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_Proj_other (he703 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let (w20 := w20) (x_v := xv) (x_b := xb) (cs39 := cs39) (v42 := v42)
            (m45 := m45) (cs53 := cs53)
            (ld12 := ld12) (ev55 := ev55) (ev41 := ev41) (hc86 := hc86) =>
          subst hc86
          obtain ⟨_, V, B, rfl, _, hV, hB⟩ := hG.letE_of_load ld12
          have hbnd53 : IxVM.Consistency.Bounded cs53 :=
            RomBound.bounded_mono hgood.2 (fun z hz => by simp [hz])
          have hinst : Tm c.κ d Γ m45 0 (instShift V 0 B) v42 := by
            have hi := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ ev55 xb xv 0 rfl hbnd53
              d Γ B V (by simpa using hB) hV
            simpa [instShift_eq_instantiate1 hV.looseBVarsBounded 0 B] using hi
          have e1 := ev55.heap_extends
          exact (ih _ _ _ _ _ _ (by rec_lt_calls) ev41 rfl
            (hgood.sub fun z hz => by simp [hz])).1 rfl d Γ (instShift V 0 B) D v42 xd rfl
            hinst (hD.mono e1)
        | .other_Let (w110 := w110) (x_v2 := xv2) (x_b2 := xb2) (cs129 := cs129)
            (v133 := v133) (m142 := m142) (cs150 := cs150)
            (ld102 := ld102) (ev152 := ev152) (ev131 := ev131) (hc176 := hc176) .. =>
          subst hc176
          obtain ⟨_, V2, B2, rfl, _, hV2, hB2⟩ := hD.letE_of_load ld102
          have hbnd150 : IxVM.Consistency.Bounded cs150 :=
            RomBound.bounded_mono hgood.2 (fun z hz => by simp [hz])
          have hinst : Tm c.κ d Γ m142 0 (instShift V2 0 B2) v133 := by
            have hi := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ ev152 xb2 xv2 0 rfl hbnd150
              d Γ B2 V2 (by simpa using hB2) hV2
            simpa [instShift_eq_instantiate1 hV2.looseBVarsBounded 0 B2] using hi
          have e1 := ev152.heap_extends
          exact (ih _ _ _ _ _ _ (by rec_lt_calls) ev131 rfl
            (hgood.sub fun z hz => by simp [hz])).1 rfl d Γ G (instShift V2 0 B2) xg v133 rfl
            (hG.mono e1) hinst
        | .other_other_App_App_n1 (x_f := xf) (x_a := xa) (x_f2 := xf2) (x_a2 := xa2)
            (m240 := m240) (cs251 := cs251) (cs277 := cs277)
            (ld192 := ld192) (ld221 := ld221) (ev253 := ev253) (ev279 := ev279)
            (hc296 := hc296) .. =>
          subst hc296
          obtain ⟨Ef, Ea, rfl, hEf, hEa⟩ := hG.app_of_load ld192
          obtain ⟨Ef2, Ea2, rfl, hEf2, hEa2⟩ := hD.app_of_load ld221
          have e1 := ev253.heap_extends
          exact .app
            ((ih _ _ _ _ _ _ (by rec_lt_calls) ev253 rfl
              (hgood.sub fun z hz => by simp [hz])).1 rfl d Γ Ef Ef2 xf xf2 rfl hEf hEf2)
            ((ih _ _ _ _ _ _ (by rec_lt_calls) ev279 rfl
              (hgood.sub fun z hz => by simp [hz])).1 rfl d Γ Ea Ea2 xa xa2 rfl
              (hEa.mono e1) (hEa2.mono e1))
        | .other_other_Lam_Lam (x_t := xt) (x_b := xb) (x_m := xm)
            (x_t2 := xt2) (x_b2 := xb2) (x_m2 := xm2) (cs370 := cs370)
            (ld192 := ld192) (ld344 := ld344) (ev372 := ev372) (hc421 := hc421) .. =>
          subst hc421
          obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hG.lam_of_load ld192
          obtain ⟨T2, B2, ℓ2, rfl, hT2, hB2, hℓ2⟩ := hD.lam_of_load ld344
          obtain ⟨hpw, ⟨A, hs, hw_dom⟩, hw_body⟩ :=
            (ih _ _ _ _ _ _ (by rec_lt_calls) ev372 rfl
              (hgood.sub fun z hz => by simp [hz])).2.2 rfl d Γ T B T2 B2 ℓ ℓ2
              xt xb xm xt2 xb2 xm2 rfl hT hB hℓ hT2 hB2 hℓ2
          exact .lam hpw hs hw_dom hw_body
        | .other_other_Forall_Forall (x_t := xt) (x_b := xb) (x_m := xm)
            (x_t2 := xt2) (x_b2 := xb2) (x_m2 := xm2) (cs488 := cs488)
            (ld192 := ld192) (ld462 := ld462) (ev490 := ev490) (hc539 := hc539) .. =>
          subst hc539
          obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hG.forallE_of_load ld192
          obtain ⟨T2, B2, ℓ2, rfl, hT2, hB2, hℓ2⟩ := hD.forallE_of_load ld462
          obtain ⟨hpw, ⟨A, hs, hw_dom⟩, hw_body⟩ :=
            (ih _ _ _ _ _ _ (by rec_lt_calls) ev490 rfl
              (hgood.sub fun z hz => by simp [hz])).2.2 rfl d Γ T B T2 B2 ℓ ℓ2
              xt xb xm xt2 xb2 xm2 rfl hT hB hℓ hT2 hB2 hℓ2
          exact .forallE hpw hs hw_dom hw_body
        | .other_other_Proj_Proj_n1 (x_s := xs) (x_i := xi) (x_e := xe)
            (x_s2 := xs2) (x_i2 := xi2) (x_e2 := xe2) (m604 := m604)
            (x612 := x612) (y613 := y613) (m614 := m614)
            (cs623 := cs623) (cs645 := cs645) (v648 := v648) (cs672 := cs672)
            (ld192 := ld192) (ld580 := ld580) (ev625 := ev625) (op662 := op662)
            (ev647 := ev647) (op619 := op619) (ev674 := ev674) (hc691 := hc691) .. =>
          subst hc691
          obtain ⟨sa, fa, Ea, rfl, rfl, hsa, hEa⟩ := hG.proj_of_load ld192
          obtain ⟨sb, fb, Eb, rfl, rfl, hsb, hEb⟩ := hD.proj_of_load ld580
          obtain ⟨haddr, rfl⟩ := Lib.address_eq_spec ev625 hsa hsb
          obtain ⟨hiz, rfl⟩ := Lib.is_zero_spec ev647
          have hs_eq : sa = sb := by
            by_cases hab : sa = sb
            · exact hab
            · rw [ite_eq_right hab] at haddr
              rw [haddr, hiz] at op619
              simp [evalBinOp, bind, Except.bind, pure, Except.pure] at op619
          subst hs_eq
          have hv648 : v648 = .field 0 := by
            by_cases h0 : v648 = .field 0
            · exact h0
            · rw [hiz, ite_eq_right h0, haddr] at op619
              simp [evalBinOp, bind, Except.bind, pure, Except.pure] at op619
          rw [hv648] at op662
          simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
            Except.ok.injEq, Value.field.injEq] at op662
          have hfeq : fa = fb := sub_eq_zero.mp op662
          subst hfeq
          exact .proj
            ((ih _ _ _ _ _ _ (by rec_lt_calls) ev674 rfl
              (hgood.sub fun z hz => by simp [hz])).1 rfl d Γ Ea Eb xe xe2 rfl hEa hEb)
        | .other_other_other (cs713 := cs713) (ev715 := ev715) (hc732 := hc732) .. =>
          subst hc732
          exact (kexpr_struct_eq_tm_one hG hD ev715).toWrapTSem c.env.find?
      · subst hfn hargs
        match Obs.«KernelCheck::wrap_dom».obsx ev with
        | .other_other_other (he200 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let (w20 := w20) (x_v := xv) (x_b := xb) (cs39 := cs39) (v42 := v42)
            (m45 := m45) (cs53 := cs53)
            (ld12 := ld12) (ev55 := ev55) (ev41 := ev41) (hc86 := hc86) =>
          subst hc86
          obtain ⟨_, V, B, rfl, _, hV, hB⟩ := hT.letE_of_load ld12
          have hbnd53 : IxVM.Consistency.Bounded cs53 :=
            RomBound.bounded_mono hgood.2 (fun z hz => by simp [hz])
          have hinst : Tm c.κ d Γ m45 0 (instShift V 0 B) v42 := by
            have hi := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ ev55 xb xv 0 rfl hbnd53
              d Γ B V (by simpa using hB) hV
            simpa [instShift_eq_instantiate1 hV.looseBVarsBounded 0 B] using hi
          have e1 := ev55.heap_extends
          exact (ih _ _ _ _ _ _ (by rec_lt_calls) ev41 rfl
            (hgood.sub fun z hz => by simp [hz])).2.1 rfl d Γ (instShift V 0 B) T2 v42 xt2 rfl
            hinst (hT2.mono e1)
        | .other_n1 (cs103 := cs103) (ev105 := ev105) (hc128 := hc128) .. =>
          subst hc128
          have hw := (ih _ _ _ _ _ _ (by rec_lt_calls) ev105 rfl
            (hgood.sub fun z hz => by simp [hz])).1 rfl d Γ T T2 xt xt2 rfl hT hT2
          exact ⟨T, .refl T, hw⟩
        | .other_other_n1_bind (m92 := m92) (cs103 := cs103) (m134 := m134)
            (cs145 := cs145) (x_a := xa) (cs177 := cs177)
            (ev105 := ev105) (ev147 := ev147) (ev179 := ev179) (hc196 := hc196) .. =>
          subst hc196
          have e1 := ev105.heap_extends
          have e2 := ev147.heap_extends
          obtain ⟨A₁, hc₁, hA₁⟩ := consume_wrapper_one_spec hlf
            (hgood.sub fun z hz => by simp [hz]) (hT.mono e1) ev147
          obtain ⟨A₂, hs₂, hw₂⟩ := (ih _ _ _ _ _ _ (by rec_lt_calls) ev179 rfl
            (hgood.sub fun z hz => by simp [hz])).2.1 rfl d Γ A₁ T2 xa xt2 rfl
            hA₁ (hT2.mono (e1.trans e2))
          exact ⟨A₂, .step hc₁ hs₂, hw₂⟩
      · subst hfn hargs
        match Obs.«KernelCheck::wrap_binder».obs ev with
        | .n1_other (he98 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other (he105 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .n1_n1 (m2 := m2) (cs13 := cs13) (m37 := m37) (cs48 := cs48) (cs74 := cs74)
            (ev15 := ev15) (ev50 := ev50) (ev76 := ev76) (hc93 := hc93) =>
          subst hc93
          have hpw := pw_eq_one hℓ hℓ2 ev15
          have e1 := ev15.heap_extends
          have e2 := ev50.heap_extends
          have hdom := (ih _ _ _ _ _ _ (by rec_lt_calls) ev50 rfl
            (hgood.sub fun z hz => by simp [hz])).2.1 rfl d Γ T T2 xt xt2 rfl
            (hT.mono e1) (hT2.mono e1)
          let Γ' := Ghost.extend Γ d (.sort .zero)
          have hB_open : Tm c.κ (d + 1) Γ' m37 0 (B.instantiate1 (.fvar d (.sort .zero))) xb :=
            (hB.mono (e1.trans e2)).open_body (Ghost.extend_at _ _ _) (Ghost.extend_below _ _ _)
          have hB2_open : Tm c.κ (d + 1) Γ' m37 0 (B2.instantiate1 (.fvar d (.sort .zero))) xb2 :=
            (hB2.mono (e1.trans e2)).open_body (Ghost.extend_at _ _ _) (Ghost.extend_below _ _ _)
          have hw_open := (ih _ _ _ _ _ _ (by rec_lt_calls) ev76 rfl
            (hgood.sub fun z hz => by simp [hz])).1 rfl (d + 1) Γ'
            (B.instantiate1 (.fvar d (.sort .zero))) (B2.instantiate1 (.fvar d (.sort .zero)))
            xb xb2 rfl hB_open hB2_open
          have hw_abs := hw_open.abstract1 d 0
          rw [abstract1_instantiate1_cancel (.sort .zero) 0 (tm_fvarIdxLt hB) hB.looseBVarsBounded,
            abstract1_instantiate1_cancel (.sort .zero) 0 (tm_fvarIdxLt hB2) hB2.looseBVarsBounded]
            at hw_abs
          exact ⟨hpw, hdom, hw_abs⟩)

/-- `KernelCheck::wrap_rel` returning `.field 1` on two closed `Tm` heap terms certifies
`WrapRelSem c.env.find? G D`. -/
theorem wrap_rel_spec {c : Ctx} {Γ : Nat → KExpr} {G D : KExpr} {xg xd : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hlf : LoadFacts c) (hgood : Good c cs)
    (hG : Tm c.κ 0 Γ h 0 G xg) (hD : Tm c.κ 0 Γ h 0 D xd)
    (ev : ObsFn W "KernelCheck::wrap_rel" [xg, xd] h (.field 1) h' cs) :
    WrapRelSem c.env.find? G D :=
  ((wrap_rel_family hlf _ _ _ _ _ _ ev rfl hgood).1 rfl 0 Γ G D xg xd rfl hG hD).toWrapRelSem
    (hasFvar_false_of_fvarIdxLt_zero (tm_fvarIdxLt hG))

/-! ## Section 4: `is_large_eliminator` and large-`Prop` singleton sort checks -/

private theorem args_contain_bvar_01 {a t : SourceValue F} {h : Heap F} {r : SourceValue F}
    {h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::args_contain_bvar" [a, t] h r h' cs) :
    r = .field 0 ∨ r = .field 1 :=
  ObsFn.strong_induction (world := W)
    (fun fname ag _ rr _ _ => fname = "KernelCheck::args_contain_bvar" →
      ∀ aa tt, ag = [aa, tt] → rr = .field 0 ∨ rr = .field 1)
    (fun _ _ _ _ _ _ ev_i ih_i hfn _ _ hag => by
      subst hfn hag
      match Obs.«KernelCheck::args_contain_bvar».obs ev_i with
      | .Nil (he20 := he) .. => exact Or.inl he
      | .Cons_BVar_n0 (he87 := he) .. => exact Or.inr he
      | .Cons_BVar_other (ev99 := ev_r) (hc116 := hc_r) .. =>
        subst hc_r
        exact ih_i _ _ _ _ _ _ (by rec_lt_calls) ev_r rfl _ _ rfl
      | .Cons_other (ev126 := ev_r) (hc143 := hc_r) .. =>
        subst hc_r
        exact ih_i _ _ _ _ _ _ (by rec_lt_calls) ev_r rfl _ _ rfl)
    _ _ _ _ _ _ ev rfl a t rfl

private theorem args_contain_bvar_one_spec {κ : _root_.Address → KKey} {d : Nat}
    {Γ : Nat → KExpr} {h : Heap F} :
    ∀ {args : List KExpr} {pargs : SourceValue F} {target : Nat} {h' : Heap F} {cs : List (Call F)},
      target < d →
      target < 549755813888 →
      RepList kexprListEnum (fun h E p => Tm κ d Γ h 0 E p) h args pargs →
      ObsFn W "KernelCheck::args_contain_bvar" [pargs, .field (target : F)] h (.field 1) h' cs →
      Expr.fvar (fvIdx d 0 target) (Γ (fvIdx d 0 target)) ∈ args ∧ h' = h
  | _, _, target, _, _, ht1, ht2, hrep, ev => by
    match Obs.«KernelCheck::args_contain_bvar».obs ev with
    | .Nil (he20 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .Cons_BVar_n0 (x_a := xa) (x_rest := xrest) (x_i := xi)
        (ld12 := ld12) (ld51 := ld51) (op80 := op80) (he88 := he88) .. =>
      obtain ⟨A, rest, rfl, hA, _⟩ := RepList.cons_of_load hrep ld12
      obtain ⟨i_f, rfl, _, hbvar⟩ := hA.bvar_of_load ld51
      simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
        Except.ok.injEq, Value.field.injEq] at op80
      have hif : i_f = (target : F) := sub_eq_zero.mp op80
      have hval : ZMod.val i_f = target := by
        rw [hif]
        exact ZMod.val_natCast_of_lt (Nat.lt_trans ht2 (by decide))
      rcases hbvar with ⟨hlt0, _⟩ | ⟨_, _, rfl⟩
      · omega
      · rw [hval]
        exact ⟨List.mem_cons_self, he88⟩
    | .Cons_BVar_other (x_rest := xrest) (cs97 := cs97)
        (ld12 := ld12) (ev99 := ev99) .. =>
      obtain ⟨A, rest, rfl, _, hrest⟩ := RepList.cons_of_load hrep ld12
      obtain ⟨hmem, hh⟩ := args_contain_bvar_one_spec ht1 ht2 hrest ev99
      exact ⟨List.mem_cons_of_mem _ hmem, hh⟩
    | .Cons_other (x_rest := xrest) (cs124 := cs124)
        (ld12 := ld12) (ev126 := ev126) .. =>
      obtain ⟨A, rest, rfl, _, hrest⟩ := RepList.cons_of_load hrep ld12
      obtain ⟨hmem, hh⟩ := args_contain_bvar_one_spec ht1 ht2 hrest ev126
      exact ⟨List.mem_cons_of_mem _ hmem, hh⟩

private theorem all_bvars_in_args_one_spec {κ : _root_.Address → KKey} {d : Nat}
    {Γ : Nat → KExpr} {args : List KExpr} :
    ∀ {targets : List Nat} {pbvars pargs : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ tgt ∈ targets, tgt < d ∧ tgt < 549755813888) →
      RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F)) h targets pbvars →
      RepList kexprListEnum (fun h E p => Tm κ d Γ h 0 E p) h args pargs →
      ObsFn W "KernelCheck::all_bvars_in_args" [pbvars, pargs] h (.field 1) h' cs →
      ∀ tgt ∈ targets, Expr.fvar (fvIdx d 0 tgt) (Γ (fvIdx d 0 tgt)) ∈ args
  | _, _, _, _, _, _, htgt, hbvars, hargs, ev => by
    match Obs.«KernelCheck::all_bvars_in_args».obs ev with
    | .Nil (ld12 := ld12) .. =>
      obtain rfl := RepList.nil_of_load hbvars ld12
      intro _ hm; exact nomatch hm
    | .Cons_n0 (he75 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .Cons_other (x_b := xb) (x_rest := xrest) (v40 := v40) (m41 := m41)
        (cs52 := cs52) (cs85 := cs85)
        (ld12 := ld12) (ev54 := ev54) (hne78 := hne78) (ev87 := ev87) .. =>
      obtain ⟨t0, rest, rfl, rfl, hrest⟩ := RepList.cons_of_load hbvars ld12
      obtain ⟨ht0_d, ht0_lt⟩ := htgt t0 List.mem_cons_self
      have hv40 : v40 = .field 1 := by
        rcases args_contain_bvar_01 ev54 with he0 | he1
        · exact absurd he0 hne78
        · exact he1
      rw [hv40] at ev54
      obtain ⟨hmem0, rfl⟩ := args_contain_bvar_one_spec ht0_d ht0_lt hargs ev54
      have ih_rest := all_bvars_in_args_one_spec
        (fun t ht => htgt t (List.mem_cons_of_mem _ ht)) hrest hargs ev87
      intro tgt htgt_mem
      rcases List.mem_cons.mp htgt_mem with rfl | hmem_tl
      · exact hmem0
      · exact ih_rest tgt hmem_tl

private theorem openPisAtFvars_succ_forallE {m off : Nat} {dom body : KExpr}
    {bi : Ix.Kernel.BinderMeta} {fvs : List KExpr} {res : KExpr}
    (h : Ix.Kernel.openPisAtFvars (m + 1) (.forallE dom body bi) off = some (fvs, res)) :
    ∃ fvs_tl, fvs = .fvar off dom :: fvs_tl ∧
      Ix.Kernel.openPisAtFvars m (body.instantiate1 (.fvar off dom)) (off + 1) =
        some (fvs_tl, res) := by
  dsimp only [Ix.Kernel.openPisAtFvars] at h
  cases htl : Ix.Kernel.openPisAtFvars m (body.instantiate1 (.fvar off dom)) (off + 1) with
  | none => rw [htl] at h; cases h
  | some p =>
    obtain ⟨fvs_tl, res'⟩ := p
    rw [htl] at h
    injection h with hp
    injection hp with hfvs hres
    subst hres
    exact ⟨fvs_tl, hfvs.symm, rfl⟩

private theorem fvar_not_in_fvsP {nP : Nat} :
    ∀ {fvsP : List KExpr} {ty : KExpr} {m off : Nat} {crest : KExpr},
      Ix.Kernel.openPisAtFvars m ty off = some (fvsP, crest) →
      off + m ≤ nP →
      ∀ k, nP ≤ k → ∀ e : KExpr, e ∈ fvsP → ∀ fty, e ≠ .fvar k fty
  | _, _, 0, _, _, hop, _, _, _, _, he, _, _ => by
    simp [Ix.Kernel.openPisAtFvars] at hop
    obtain ⟨rfl, _⟩ := hop
    exact nomatch he
  | _, .forallE dom body _, m + 1, off, _, hop, hle, k, hk, e, he, fty, heq => by
    obtain ⟨tl, rfl, htl⟩ := openPisAtFvars_succ_forallE hop
    rcases List.mem_cons.mp he with rfl | hmem
    · injection heq with hidx _
      omega
    · exact fvar_not_in_fvsP htl (by omega) k hk e hmem fty heq
  | _, .bvar _, _ + 1, _, _, hop, _, _, _, _, _, _, _
  | _, .fvar _ _, _ + 1, _, _, hop, _, _, _, _, _, _, _
  | _, .sort _, _ + 1, _, _, hop, _, _, _, _, _, _, _
  | _, .const _ _, _ + 1, _, _, hop, _, _, _, _, _, _, _
  | _, .lit _, _ + 1, _, _, hop, _, _, _, _, _, _, _
  | _, .app _ _, _ + 1, _, _, hop, _, _, _, _, _, _, _
  | _, .lam _ _ _, _ + 1, _, _, hop, _, _, _, _, _, _, _
  | _, .letE _ _ _ _, _ + 1, _, _, hop, _, _, _, _, _, _, _
  | _, .proj _ _ _, _ + 1, _, _, hop, _, _, _, _, _, _, _ => by
    simp [Ix.Kernel.openPisAtFvars] at hop

private theorem check_large_walk_fields_go (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    (hef : EnvFacts c) (hlf : LoadFacts c)
    {T : KKey} {lps : List LevelParam} {nP nF : Nat} {fvsP : List KExpr}
    (hnPF_lt : nP + nF < 2147483648)
    (hfvsP_not : ∀ k, nP ≤ k → ∀ e ∈ fvsP, ∀ fty, e ≠ .fvar k fty) :
    ∀ (rem field_idx : Nat) {Γ : Nat → KExpr} {cur_ty : KExpr} {xFvs idxArgs : List KExpr}
      {data_idxs : List Nat}
      {rc xty ptypes pbvars : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      rem + field_idx = nF →
      Ix.Kernel.openPisAtFvars rem cur_ty (nP + field_idx) =
        some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)) →
      Good c cs →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h (nP + field_idx) ptypes →
      GhostScoped Γ (nP + field_idx) →
      Tm c.κ (nP + field_idx) Γ h 0 cur_ty xty →
      (∀ idx ∈ data_idxs, idx < field_idx) →
      RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F)) h
        (data_idxs.map (fun idx => (nF - 1) - idx)) pbvars →
      ObsFn W "KernelCheck::check_large_walk_fields"
        [rc, xty, .field (nF : F), .field (field_idx : F), ptypes, pbvars] h (.field 1) h' cs →
      ∃ sorts_rem : List KLevel,
        sorts_rem.length = rem ∧
        (∀ idx ∈ data_idxs,
          idxArgs.contains (.fvar (nP + idx) (Γ (nP + idx))) = true) ∧
        ∀ i < rem, ∃ fv ty u,
          xFvs[i]? = some fv ∧
          sorts_rem[i]? = some u ∧
          Infer c.env .full (nP + field_idx + i) fv.fvarTypeD ty ∧
          Red c.env (nP + field_idx + i) ty (.sort u) ∧
          ((∀ φ, Level.eval φ u = 0) ∨ idxArgs.contains fv = true)
  | 0, field_idx, Γ, cur_ty, xFvs, idxArgs, data_idxs, rc, xty, ptypes, pbvars, h, h', cs,
      hsum, hop, hgood, _, _, _, hcur, hdata_lt, hbvars, ev => by
    have hfi_eq : field_idx = nF := by omega
    subst hfi_eq
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    match Obs.«KernelCheck::check_large_walk_fields».obs ev with
    | .other_Forall (op17 := op17) (hne88 := hne88) .. =>
      simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
        Except.ok.injEq, sub_self] at op17
      exact absurd op17.symm hne88
    | .other_other (he389 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .n0 (m25 := m25) (cs36 := cs36) (w53 := w53) (x_args := xargs) (cs67 := cs67)
        (ev38 := ev38) (ev69 := ev69) (hc86 := hc86) .. =>
      subst hc86
      have hbnd36 : IxVM.Consistency.Bounded cs36 :=
        RomBound.bounded_mono hgood.2 (fun z hz => by simp [hz])
      obtain ⟨hd, sp, H, As, hpair, _, hAs, heq_app⟩ :=
        SubstAux.gall c.κ .collect_spine _ _ _ _ _ ev38 xty rfl hbnd36 (nP + field_idx) Γ 0 _ hcur
      injection hpair with hlist; injection hlist with _ hlist; injection hlist with hsp _
      subst hsp
      have hAs_sub : ∀ e ∈ As, e ∈ fvsP ++ idxArgs := by
        have h1 : (Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)).getAppArgs =
            fvsP ++ idxArgs := by
          rw [getAppArgs_mkAppN]; rfl
        have h2 : (Expr.mkAppN H As).getAppArgs = H.getAppArgs ++ As := getAppArgs_mkAppN As H
        have h3 : fvsP ++ idxArgs = H.getAppArgs ++ As := by
          rw [← h1, ← h2, heq_app]
        intro e he
        rw [h3]
        exact List.mem_append_right _ he
      have htgt : ∀ tgt ∈ data_idxs.map (fun idx => (field_idx - 1) - idx),
          tgt < nP + field_idx ∧ tgt < 549755813888 := by
        intro tgt htgt_mem
        obtain ⟨idx, hidx_mem, rfl⟩ := List.mem_map.mp htgt_mem
        have := hdata_lt idx hidx_mem
        exact ⟨by omega, by omega⟩
      have e1 := ev38.heap_extends
      have hbvars' : RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F)) m25
          (data_idxs.map (fun idx => (field_idx - 1) - idx)) pbvars :=
        repList_heapMono₂ byteListEnum (fun _ _ _ _ _ hv => hv) e1 hbvars
      have hall := all_bvars_in_args_one_spec htgt hbvars' hAs ev69
      refine ⟨[], rfl, ?_, fun _ hlt => nomatch hlt⟩
      intro idx hidx_mem
      have hidx_lt : idx < field_idx := hdata_lt idx hidx_mem
      have htgt_mem : (field_idx - 1) - idx ∈ data_idxs.map (fun idx => (field_idx - 1) - idx) :=
        List.mem_map.mpr ⟨idx, hidx_mem, rfl⟩
      have hmem_As := hall ((field_idx - 1) - idx) htgt_mem
      have hfv_eq : fvIdx (nP + field_idx) 0 ((field_idx - 1) - idx) = nP + idx := by
        unfold fvIdx; omega
      rw [hfv_eq] at hmem_As
      rcases List.mem_append.mp (hAs_sub _ hmem_As) with hmem_P | hmem_I
      · exact absurd rfl (hfvsP_not (nP + idx) (by omega) _ hmem_P _)
      · exact List.contains_iff_mem.mpr hmem_I
  | m + 1, field_idx, Γ, cur_ty, xFvs, idxArgs, data_idxs, rc, xty, ptypes, pbvars, h, h', cs,
      hsum, hop, hgood, hrc, htypes, hsc, hcur, hdata_lt, hbvars, ev => by
    match Obs.«KernelCheck::check_large_walk_fields».obs ev with
    | .n0 (op17 := op17) .. =>
      have hsub := evalBinOp_sub_nat (by omega : field_idx ≤ nF) op17
      rw [show nF - field_idx = m + 1 by omega] at hsub
      exact absurd hsub.symm (succ_field_ne_zero (by omega))
    | .other_other (he389 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .other_Forall (x_dom := x_dom) (x_body := x_body) (w111 := w111)
        (v127 := v127) (m128 := m128) (cs138 := cs138)
        (v165 := v165) (m166 := m166) (y174 := y174) (cs184 := cs184)
        (m197 := m197) (v209 := v209) (x217 := x217)
        (v282 := v282) (m283 := m283) (cs285 := cs285)
        (m292 := m292) (cs325 := cs325) (v331 := v331)
        (ld103 := ld103) (ev140 := ev140) (hm205 := hm205) (ev186 := ev186)
        (op180 := op180) (op232 := op232) (op224 := op224) (sg290 := sg290)
        (hm302 := hm302) (op368 := op368) (ev327 := ev327) (hc384 := hc384) .. =>
      subst hc384
      obtain ⟨dom, body, _, rfl, hdom, hbody, _⟩ := hcur.forallE_of_load ld103
      obtain ⟨xFvs_tl, rfl, hop_tl⟩ := openPisAtFvars_succ_forallE hop
      rw [show nP + field_idx + 1 = nP + (field_idx + 1) by omega] at hop_tl
      have hg_es : Good c cs138 := hgood.sub (fun z hz => by simp [hz])
      obtain ⟨ty₀, u₀, ℓ₀, hinf₀, hred₀, hℓ₀, hu₀⟩ :=
        core_ensure_sort hCore hrc htypes hsc hef hlf hg_es ev140 hdom
      have e_es := ev140.heap_extends
      have e_zero : Heap.Extends m128 m197 := by rw [hm205]; exact Heap.Extends.snoc m128 _
      have hzero_rep : RepKLevel m197 .zero
          (.ptr (.enum "KernelTypes::KLevelNode") m128.length) := .zero (by rw [hm205]; simp)
      have hbnd184 : IxVM.Consistency.Bounded cs184 :=
        RomBound.bounded_mono hgood.2 (fun z hz => by simp [hz])
      obtain ⟨hy174, e_eq⟩ := IxVM.Refinement.Levels.levelEqual_obs ev186 hbnd184
        (repKLevel_heapMono₂ e_zero hℓ₀) hzero_rep
      rw [evalBinOp_sub_nat (by omega : 1 ≤ nF) op232] at op224
      have hv209 : v209 = .field (((nF - 1) - field_idx : Nat) : F) :=
        evalBinOp_sub_nat (by omega : field_idx ≤ nF - 1) op224
      have hv331 : v331 = .field ((field_idx + 1 : Nat) : F) :=
        evalBinOp_add_nat field_idx 1 op368
      rw [hv331] at ev327
      have e_pre := e_es.trans (e_zero.trans e_eq)
      cases heq_lvl : IxVM.Refinement.KernelLevels.levelEqual ℓ₀ .zero with
      | true =>
        rw [heq_lvl] at hy174
        rw [hy174] at ev186 op180
        have hℓ_zero := levels_equal_one hLevels ev186 hbnd184
          (repKLevel_heapMono₂ e_zero hℓ₀) hzero_rep
        have hu₀_zero : ∀ φ, Level.eval φ u₀ = 0 := fun φ => by
          rw [hu₀ φ, hℓ_zero φ]; rfl
        have hv165 : v165 = .field 0 := by
          simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
            Except.ok.injEq, sub_self] at op180
          exact op180.symm
        match sg290 with
        | .other (hne253 := hne) .. => exact absurd hv165 hne
        | .n0 (he250 := hv282) (he251 := hm283) (hc252 := hcs285) .. =>
          subst v282 m283 cs285
          obtain ⟨e_push, htypes', hsc'⟩ :=
            push_binder_types (hdom.mono e_pre) (htypes.mono e_pre) hsc
          rw [hm302] at ev327
          have htypes'' : TypesRep c.κ (Ghost.extend Γ (nP + field_idx) dom)
              (m166 ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]])
              (nP + (field_idx + 1)) (.ptr (.enum kexprListEnum) m166.length) := by
            rw [show nP + (field_idx + 1) = nP + field_idx + 1 by omega]
            exact htypes'
          have hsc'' : GhostScoped (Ghost.extend Γ (nP + field_idx) dom)
              (nP + (field_idx + 1)) := by
            rw [show nP + (field_idx + 1) = nP + field_idx + 1 by omega]
            exact hsc'
          have hbody_open : Tm c.κ (nP + (field_idx + 1)) (Ghost.extend Γ (nP + field_idx) dom)
              (m166 ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]]) 0
              (body.instantiate1 (.fvar (nP + field_idx) dom)) x_body := by
            rw [show nP + (field_idx + 1) = nP + field_idx + 1 by omega]
            exact (hbody.mono (e_pre.trans e_push)).open_body
              (Ghost.extend_at _ _ _) (Ghost.extend_below _ _ _)
          have hbvars' : RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F))
              (m166 ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]])
              (data_idxs.map (fun idx => (nF - 1) - idx)) pbvars :=
            repList_heapMono₂ byteListEnum (fun _ _ _ _ _ hv => hv) (e_pre.trans e_push) hbvars
          have hg_rec : Good c cs325 := hgood.sub (fun z hz => by simp [hz])
          obtain ⟨sorts_tl, hlen_tl, hdata_tl, hfields_tl⟩ :=
            check_large_walk_fields_go hLevels hCore hef hlf hnPF_lt hfvsP_not
              m (field_idx + 1) (by omega) hop_tl hg_rec
              (hrc.mono (e_pre.trans e_push)) htypes'' hsc'' hbody_open
              (fun idx hidx => Nat.lt_succ_of_lt (hdata_lt idx hidx)) hbvars' ev327
          refine ⟨u₀ :: sorts_tl, by simp [hlen_tl], ?_, ?_⟩
          · intro idx hidx
            have hlt_i := hdata_lt idx hidx
            have hmem_ext := hdata_tl idx hidx
            rwa [Ghost.extend_below _ _ _ _ (by omega)] at hmem_ext
          · intro i hi
            cases i with
            | zero =>
              exact ⟨.fvar (nP + field_idx) dom, ty₀, u₀, rfl, rfl,
                by simpa [Expr.fvarTypeD] using hinf₀, by simpa using hred₀, Or.inl hu₀_zero⟩
            | succ k =>
              obtain ⟨fv, ty, u, hfv, hu, hinf_k, hred_k, hor_k⟩ := hfields_tl k (by omega)
              rw [show nP + (field_idx + 1) + k = nP + field_idx + (k + 1) by omega] at hinf_k hred_k
              exact ⟨fv, ty, u, hfv, hu, hinf_k, hred_k, hor_k⟩
      | false =>
        rw [heq_lvl] at hy174
        rw [hy174] at op180
        have hv165 : v165 = .field 1 := by
          simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
            Except.ok.injEq, sub_zero] at op180
          exact op180.symm
        match sg290 with
        | .n0 (hv248 := hv0) .. =>
          exact absurd (Value.field.inj (hv165.symm.trans hv0)) one_ne_zero
        | .other (he261 := hv282) (hm260 := hm283) (hc281 := hcs285) .. =>
          subst hv282 hcs285
          have e_cons_bvar : Heap.Extends m166 m283 := by
            rw [hm283]; exact Heap.Extends.snoc m166 _
          have hbvars_m283 : RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F)) m283
              ((field_idx :: data_idxs).map (fun idx => (nF - 1) - idx))
              (.ptr (.enum byteListEnum) m166.length) :=
            RepLinkedList.cons (by rw [hm283]; simp) hv209
              (repList_heapMono₂ byteListEnum (fun _ _ _ _ _ hv => hv)
                (e_pre.trans e_cons_bvar) hbvars)
          have e_pre2 := e_pre.trans e_cons_bvar
          obtain ⟨e_push, htypes', hsc'⟩ :=
            push_binder_types (hdom.mono e_pre2) (htypes.mono e_pre2) hsc
          rw [hm302] at ev327
          have htypes'' : TypesRep c.κ (Ghost.extend Γ (nP + field_idx) dom)
              (m283 ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]])
              (nP + (field_idx + 1)) (.ptr (.enum kexprListEnum) m283.length) := by
            rw [show nP + (field_idx + 1) = nP + field_idx + 1 by omega]
            exact htypes'
          have hsc'' : GhostScoped (Ghost.extend Γ (nP + field_idx) dom)
              (nP + (field_idx + 1)) := by
            rw [show nP + (field_idx + 1) = nP + field_idx + 1 by omega]
            exact hsc'
          have hbody_open : Tm c.κ (nP + (field_idx + 1)) (Ghost.extend Γ (nP + field_idx) dom)
              (m283 ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]]) 0
              (body.instantiate1 (.fvar (nP + field_idx) dom)) x_body := by
            rw [show nP + (field_idx + 1) = nP + field_idx + 1 by omega]
            exact (hbody.mono (e_pre2.trans e_push)).open_body
              (Ghost.extend_at _ _ _) (Ghost.extend_below _ _ _)
          have hbvars_m292 : RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F))
              (m283 ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]])
              ((field_idx :: data_idxs).map (fun idx => (nF - 1) - idx))
              (.ptr (.enum byteListEnum) m166.length) :=
            repList_heapMono₂ byteListEnum (fun _ _ _ _ _ hv => hv) e_push hbvars_m283
          have hg_rec : Good c cs325 := hgood.sub (fun z hz => by simp [hz])
          have hdata_lt' : ∀ idx ∈ field_idx :: data_idxs, idx < field_idx + 1 := by
            intro idx hidx
            rcases List.mem_cons.mp hidx with rfl | hmem
            · omega
            · exact Nat.lt_succ_of_lt (hdata_lt idx hmem)
          obtain ⟨sorts_tl, hlen_tl, hdata_tl, hfields_tl⟩ :=
            check_large_walk_fields_go hLevels hCore hef hlf hnPF_lt hfvsP_not
              m (field_idx + 1) (by omega) hop_tl hg_rec
              (hrc.mono (e_pre2.trans e_push)) htypes'' hsc'' hbody_open
              hdata_lt' hbvars_m292 ev327
          have hcur_in_idx : idxArgs.contains (.fvar (nP + field_idx) dom) = true := by
            have hmem_head := hdata_tl field_idx List.mem_cons_self
            rwa [Ghost.extend_at] at hmem_head
          refine ⟨u₀ :: sorts_tl, by simp [hlen_tl], ?_, ?_⟩
          · intro idx hidx
            have hlt_i := hdata_lt idx hidx
            have hmem_ext := hdata_tl idx (List.mem_cons_of_mem _ hidx)
            rwa [Ghost.extend_below _ _ _ _ (by omega)] at hmem_ext
          · intro i hi
            cases i with
            | zero =>
              exact ⟨.fvar (nP + field_idx) dom, ty₀, u₀, rfl, rfl,
                by simpa [Expr.fvarTypeD] using hinf₀, by simpa using hred₀, Or.inr hcur_in_idx⟩
            | succ k =>
              obtain ⟨fv, ty, u, hfv, hu, hinf_k, hred_k, hor_k⟩ := hfields_tl k (by omega)
              rw [show nP + (field_idx + 1) + k = nP + field_idx + (k + 1) by omega] at hinf_k hred_k
              exact ⟨fv, ty, u, hfv, hu, hinf_k, hred_k, hor_k⟩

private theorem check_large_prop_ctor_go (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    (hef : EnvFacts c) (hlf : LoadFacts c)
    {T : KKey} {lps : List LevelParam} {nP nF : Nat}
    {fvsP crest : KExpr → Prop}
    {fvsP_full xFvs idxArgs : List KExpr} {crest₀ : KExpr}
    (hnPF_lt : nP + nF < 2147483648)
    (hfvsP_not : ∀ k, nP ≤ k → ∀ e ∈ fvsP_full, ∀ fty, e ≠ .fvar k fty)
    (hopF : Ix.Kernel.openPisAtFvars nF crest₀ nP =
      some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP_full ++ idxArgs))) :
    ∀ (remP off : Nat) {Γ : Nat → KExpr} {cur_ty : KExpr} {fvsP_rem : List KExpr}
      {rc xty ptypes : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      remP + off = nP →
      Ix.Kernel.openPisAtFvars remP cur_ty off = some (fvsP_rem, crest₀) →
      Good c cs →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h off ptypes →
      GhostScoped Γ off →
      Tm c.κ off Γ h 0 cur_ty xty →
      ObsFn W "KernelCheck::check_large_prop_ctor"
        [rc, xty, .field (remP : F), .field (nF : F), ptypes] h (.field 1) h' cs →
      ∃ sorts : List KLevel,
        FieldSortsJ rulesJ c.env true true .zero nP xFvs idxArgs nF sorts
  | 0, off, Γ, cur_ty, fvsP_rem, rc, xty, ptypes, h, h', cs,
      hsum, hopP, hgood, hrc, htypes, hsc, hcur, ev => by
    have hoff_eq : off = nP := by omega
    subst hoff_eq
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hopP
    obtain ⟨rfl, rfl⟩ := hopP
    match Obs.«KernelCheck::check_large_prop_ctor».obs ev with
    | .other_Forall (hne75 := hne) .. => exact absurd rfl hne
    | .other_other (he204 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
    | .n0 (cs18 := cs18) (m62 := m62) (hm70 := hm70) (ev20 := ev20) (hc74 := hc74) .. =>
      subst hc74
      have e_nil : Heap.Extends h m62 := by rw [hm70]; exact Heap.Extends.snoc h _
      have hbvars_nil : RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F)) m62
          (([] : List Nat).map (fun idx => (nF - 1) - idx))
          (.ptr (.enum byteListEnum) h.length) :=
        RepLinkedList.nil (by rw [hm70]; simp)
      have hg_walk : Good c cs18 := hgood.sub (fun z hz => by simp [hz])
      obtain ⟨sorts, hlen, _, hfields⟩ :=
        check_large_walk_fields_go hLevels hCore hef hlf hnPF_lt hfvsP_not
          nF 0 (by omega) (by simpa using hopF) hg_walk
          (hrc.mono e_nil) (by simpa using htypes.mono e_nil) (by simpa using hsc)
          (by simpa using hcur.mono e_nil) (by intro _ hm; cases hm) hbvars_nil ev20
      refine ⟨sorts, hlen, ?_⟩
      intro i hi
      obtain ⟨fv, ty, u, hfv, hu, hinf, hred, hor⟩ := hfields i hi
      rw [show off + 0 + i = off + i by omega] at hinf hred
      exact ⟨fv, ty, u, hfv, hu, hinf, hred, (fun h => nomatch h), (fun _ _ => hor)⟩
  | m + 1, off, Γ, cur_ty, fvsP_rem, rc, xty, ptypes, h, h', cs,
      hsum, hopP, hgood, hrc, htypes, hsc, hcur, ev => by
    match Obs.«KernelCheck::check_large_prop_ctor».obs ev with
    | .n0 (hv14 := hv) .. =>
      exact absurd hv (succ_field_ne_zero (by omega))
    | .other_other (he204 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .other_Forall (x_dom := x_dom) (x_body := x_body) (m115 := m115)
        (cs148 := cs148) (v153 := v153)
        (ld90 := ld90) (hm125 := hm125) (op183 := op183) (ev150 := ev150) (hc199 := hc199) .. =>
      subst hc199
      obtain ⟨dom, body, _, rfl, hdom, hbody, _⟩ := hcur.forallE_of_load ld90
      obtain ⟨fvsP_tl, rfl, hopP_tl⟩ := openPisAtFvars_succ_forallE hopP
      obtain ⟨e_push, htypes', hsc'⟩ := push_binder_types hdom htypes hsc
      rw [evalBinOp_sub_succ m op183, hm125] at ev150
      have hbody_open : Tm c.κ (off + 1) (Ghost.extend Γ off dom)
          (h ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]]) 0
          (body.instantiate1 (.fvar off dom)) x_body :=
        (hbody.mono e_push).open_body (Ghost.extend_at _ _ _) (Ghost.extend_below _ _ _)
      have hg_rec : Good c cs148 := hgood.sub (fun z hz => by simp [hz])
      exact check_large_prop_ctor_go (fvsP := fvsP) (crest := crest)
        hLevels hCore hef hlf hnPF_lt hfvsP_not hopF m (off + 1) (by omega) hopP_tl hg_rec
        (hrc.mono e_push) htypes' hsc' hbody_open ev150

/-- `FieldSortsJ` at `isProp = false` holds at any `large : Bool`, and at `isProp = true` its
level parameter `s` is unused. -/
theorem fieldSortsJ_large_of_isProp_false {env : Ix.Kernel.Env .anon} {s : KLevel}
    {nP n : Nat} {fvs idxArgs : List KExpr} {sorts : List KLevel}
    (h : FieldSortsJ rulesJ env false false s nP fvs idxArgs n sorts) :
    ∀ large : Bool, FieldSortsJ rulesJ env false large s nP fvs idxArgs n sorts := by
  intro large
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨fv, ty, u, hfv, hu, hinf, hred, hle, _⟩ := h.2 i hi
  exact ⟨fv, ty, u, hfv, hu, hinf, hred, hle, fun hp => nomatch hp⟩

theorem fieldSortsJ_isProp_true_set_sort {env : Ix.Kernel.Env .anon} {s₁ s₂ : KLevel}
    {large : Bool} {nP n : Nat} {fvs idxArgs : List KExpr} {sorts : List KLevel}
    (h : FieldSortsJ rulesJ env true large s₁ nP fvs idxArgs n sorts) :
    FieldSortsJ rulesJ env true large s₂ nP fvs idxArgs n sorts := by
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨fv, ty, u, hfv, hu, hinf, hred, _, hlg⟩ := h.2 i hi
  exact ⟨fv, ty, u, hfv, hu, hinf, hred, (fun hp => nomatch hp), hlg⟩

/-- `KernelCheck::is_large_eliminator` returning `.field 1` certifies the large-elimination
guard `(∀ φ, Level.eval φ resSort ≠ 0) ∨ ctors.length < 2` and upgrades `SumCtorsRunJ` from
`large = false` to `large = true` in `c.env`. -/
theorem is_large_eliminator_one_spec (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    (hef : EnvFacts c) (hlf : LoadFacts c)
    {T : KKey} {lps : List LevelParam} {nP nIdx : Nat} {resSort ind_lvl : KLevel}
    {cvTa : KConstantVal} {ctors ctorsA : List (KConstantVal × Nat)}
    {sortss₀ : List (List KLevel)}
    {rc x_res_lvl x_single_opt x_is_solo : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hnCtors_lt : ctors.length < 4294967296)
    (hnPF_lt : ∀ cA ∈ ctorsA, nP + cA.2 < 2147483648)
    (hres_rep : RepKLevel h ind_lvl x_res_lvl)
    (hres_eq : LvEq resSort ind_lvl)
    (hrc : RCRep c.t c.lim h rc)
    (hgood : Good c cs)
    (hctors₀ : SumCtorsRunJ rulesJ c.env c.env T lps nP nIdx resSort
      (Level.isEquiv resSort .zero == some true) false cvTa ctors ctorsA sortss₀)
    (hopt : ctors.length = 1 →
      ∃ cA₀ xnl xcty w2 w3 w4 w5,
        ctorsA = [cA₀] ∧
        x_single_opt = .tuple [.field 1,
          .construct kciEnum "Ctor"
            [xnl, xcty, w2, w3, w4, .field (nP : F), .field (cA₀.2 : F), w5]] ∧
        Tm c.κ 0 (fun _ => default) h 0 cA₀.1.type xcty)
    (ev : ObsFn W "KernelCheck::is_large_eliminator"
      [rc, x_res_lvl, .field (ctors.length : F), x_single_opt, x_is_solo] h (.field 1) h' cs) :
    ((∀ φ : LevelParam → Nat, Level.eval φ resSort ≠ 0) ∨ ctors.length < 2) ∧
    ∃ sortss_large : List (List KLevel),
      SumCtorsRunJ rulesJ c.env c.env T lps nP nIdx resSort
        (Level.isEquiv resSort .zero == some true) true cvTa ctors ctorsA sortss_large := by
  match Obs.«KernelCheck::is_large_eliminator».obs ev with
  | .other_n0 (he49 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
  | .other_other_n1_n0 (he118 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
  | .other_other_n1_other_other (he264 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
  | .other_other_other (he272 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
  | .n1 (ev15 := ev15) .. =>
    obtain ⟨hr1, _⟩ := IxVM.Refinement.Levels.levelIsNotZero_step ev15 x_res_lvl rfl ind_lvl hres_rep
    have hnz : ind_lvl.isNeverZero = true := by
      cases hz : ind_lvl.isNeverZero
      · rw [hz] at hr1; exact absurd (Value.field.inj hr1) one_ne_zero
      · rfl
    have hnot_zero : ∀ φ : LevelParam → Nat, Level.eval φ resSort ≠ 0 := fun φ => by
      rw [hres_eq φ]
      exact Ix.Kernel.Level.isNeverZero_sound φ ind_lvl hnz
    have hisProp_false : (Level.isEquiv resSort .zero == some true) = false := by
      cases hp : (Level.isEquiv resSort .zero == some true)
      · rfl
      · exact absurd (eval_zero_of_isEquiv_zero hp (fun _ => 0)) (hnot_zero (fun _ => 0))
    refine ⟨Or.inl hnot_zero, sortss₀, hctors₀.1, hctors₀.2.1, fun j c₀ cA hc₀ hcA => ?_⟩
    obtain ⟨hnf, sorts, hsj, hrun⟩ := hctors₀.2.2 j c₀ cA hc₀ hcA
    rw [hisProp_false] at hrun ⊢
    obtain ⟨hchk, hres, fvsP, crest, tfvs, trest, xFvs, idxArgs,
      hopP, hopT, hdoms, hopF, hidx_len, hxres, heres, hfs⟩ := hrun
    exact ⟨hnf, sorts, hsj, hchk, hres, fvsP, crest, tfvs, trest, xFvs, idxArgs,
      hopP, hopT, hdoms, hopF, hidx_len, hxres, heres,
      fieldSortsJ_large_of_isProp_false hfs true⟩
  | .other_other_n0 (hv69 := hv69) .. =>
    have hlen0 : ctors.length = 0 :=
      nat_eq_of_field_eq (Nat.lt_trans hnCtors_lt (by decide)) (by decide) hv69
    have hctorsA_len : ctorsA.length = ctors.length := hctors₀.1
    refine ⟨Or.inr (by omega), [], by simp [hctorsA_len, hlen0], by simp [hlen0], fun j _ _ hcj _ => ?_⟩
    have := (List.getElem?_eq_some_iff.mp hcj).1
    omega
  | .other_other_n1_other_Ctor_n0 (hv77 := hv77) (hv92 := hv92) .. =>
    have hlen1 : ctors.length = 1 :=
      nat_eq_of_field_eq (Nat.lt_trans hnCtors_lt (by decide)) (by decide) hv77
    obtain ⟨cA₀, xnl, xcty, w2, w3, w4, w5, hctorsA_eq, hopt_eq, _⟩ := hopt hlen1
    rw [hopt_eq] at hv92
    injection hv92 with h_tup; injection h_tup with _ h_tup; injection h_tup with h_ci _
    injection h_ci with _ _ hxs
    injection hxs with _ hxs; injection hxs with _ hxs; injection hxs with _ hxs
    injection hxs with _ hxs; injection hxs with _ hxs; injection hxs with _ hxs
    injection hxs with hnf0 _
    have hnF_lt : cA₀.2 < 2147483648 := by
      have := hnPF_lt cA₀ (by rw [hctorsA_eq]; exact List.mem_cons_self)
      omega
    have hnF0 : cA₀.2 = 0 :=
      nat_eq_of_field_eq (Nat.lt_trans hnF_lt (by decide)) (by decide) hnf0
    refine ⟨Or.inr (by omega), [[]], by simp [hctorsA_eq, hlen1], by simp [hlen1],
      fun j c₀ cA hc₀ hcA => ?_⟩
    have hj0 : j = 0 := by
      have := (List.getElem?_eq_some_iff.mp hc₀).1; omega
    subst hj0
    obtain ⟨hnf, _, _, hrun⟩ := hctors₀.2.2 0 c₀ cA hc₀ hcA
    have hcA_eq : cA = cA₀ := by
      rw [hctorsA_eq] at hcA; injection hcA with h; exact h.symm
    subst hcA_eq
    have hc0_2 : c₀.2 = 0 := by omega
    obtain ⟨hchk, hres, fvsP, crest, tfvs, trest, xFvs, idxArgs,
      hopP, hopT, hdoms, hopF, hidx_len, hxres, heres, _⟩ := hrun
    refine ⟨hnf, [], rfl, hchk, hres, fvsP, crest, tfvs, trest, xFvs, idxArgs,
      hopP, hopT, hdoms, hopF, hidx_len, hxres, heres, ?_⟩
    exact ⟨hc0_2.symm, fun _ hlt => by omega⟩
  | .other_other_n1_other_Ctor_other (m2 := m2) (cs210 := cs210) (m247 := m247)
      (ev15 := ev15) (hv77 := hv77) (hv92 := hv92) (hm255 := hm255)
      (ev212 := ev212) (hc259 := hc259) .. =>
    subst hc259
    have hlen1 : ctors.length = 1 :=
      nat_eq_of_field_eq (Nat.lt_trans hnCtors_lt (by decide)) (by decide) hv77
    obtain ⟨cA₀, xnl, xcty, w2, w3, w4, w5, hctorsA_eq, hopt_eq, hxcty⟩ := hopt hlen1
    rw [hopt_eq] at hv92
    injection hv92 with h_tup; injection h_tup with _ h_tup; injection h_tup with h_ci _
    injection h_ci with _ _ hxs
    injection hxs with _ hxs; injection hxs with hxcty_eq hxs; injection hxs with _ hxs
    injection hxs with _ hxs; injection hxs with _ hxs; injection hxs with hxnp_eq hxs
    injection hxs with hxnf_eq _
    cases hxcty_eq.symm; cases hxnp_eq.symm; cases hxnf_eq.symm
    cases hp : (Level.isEquiv resSort .zero == some true) with
    | false =>
      refine ⟨Or.inr (by omega), sortss₀, hctors₀.1, hctors₀.2.1, fun j c₀ cA hc₀ hcA => ?_⟩
      obtain ⟨hnf, sorts, hsj, hrun⟩ := hctors₀.2.2 j c₀ cA hc₀ hcA
      rw [hp] at hrun
      obtain ⟨hchk, hres, fvsP, crest, tfvs, trest, xFvs, idxArgs,
        hopP, hopT, hdoms, hopF, hidx_len, hxres, heres, hfs⟩ := hrun
      exact ⟨hnf, sorts, hsj, hchk, hres, fvsP, crest, tfvs, trest, xFvs, idxArgs,
        hopP, hopT, hdoms, hopF, hidx_len, hxres, heres,
        fieldSortsJ_large_of_isProp_false hfs true⟩
    | true =>
      obtain ⟨c₀, hc₀⟩ : ∃ c₀, ctors[0]? = some c₀ :=
        ⟨ctors[0]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      have hcA₀ : ctorsA[0]? = some cA₀ := by rw [hctorsA_eq]; rfl
      obtain ⟨hnf, _, _, hrun⟩ := hctors₀.2.2 0 c₀ cA₀ hc₀ hcA₀
      obtain ⟨hchk, hres, fvsP, crest, tfvs, trest, xFvs, idxArgs,
        hopP, hopT, hdoms, hopF, hidx_len, hxres, heres, _⟩ := hrun
      have e_15 := ev15.heap_extends
      have e_247 : Heap.Extends m2 m247 := by rw [hm255]; exact Heap.Extends.snoc m2 _
      have hty_nil : TypesRep c.κ (fun _ => default) m247 0
          (.ptr (.enum kexprListEnum) m2.length) := by
        rw [hm255]; exact typesRep_alloc_nil c.κ (fun _ => default) m2
      have hg_prop : Good c cs210 := hgood.sub (fun z hz => by simp [hz])
      have hnPF_cA₀ : nP + c₀.2 < 2147483648 := by
        rw [← hnf]
        exact hnPF_lt cA₀ (by rw [hctorsA_eq]; exact List.mem_cons_self)
      rw [hnf] at ev212
      obtain ⟨sorts_lg, hfs_lg0⟩ :=
        check_large_prop_ctor_go (fvsP := fun _ => True) (crest := fun _ => True)
          hLevels hCore hef hlf hnPF_cA₀
          (fvar_not_in_fvsP hopP (by omega)) hopF nP 0 (by omega) hopP hg_prop
          (hrc.mono (e_15.trans e_247)) hty_nil (fun _ hj => nomatch hj)
          (hxcty.mono (e_15.trans e_247)) ev212
      have hfs_lg : FieldSortsJ rulesJ c.env true true resSort nP xFvs idxArgs c₀.2 sorts_lg :=
        fieldSortsJ_isProp_true_set_sort hfs_lg0
      refine ⟨Or.inr (by omega), [sorts_lg], by simp [hctorsA_eq, hlen1], by simp [hlen1],
        fun j c_j cA_j hcj hcAj => ?_⟩
      have hj0 : j = 0 := by
        have := (List.getElem?_eq_some_iff.mp hcj).1; omega
      subst hj0
      rw [hc₀] at hcj; injection hcj with hcj_eq; subst hcj_eq
      rw [hcA₀] at hcAj; injection hcAj with hcAj_eq; subst hcAj_eq
      exact ⟨hnf, sorts_lg, rfl, hchk, hres, fvsP, crest, tfvs, trest, xFvs, idxArgs,
        hopP, hopT, hdoms, hopF, hidx_len, hxres, heres, hfs_lg⟩

/-! ## Section 4: Algebraic, Level-Substitution, & Scoping Lemmas for `structRecTyR` / `structRecRhsR` -/

/-- Annotated terms produced by `Annotates` contain no `.letE` nodes. -/
theorem annotates_letFree {a e : KExpr} (h : IxVM.Consistency.Annotates a e) :
    letFree a = true := by
  induction h with
  | bvar | fvar _ _ | sort | const | lit => rfl
  | app _ _ ihf iha => simp [letFree, ihf, iha]
  | lam _ _ iht ihb => simp [letFree, iht, ihb]
  | forallE _ _ iht ihb => simp [letFree, iht, ihb]
  | proj _ ih => exact ih
  | letE _ ih => exact ih

/-- `sumSplit` decomposes the post-former block tail into constructors followed by the recursor. -/
theorem sumSplit_eq_append_rec :
    ∀ {rest : List KConstantInfo} {cs : List (KConstantVal × Nat × Nat)}
      {cvR : KConstantVal} {mI rP : Nat} {rules : List (RecRule .anon)},
      Ix.Kernel.sumSplit rest = some (cs, cvR, mI, rP, rules) →
      rest = (cs.map fun c => ConstantInfo.ctorInfo c.1 c.2.1 c.2.2) ++
        [.recInfo cvR mI rP rules]
  | [.recInfo cvR mI rP rules], cs, cvR', mI', rP', rules', h => by
    simp only [Ix.Kernel.sumSplit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    rfl
  | .ctorInfo cvC nP nF :: rest, cs, cvR, mI, rP, rules, h => by
    simp only [Ix.Kernel.sumSplit, Option.map_eq_some_iff] at h
    obtain ⟨⟨cs', cvR', mI', rP', rules'⟩, hs, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
    rw [sumSplit_eq_append_rec hs]
    rfl
  | [], _, _, _, _, _, h => nomatch h
  | [.axiomInfo _], _, _, _, _, _, h | [.defnInfo _ _ _], _, _, _, _, _, h
  | [.thmInfo _ _], _, _, _, _, _, h | [.indInfo _ _], _, _, _, _, _, h
  | [.projInfo _], _, _, _, _, _, h => by
    simp [Ix.Kernel.sumSplit] at h
  | .axiomInfo _ :: _ :: _, _, _, _, _, _, h | .defnInfo _ _ _ :: _ :: _, _, _, _, _, _, h
  | .thmInfo _ _ :: _ :: _, _, _, _, _, _, h | .indInfo _ _ :: _ :: _, _, _, _, _, _, h
  | .recInfo _ _ _ _ :: _ :: _, _, _, _, _, _, h | .projInfo _ :: _ :: _, _, _, _, _, _, h =>
    nomatch h

/-- Structural inversion of `Ix.Kernel.nativeParts?` on a native one-type block with recursor. -/
theorem nativeParts?_withRec_inv {nPd : Nat} {block : List KConstantInfo}
    {p₀ : Ix.Kernel.NativeParts .anon}
    (hp : Ix.Kernel.nativeParts? nPd block = some p₀) :
    ∃ (caps₀ : Ix.Kernel.IndCaps .anon) (cs : List (KConstantVal × Nat × Nat))
      (mI rP : Nat) (rules : List (RecRule .anon)),
      block = .indInfo p₀.cvT caps₀ ::
        (cs.map fun c => ConstantInfo.ctorInfo c.1 c.2.1 c.2.2) ++
        [.recInfo p₀.cvR mI rP rules] ∧
      p₀.nP = nPd ∧
      p₀.ctors = cs.map (fun c => (c.1, c.2.2)) ∧
      p₀.rhss = rules.map (·.rhs) ∧
      Ix.Kernel.reservedBasisNames.contains p₀.cvT.name = false ∧
      Ix.Kernel.reservedBasisNames.contains p₀.cvR.name = false ∧
      (∀ c ∈ cs, c.2.1 = p₀.nP ∧ c.1.levelParams = p₀.cvT.levelParams ∧
        Ix.Kernel.reservedBasisNames.contains c.1.name = false) ∧
      (p₀.recPinned = true →
        rP = p₀.nP + 1 + p₀.ctors.length ∧
        mI = p₀.nP + 1 + p₀.ctors.length + p₀.nIdx ∧
        rules.length = p₀.ctors.length ∧
        ∀ j < p₀.ctors.length, ∀ rule c,
          rules[j]? = some rule → p₀.ctors[j]? = some c →
          rule.ctor = c.1.name ∧ rule.nfields = c.2) := by
  unfold Ix.Kernel.nativeParts? at hp
  cases hs : Ix.Kernel.nativeShape? nPd block with
  | none => rw [hs] at hp; exact nomatch hp
  | some p =>
    rw [hs] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    subst hp
    unfold Ix.Kernel.nativeShape? at hs
    cases block with
    | nil => exact nomatch hs
    | cons hd rest =>
      cases hd with
      | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | ctorInfo _ _ _
      | recInfo _ _ _ _ | projInfo _ => exact nomatch hs
      | indInfo cvT caps₀ =>
        dsimp only at hs
        cases hsp : Ix.Kernel.sumSplit rest with
        | none => rw [hsp] at hs; exact nomatch hs
        | some q =>
          obtain ⟨cs, cvR, mI, rP, rules⟩ := q
          rw [hsp] at hs
          cases hcnt : Ix.Kernel.nativeCounts? nPd cvT cs mI rP with
          | none => rw [hcnt] at hs; exact nomatch hs
          | some pair =>
            obtain ⟨nP, nIdx⟩ := pair
            rw [hcnt] at hs
            have hnP_eq : nP = nPd := by
              unfold Ix.Kernel.nativeCounts? at hcnt
              split at hcnt
              · split at hcnt
                · injection hcnt with hpair; injection hpair with h1 _; exact h1.symm
                · exact nomatch hcnt
              · split at hcnt
                · exact nomatch hcnt
                · split at hcnt
                  · injection hcnt with hpair; injection hpair with h1 _; exact h1.symm
                  · exact nomatch hcnt
            by_cases hcond : (Ix.Kernel.reservedBasisNames.contains cvT.name == false &&
                Ix.Kernel.reservedBasisNames.contains cvR.name == false &&
                cs.all (fun c => c.2.1 == nP && c.1.levelParams == cvT.levelParams &&
                  Ix.Kernel.reservedBasisNames.contains c.1.name == false)) = true
            · rw [ite_eq_left hcond] at hs
              have hpin_unfold :
                  Ix.Kernel.nativeRecPinOk p (.indInfo cvT caps₀ :: rest) = true →
                    rP = p.nP + 1 + p.ctors.length ∧
                    mI = p.nP + 1 + p.ctors.length + p.nIdx ∧
                    rules.length = p.ctors.length ∧
                    ∀ j < p.ctors.length, ∀ rule c,
                      rules[j]? = some rule → p.ctors[j]? = some c →
                      rule.ctor = c.1.name ∧ rule.nfields = c.2 ∧ p.ctors = cs.map (fun x => (x.1, x.2.2)) := by
                intro hpin
                unfold Ix.Kernel.nativeRecPinOk at hpin
                rw [hsp] at hpin
                simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hpin
                obtain ⟨⟨⟨hrP, hmI⟩, hlen⟩, hall⟩ := hpin
                refine ⟨hrP, hmI, hlen, fun j hj rule c hrule hc => ?_⟩
                have hshape_ctors : p.ctors = cs.map (fun x => (x.1, x.2.2)) := by
                  dsimp only at hs
                  split at hs <;> injection hs with hp_eq <;> rw [← hp_eq]
                have hj_cs : j < cs.length := by rw [hshape_ctors, List.length_map] at hj; exact hj
                obtain ⟨c3, hc3⟩ : ∃ c3, cs[j]? = some c3 :=
                  ⟨cs[j]'hj_cs, List.getElem?_eq_getElem hj_cs⟩
                have hj_spec := hall j hj
                rw [hrule, hc3] at hj_spec
                simp only [Bool.and_eq_true, beq_iff_eq] at hj_spec
                rw [hshape_ctors, List.getElem?_map, hc3] at hc
                injection hc with hc_eq; subst hc_eq
                exact ⟨hj_spec.1, hj_spec.2, hshape_ctors⟩
              dsimp only at hs
              have hshape : p.cvT = cvT ∧ p.ctors = cs.map (fun c => (c.1, c.2.2)) ∧
                  p.nP = nP ∧ p.nIdx = nIdx ∧ p.cvR = cvR ∧ p.rhss = rules.map (·.rhs) := by
                split at hs <;> injection hs with hp_eq <;> rw [← hp_eq] <;>
                  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
              obtain ⟨hcvT, hctors, hnP, hnIdx, hcvR, hrhss⟩ := hshape
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcond
              obtain ⟨⟨hbT, hbR⟩, hcs⟩ := hcond
              refine ⟨caps₀, cs, mI, rP, rules, ?_, ?_, hctors, hrhss, ?_, ?_, ?_, ?_⟩
              · dsimp only
                rw [hcvT, hcvR, sumSplit_eq_append_rec hsp]
                rfl
              · dsimp only; rw [hnP, hnP_eq]
              · dsimp only; rwa [hcvT]
              · dsimp only; rwa [hcvR]
              · intro c hc
                have := hcs c hc
                dsimp only
                rw [hnP, hcvT]
                exact ⟨this.1.1, this.1.2, this.2⟩
              · intro hpin
                obtain ⟨hrP, hmI, hlen, hall⟩ := hpin_unfold hpin
                exact ⟨hrP, hmI, hlen, fun j hj rule c hr hc =>
                  let q := hall j hj rule c hr hc
                  ⟨q.1, q.2.1⟩⟩
            · have hcondF := Bool.eq_false_iff.mpr hcond
              rw [hcondF] at hs
              exact nomatch hs

/-! ### `instantiateLevelParams` / `posOf` commutation with recursor & rule generators -/

theorem ilp_liftLooseBVars (ks : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr) (s c : Nat),
      (e.liftLooseBVars s c).instantiateLevelParams ks us =
        (e.instantiateLevelParams ks us).liftLooseBVars s c
  | .bvar i, s, c => by simp only [Expr.liftLooseBVars, Expr.instantiateLevelParams]; split <;> rfl
  | .fvar idx ty, s, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams, ilp_liftLooseBVars ks us ty s c]
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, s, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      ilp_liftLooseBVars ks us f s c, ilp_liftLooseBVars ks us a s c]
  | .lam ty bo m, s, c | .forallE ty bo m, s, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      ilp_liftLooseBVars ks us ty s c, ilp_liftLooseBVars ks us bo s (c + 1)]
  | .letE ty v bo m, s, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      ilp_liftLooseBVars ks us ty s c, ilp_liftLooseBVars ks us v s c,
      ilp_liftLooseBVars ks us bo s (c + 1)]
  | .proj _ _ e, s, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams, ilp_liftLooseBVars ks us e s c]

theorem ilp_mkAppN (ks : List LevelParam) (us : List KLevel) :
    ∀ (args : List KExpr) (f : KExpr),
      (Expr.mkAppN f args).instantiateLevelParams ks us =
        Expr.mkAppN (f.instantiateLevelParams ks us) (args.map (·.instantiateLevelParams ks us))
  | [], _ => rfl
  | a :: as, f => ilp_mkAppN ks us as (.app f a)

theorem ilp_getAppArgs (ks : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr),
      (e.instantiateLevelParams ks us).getAppArgs = e.getAppArgs.map (·.instantiateLevelParams ks us)
  | .app f a => by simp [Expr.instantiateLevelParams, Expr.getAppArgs, ilp_getAppArgs ks us f]
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

theorem ilp_stripPis (ks : List LevelParam) (us : List KLevel) :
    ∀ (k : Nat) {e body : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)},
      e.stripPis k = some (bs, body) →
      (e.instantiateLevelParams ks us).stripPis k =
        some (bs.map (fun b => (b.1.instantiateLevelParams ks us,
          { b.2 with pw := Level.substPW ks us b.2.pw })),
          body.instantiateLevelParams ks us)
  | 0, e, body, bs, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | k + 1, .forallE ty rest m, body, bs, h => by
    rw [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs', body'⟩, hrest, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    simp only [Expr.instantiateLevelParams, Expr.stripPis, ilp_stripPis ks us k hrest, Option.map]
    rfl
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, h | _ + 1, .lit _, _, _, h | _ + 1, .proj _ _ _, _, _, h =>
    nomatch h

theorem ilp_piBinders (ks : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr),
      (e.instantiateLevelParams ks us).piBinders =
        ((e.piBinders).1.map (fun b => (b.1.instantiateLevelParams ks us,
          { b.2 with pw := Level.substPW ks us b.2.pw })),
         (e.piBinders).2.instantiateLevelParams ks us)
  | .forallE ty bo m => by
    simp [Expr.instantiateLevelParams, Ix.Kernel.Expr.piBinders, ilp_piBinders ks us bo]
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

theorem ilp_replacePisPw (ks : List LevelParam) (us : List KLevel) (pw : Ix.Kernel.PropWhen) :
    ∀ (k : Nat) {tele b r : KExpr},
      Expr.replacePisPw pw k tele b = some r →
      Expr.replacePisPw (Level.substPW ks us pw) k
        (tele.instantiateLevelParams ks us) (b.instantiateLevelParams ks us) =
        some (r.instantiateLevelParams ks us)
  | 0, tele, b, r, h => by
    simp only [Expr.replacePisPw, Option.some.injEq] at h
    subst h; rfl
  | k + 1, .forallE ty rest m, b, r, h => by
    simp only [Expr.replacePisPw, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    simp only [Expr.instantiateLevelParams, Expr.replacePisPw,
      ilp_replacePisPw ks us pw k hr', Option.map]
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, h | _ + 1, .lit _, _, _, h | _ + 1, .proj _ _ _, _, _, h =>
    nomatch h

theorem ilp_pisToLamsPw (ks : List LevelParam) (us : List KLevel) (pw : Ix.Kernel.PropWhen) :
    ∀ (k : Nat) {tele b r : KExpr},
      Expr.pisToLamsPw pw k tele b = some r →
      Expr.pisToLamsPw (Level.substPW ks us pw) k
        (tele.instantiateLevelParams ks us) (b.instantiateLevelParams ks us) =
        some (r.instantiateLevelParams ks us)
  | 0, tele, b, r, h => by
    simp only [Expr.pisToLamsPw, Option.some.injEq] at h
    subst h; rfl
  | k + 1, .forallE ty rest m, b, r, h => by
    simp only [Expr.pisToLamsPw, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    simp only [Expr.instantiateLevelParams, Expr.pisToLamsPw,
      ilp_pisToLamsPw ks us pw k hr', Option.map]
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, h | _ + 1, .lit _, _, _, h | _ + 1, .proj _ _ _, _, _, h =>
    nomatch h

theorem option_map_ilp_replacePisPw (ks : List LevelParam) (us : List KLevel)
    (pw : Ix.Kernel.PropWhen) :
    ∀ (k : Nat) (tele b : KExpr),
      (Expr.replacePisPw pw k tele b).map (Expr.instantiateLevelParams ks us) =
        Expr.replacePisPw (Level.substPW ks us pw) k
          (tele.instantiateLevelParams ks us) (b.instantiateLevelParams ks us)
  | 0, _, _ => rfl
  | k + 1, .forallE ty rest m, b => by
    simp only [Expr.replacePisPw, Expr.instantiateLevelParams, Option.map_map]
    rw [← option_map_ilp_replacePisPw ks us pw k rest b, Option.map_map]
    rfl
  | _ + 1, .bvar _, _ | _ + 1, .fvar _ _, _ | _ + 1, .sort _, _
  | _ + 1, .const _ _, _ | _ + 1, .app _ _, _ | _ + 1, .lam _ _ _, _
  | _ + 1, .letE _ _ _ _, _ | _ + 1, .lit _, _ | _ + 1, .proj _ _ _, _ => rfl

theorem option_map_ilp_pisToLamsPw (ks : List LevelParam) (us : List KLevel)
    (pw : Ix.Kernel.PropWhen) :
    ∀ (k : Nat) (tele b : KExpr),
      (Expr.pisToLamsPw pw k tele b).map (Expr.instantiateLevelParams ks us) =
        Expr.pisToLamsPw (Level.substPW ks us pw) k
          (tele.instantiateLevelParams ks us) (b.instantiateLevelParams ks us)
  | 0, _, _ => rfl
  | k + 1, .forallE ty rest m, b => by
    simp only [Expr.pisToLamsPw, Expr.instantiateLevelParams, Option.map_map]
    rw [← option_map_ilp_pisToLamsPw ks us pw k rest b, Option.map_map]
    rfl
  | _ + 1, .bvar _, _ | _ + 1, .fvar _ _, _ | _ + 1, .sort _, _
  | _ + 1, .const _ _, _ | _ + 1, .app _ _, _ | _ + 1, .lam _ _ _, _
  | _ + 1, .letE _ _ _ _, _ | _ + 1, .lit _, _ | _ + 1, .proj _ _ _, _ => rfl

theorem ilp_mkPisOf (ks : List LevelParam) (us : List KLevel) :
    ∀ (bs : List (KExpr × Ix.Kernel.BinderMeta)) (body : KExpr),
      (Ix.Kernel.Expr.mkPisOf bs body).instantiateLevelParams ks us =
        Ix.Kernel.Expr.mkPisOf
          (bs.map fun b => (b.1.instantiateLevelParams ks us,
            { b.2 with pw := Level.substPW ks us b.2.pw }))
          (body.instantiateLevelParams ks us)
  | [], _ => rfl
  | (ty, mt) :: bs, body => by
    simp [Ix.Kernel.Expr.mkPisOf, Expr.instantiateLevelParams, ilp_mkPisOf ks us bs body]

theorem ilp_mkLamsOf (ks : List LevelParam) (us : List KLevel) :
    ∀ (bs : List (KExpr × Ix.Kernel.BinderMeta)) (body : KExpr),
      (Ix.Kernel.Expr.mkLamsOf bs body).instantiateLevelParams ks us =
        Ix.Kernel.Expr.mkLamsOf
          (bs.map fun b => (b.1.instantiateLevelParams ks us,
            { b.2 with pw := Level.substPW ks us b.2.pw }))
          (body.instantiateLevelParams ks us)
  | [], _ => rfl
  | (ty, mt) :: bs, body => by
    simp [Ix.Kernel.Expr.mkLamsOf, Expr.instantiateLevelParams, ilp_mkLamsOf ks us bs body]

theorem ilp_structPsAt (ks : List LevelParam) (us : List KLevel) (o n : Nat) :
    (Ix.Kernel.structPsAt (md := .anon) o n).map (·.instantiateLevelParams ks us) =
      Ix.Kernel.structPsAt o n := by
  simp [Ix.Kernel.structPsAt, Expr.instantiateLevelParams]

theorem ilp_structTeleVars (ks : List LevelParam) (us : List KLevel) (m : Nat) :
    (Ix.Kernel.structTeleVars (md := .anon) m).map (·.instantiateLevelParams ks us) =
      Ix.Kernel.structTeleVars m := by
  simp [Ix.Kernel.structTeleVars, Expr.instantiateLevelParams]

theorem ilp_structRecPrefixAt (ks : List LevelParam) (us : List KLevel) (nP n nF e : Nat) :
    (Ix.Kernel.structRecPrefixAt (md := .anon) nP n nF e).map (·.instantiateLevelParams ks us) =
      Ix.Kernel.structRecPrefixAt nP n nF e := by
  simp [Ix.Kernel.structRecPrefixAt, ilp_structPsAt, Expr.instantiateLevelParams]

theorem ilp_structIdxAt (ks : List LevelParam) (us : List KLevel) (nF o i l m : Nat) (e : KExpr) :
    (Ix.Kernel.structIdxAt nF o i l m e).instantiateLevelParams ks us =
      Ix.Kernel.structIdxAt nF o i l m (e.instantiateLevelParams ks us) := by
  simp [Ix.Kernel.structIdxAt, ilp_liftLooseBVars]

theorem ilp_structTeleAt (ks : List LevelParam) (us : List KLevel)
    (nF o i l : Nat) (pw : Ix.Kernel.PropWhen) (tele : List (KExpr × Ix.Kernel.BinderMeta)) :
    (Ix.Kernel.structTeleAt nF o i l pw tele).map
      (fun b => (b.1.instantiateLevelParams ks us,
        { b.2 with pw := Level.substPW ks us b.2.pw })) =
      Ix.Kernel.structTeleAt nF o i l (Level.substPW ks us pw)
        (tele.map fun b => (b.1.instantiateLevelParams ks us,
          { b.2 with pw := Level.substPW ks us b.2.pw })) := by
  simp only [Ix.Kernel.structTeleAt, List.length_map, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hk]
  simp [ilp_structIdxAt]

theorem ilp_structFieldTeleOf (ks : List LevelParam) (us : List KLevel)
    (cty : KExpr) (nP nF i : Nat)
    (hs : ∃ cbs cbody, cty.stripPis (nP + nF) = some (cbs, cbody) ∧ nP + i < cbs.length) :
    Ix.Kernel.structFieldTeleOf (cty.instantiateLevelParams ks us) nP nF i =
      (Ix.Kernel.structFieldTeleOf cty nP nF i).map
        (fun b => (b.1.instantiateLevelParams ks us,
          { b.2 with pw := Level.substPW ks us b.2.pw })) := by
  obtain ⟨cbs, cbody, hstrip, hlt⟩ := hs
  unfold Ix.Kernel.structFieldTeleOf
  rw [hstrip, ilp_stripPis ks us (nP + nF) hstrip]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt,
    Option.map_some, Option.getD_some, ilp_piBinders]

theorem ilp_structFieldIdxOf (ks : List LevelParam) (us : List KLevel)
    (cty : KExpr) (nP nF i : Nat)
    (hs : ∃ cbs cbody, cty.stripPis (nP + nF) = some (cbs, cbody) ∧ nP + i < cbs.length) :
    Ix.Kernel.structFieldIdxOf (cty.instantiateLevelParams ks us) nP nF i =
      (Ix.Kernel.structFieldIdxOf cty nP nF i).map (·.instantiateLevelParams ks us) := by
  obtain ⟨cbs, cbody, hstrip, hlt⟩ := hs
  unfold Ix.Kernel.structFieldIdxOf
  rw [hstrip, ilp_stripPis ks us (nP + nF) hstrip]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt,
    Option.map_some, Option.getD_some, ilp_piBinders, ilp_getAppArgs, ← List.map_drop]

theorem ilp_structIhPis (ks : List LevelParam) (us : List KLevel)
    (nF o : Nat) (pw : Ix.Kernel.PropWhen)
    (teleOf teleOf' : Nat → List (KExpr × Ix.Kernel.BinderMeta))
    (idxOf idxOf' : Nat → List KExpr) :
    ∀ (is : List Nat) (l : Nat) (body : KExpr),
      (∀ i ∈ is, teleOf' i = (teleOf i).map (fun b => (b.1.instantiateLevelParams ks us,
          { b.2 with pw := Level.substPW ks us b.2.pw })) ∧
        idxOf' i = (idxOf i).map (·.instantiateLevelParams ks us)) →
      (Ix.Kernel.structIhPis nF o pw teleOf idxOf is l body).instantiateLevelParams ks us =
        Ix.Kernel.structIhPis nF o (Level.substPW ks us pw) teleOf' idxOf' is l
          (body.instantiateLevelParams ks us)
  | [], _, _, _ => rfl
  | i :: is, l, body, hfg => by
    obtain ⟨htele, hidx⟩ := hfg i List.mem_cons_self
    have hlen : (teleOf' i).length = (teleOf i).length := by rw [htele, List.length_map]
    simp only [Ix.Kernel.structIhPis, Expr.instantiateLevelParams,
      ilp_mkPisOf, ilp_structTeleAt, ilp_mkAppN, List.map_append, List.map_map,
      List.map_cons, List.map_nil, ilp_structTeleVars,
      ilp_structIhPis ks us nF o pw teleOf teleOf' idxOf idxOf' is (l + 1) body
        (fun k hk => hfg k (List.mem_cons_of_mem _ hk))]
    rw [← htele, hidx, List.map_map, hlen]
    congr 2
    congr 2
    congr 1
    funext e
    exact ilp_structIdxAt ks us nF o i l (teleOf i).length e

theorem ilp_structIhApp (ks : List LevelParam) (us : List KLevel)
    (recC : KKey) (rlvls : List KLevel) (pw : Ix.Kernel.PropWhen) (nP n nF i : Nat)
    (tele : List (KExpr × Ix.Kernel.BinderMeta)) (idx : List KExpr) :
    (Ix.Kernel.structIhApp recC rlvls pw nP n nF i tele idx).instantiateLevelParams ks us =
      Ix.Kernel.structIhApp recC (rlvls.map (Level.subst ks us)) (Level.substPW ks us pw)
        nP n nF i
        (tele.map fun b => (b.1.instantiateLevelParams ks us,
          { b.2 with pw := Level.substPW ks us b.2.pw }))
        (idx.map (·.instantiateLevelParams ks us)) := by
  unfold Ix.Kernel.structIhApp
  simp only [ilp_mkLamsOf, ilp_structTeleAt, ilp_mkAppN, Expr.instantiateLevelParams,
    List.length_map, List.map_append, List.map_map, List.map_cons, List.map_nil,
    ilp_structRecPrefixAt, ilp_structTeleVars]
  congr 2
  congr 1
  congr 1
  apply List.map_congr_left
  intro e _
  exact ilp_structIdxAt ks us nF (n + 1) i 0 tele.length e

/-! ### Level-parameter lists for small (`univ_offset = 0`) and large (`univ_offset = 1`) recursors -/

theorem level_subst_go_cons_ne {k n : LevelParam} {v : KLevel}
    {ks : List LevelParam} {vs : List KLevel} (hne : k ≠ n) :
    Level.subst.go (k :: ks) (v :: vs) n = Level.subst.go ks vs n := by
  simp [Level.subst.go, ite_eq_right hne]

theorem level_subst_cons_unused (k : LevelParam) (v : KLevel)
    (ks : List LevelParam) (vs : List KLevel) (hk_not_in : k ∉ ks) :
    ∀ {u : KLevel}, u.allParamsDefined ks = true →
      Level.subst (k :: ks) (v :: vs) u = Level.subst ks vs u
  | .zero, _ => rfl
  | .succ l, h => congrArg Level.succ (level_subst_cons_unused k v ks vs hk_not_in h)
  | .max l r, h => by
    simp only [Level.allParamsDefined, Bool.and_eq_true] at h
    exact congrArg₂ Level.max
      (level_subst_cons_unused k v ks vs hk_not_in h.1)
      (level_subst_cons_unused k v ks vs hk_not_in h.2)
  | .imax l r, h => by
    simp only [Level.allParamsDefined, Bool.and_eq_true] at h
    exact congrArg₂ Level.imax
      (level_subst_cons_unused k v ks vs hk_not_in h.1)
      (level_subst_cons_unused k v ks vs hk_not_in h.2)
  | .param n, h => by
    simp only [Level.allParamsDefined, List.contains_iff_mem] at h
    have hne : k ≠ n := by intro heq; subst heq; exact hk_not_in h
    exact level_subst_go_cons_ne hne

theorem pw_subst_cons_unused (k : LevelParam) (v : KLevel)
    (ks : List LevelParam) (vs : List KLevel) (hk_not_in : k ∉ ks)
    {pw : Ix.Kernel.PropWhen} (hpw : pw.paramsDefined ks = true) :
    Level.substPW (k :: ks) (v :: vs) pw = Level.substPW ks vs pw := by
  cases pw with
  | never =>
    apply Ix.Kernel.PropWhen.eq_of_holds
    intro φ
    rw [Level.holds_substPW, Level.holds_substPW,
      Ix.Kernel.PropWhen.holds_never, Ix.Kernel.PropWhen.holds_never]
  | ifAllZero ps =>
    simp only [Ix.Kernel.PropWhen.paramsDefined_ifAllZero, List.all_eq_true,
      List.contains_iff_mem] at hpw
    apply Ix.Kernel.PropWhen.eq_of_holds
    intro φ
    rw [Level.holds_substPW, Level.holds_substPW,
      Ix.Kernel.PropWhen.holds_ifAllZero, Ix.Kernel.PropWhen.holds_ifAllZero]
    have hcongr : ps.all (fun n => Level.substFn φ (k :: ks) (v :: vs) n == 0) =
        ps.all (fun n => Level.substFn φ ks vs n == 0) := by
      have hsub : ∀ n ∈ ps,
          (Level.substFn φ (k :: ks) (v :: vs) n == 0) = (Level.substFn φ ks vs n == 0) := by
        intro n hn
        have hne : k ≠ n := fun heq => hk_not_in (by rw [heq]; exact hpw n hn)
        rw [← Level.eval_subst_go, ← Level.eval_subst_go, level_subst_go_cons_ne hne]
      induction ps with
      | nil => rfl
      | cons p rest ih =>
        simp only [List.all_cons]
        rw [hsub p List.mem_cons_self,
          ih (fun x hx => hpw x (List.mem_cons_of_mem _ hx))
             (fun x hx => hsub x (List.mem_cons_of_mem _ hx))]
    exact hcongr

/-- If `e.allLevelParamsDefined (List.range n) = true`, then `posOf (n :: List.range n) e`
equals `e.instantiateLevelParams (List.range n) ((List.range n).map (fun i => .param (1 + i)))`. -/
theorem posOf_large_eq_inst_shifted (n : Nat) :
    ∀ {e : KExpr}, e.allLevelParamsDefined (List.range n) = true →
      posOf (n :: List.range n) e =
        e.instantiateLevelParams (List.range n) ((List.range n).map fun i => Level.param (1 + i)) := by
  have hpos : posLevels (n :: List.range n) =
      Level.param 0 :: (List.range n).map (fun i => Level.param (1 + i)) := by
    simp only [posLevels, List.length_cons, List.length_range, List.range_succ_eq_map,
      List.map_cons, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro x _
    simp [Nat.add_comm]
  have hnot_in : n ∉ List.range n := by simp [List.mem_range]
  intro e he
  unfold posOf
  rw [hpos]
  induction e with
  | bvar _ | lit _ => rfl
  | fvar idx ty ih =>
    exact congrArg (Expr.fvar idx) (ih he)
  | sort u =>
    exact congrArg Expr.sort (level_subst_cons_unused n _ _ _ hnot_in he)
  | const nm vs =>
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at he
    simp only [Expr.instantiateLevelParams]
    congr 1
    apply List.map_congr_left
    intro v hv
    exact level_subst_cons_unused n _ _ _ hnot_in (he v hv)
  | app f a ihf iha =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at he
    exact congrArg₂ Expr.app (ihf he.1) (iha he.2)
  | lam ty bo m iht ihb =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at he
    simp only [Expr.instantiateLevelParams, iht he.1.1, ihb he.1.2,
      pw_subst_cons_unused n _ _ _ hnot_in he.2]
  | forallE ty bo m iht ihb =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at he
    simp only [Expr.instantiateLevelParams, iht he.1.1, ihb he.1.2,
      pw_subst_cons_unused n _ _ _ hnot_in he.2]
  | letE ty v bo m iht ihv ihb =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at he
    simp only [Expr.instantiateLevelParams, iht he.1.1, ihv he.1.2, ihb he.2]
  | proj s i e ih =>
    exact congrArg (Expr.proj s i) (ih he)

theorem level_subst_range_go :
    ∀ (m s k : Nat) (vs : List KLevel) (hk : k < m) (hlen : vs.length = m),
      Level.subst.go ((List.range m).map (s + ·)) vs (s + k) = vs[k]'(hk.trans_eq hlen.symm)
  | 0, _, _, _, hk, _ => nomatch hk
  | m + 1, s, 0, v :: vs, _, _ => by simp [List.range_succ_eq_map, Level.subst.go]
  | m + 1, s, k + 1, v :: vs, hk, hlen => by
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def, Nat.add_zero]
    rw [level_subst_go_cons_ne (show s ≠ s + (k + 1) by omega)]
    have hmap : List.map (fun x => s + x.succ) (List.range m) =
        List.map ((s + 1) + ·) (List.range m) := by
      apply List.map_congr_left; intro x _; omega
    rw [hmap, show s + (k + 1) = (s + 1) + k by omega]
    exact level_subst_range_go m (s + 1) k vs (by omega) (by simp at hlen; omega)
  | _ + 1, _, _, [], _, hlen => nomatch hlen

theorem map_subst_range_params (n : Nat) (vs : List KLevel) (hlen : vs.length = n) :
    ((List.range n).map Level.param).map (Level.subst (List.range n) vs) = vs := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi1 hi2
    simp only [List.length_map, List.length_range] at hi1
    simp only [List.getElem_map, List.getElem_range]
    have h0 := level_subst_range_go n 0 i vs hi1 hlen
    simpa [Nat.zero_add, Level.subst] using h0

theorem map_subst_large_former_params (n : Nat) :
    ((List.range n).map Level.param).map
        (Level.subst (n :: List.range n) (posLevels (n :: List.range n))) =
      (List.range n).map (fun i => Level.param (1 + i)) := by
  have hpos : posLevels (n :: List.range n) =
      Level.param 0 :: (List.range n).map (fun i => Level.param (1 + i)) := by
    simp only [posLevels, List.length_cons, List.length_range, List.range_succ_eq_map,
      List.map_cons, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro x _
    simp [Nat.add_comm]
  have hnot_in : n ∉ List.range n := by simp [List.mem_range]
  rw [hpos]
  calc
    ((List.range n).map Level.param).map
        (Level.subst (n :: List.range n) (Level.param 0 :: (List.range n).map (fun i => Level.param (1 + i))))
      = ((List.range n).map Level.param).map
          (Level.subst (List.range n) ((List.range n).map (fun i => Level.param (1 + i)))) := by
        apply List.map_congr_left
        intro u hu
        simp only [List.mem_map] at hu
        obtain ⟨k, hk, rfl⟩ := hu
        exact level_subst_cons_unused n _ _ _ hnot_in
          (by simp [Level.allParamsDefined, List.contains_iff_mem, hk])
    _ = (List.range n).map (fun i => Level.param (1 + i)) :=
        map_subst_range_params n _ (by simp)

theorem map_subst_large_rec_params (n : Nat) :
    ((n :: List.range n).map Level.param).map
        (Level.subst (n :: List.range n) (posLevels (n :: List.range n))) =
      (List.range (n + 1)).map Level.param := by
  have hpos : posLevels (n :: List.range n) =
      Level.param 0 :: (List.range n).map (fun i => Level.param (1 + i)) := by
    simp only [posLevels, List.length_cons, List.length_range, List.range_succ_eq_map,
      List.map_cons, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro x _
    simp [Nat.add_comm]
  simp only [List.map_cons]
  have hhead : Level.subst (n :: List.range n) (posLevels (n :: List.range n)) (.param n) =
      Level.param 0 := by
    rw [hpos]; simp [Level.subst, Level.subst.go]
  rw [hhead, map_subst_large_former_params n, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro x _
  simp [Nat.add_comm]

/-! ### Syntactic scoping (`GenScoped`) and existence of `structRecTyR` / `structRecRhsR` -/

/-- Combined syntactic well-scopedness for generated recursor types and rule RHSs:
loose-bvar bound, level-parameter coverage, constant resolution, `hasFvar = false`, and
`defnAritiesOk` (needed for `WrapRelSem.defeq`). -/
def GenScoped (env : Ix.Kernel.Env .anon) (rlps : List LevelParam) (b : Nat) (e : KExpr) : Prop :=
  e.looseBVarsBounded b = true ∧
  e.allLevelParamsDefined rlps = true ∧
  e.constsResolve env = true ∧
  e.hasFvar = false ∧
  defnAritiesOk env.find? e = true

theorem GenScoped.mono_b {env : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b₁ b₂ : Nat}
    {e : KExpr} (hle : b₁ ≤ b₂) (h : GenScoped env rlps b₁ e) : GenScoped env rlps b₂ e :=
  ⟨Expr.looseBVarsBounded_mono hle h.1, h.2⟩

theorem constsResolve_mono_env {env₁ env₂ : Ix.Kernel.Env .anon}
    (hsub : ∀ k ci, env₁.find? k = some ci → env₂.find? k = some ci) :
    ∀ {e : KExpr}, e.constsResolve env₁ = true → e.constsResolve env₂ = true
  | .bvar _ | .sort _ | .lit _ => fun _ => by simp [Expr.constsResolve]
  | .fvar _ _ => fun h => constsResolve_mono_env hsub h
  | .const n _ => fun h => by
    have hc : (env₁.find? n).isSome = true := h
    rw [Option.isSome_iff_exists] at hc
    obtain ⟨ci, hci⟩ := hc
    simp [Expr.constsResolve, hsub n ci hci]
  | .app _ _ => fun h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨constsResolve_mono_env hsub h.1, constsResolve_mono_env hsub h.2⟩
  | .lam _ _ _ | .forallE _ _ _ => fun h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨constsResolve_mono_env hsub h.1, constsResolve_mono_env hsub h.2⟩
  | .letE _ _ _ _ => fun h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨constsResolve_mono_env hsub h.1.1, constsResolve_mono_env hsub h.1.2⟩,
      constsResolve_mono_env hsub h.2⟩
  | .proj _ _ _ => fun h => constsResolve_mono_env hsub h

theorem GenScoped.mono_env {env₁ env₂ : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b : Nat}
    {e : KExpr}
    (hsub : ∀ k ci, env₁.find? k = some ci → env₂.find? k = some ci)
    (hdefn : ∀ n cv v hn, env₂.find? n = some (.defnInfo cv v hn) →
      env₁.find? n = some (.defnInfo cv v hn))
    (h : GenScoped env₁ rlps b e) : GenScoped env₂ rlps b e :=
  ⟨h.1, h.2.1, constsResolve_mono_env hsub h.2.2.1, h.2.2.2.1,
    defnAritiesOk_congr_defn hdefn e h.2.2.2.2⟩

theorem GenScoped.mono_lps {env : Ix.Kernel.Env .anon} {lps₁ lps₂ : List LevelParam} {b : Nat}
    {e : KExpr} (hsub : ∀ x ∈ lps₁, x ∈ lps₂) (h : GenScoped env lps₁ b e) :
    GenScoped env lps₂ b e := by
  refine ⟨h.1, ?_, h.2.2⟩
  have hl : ∀ {u : KLevel}, u.allParamsDefined lps₁ = true → u.allParamsDefined lps₂ = true := by
    intro u
    induction u with
    | zero => intro _; rfl
    | succ l ih => exact ih
    | max l r ihl ihr | imax l r ihl ihr =>
      simp only [Level.allParamsDefined, Bool.and_eq_true]
      exact fun ⟨h1, h2⟩ => ⟨ihl h1, ihr h2⟩
    | param n =>
      simp only [Level.allParamsDefined, List.contains_iff_mem]
      exact fun hn => hsub n hn
  have hpw : ∀ {pw : Ix.Kernel.PropWhen},
      pw.paramsDefined lps₁ = true → pw.paramsDefined lps₂ = true := by
    intro pw
    cases pw with
    | never => intro _; rfl
    | ifAllZero ps =>
      simp only [Ix.Kernel.PropWhen.paramsDefined_ifAllZero, List.all_eq_true,
        List.contains_iff_mem]
      exact fun hps p hp => hsub p (hps p hp)
  have he := h.2.1
  clear h
  revert he
  induction e with
  | bvar _ | lit _ => intro _; rfl
  | fvar _ _ ih => exact ih
  | sort u => exact hl
  | const _ vs =>
    simp only [Expr.allLevelParamsDefined, List.all_eq_true]
    exact fun hv v hmem => hl (hv v hmem)
  | app f a ihf iha =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact fun ⟨h1, h2⟩ => ⟨ihf h1, iha h2⟩
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨iht h1, ihb h2⟩, hpw h3⟩
  | letE _ _ _ _ iht ihv ihb =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨iht h1, ihv h2⟩, ihb h3⟩
  | proj _ _ _ ih => exact ih

theorem GenScoped.bvar {env : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b i : Nat}
    (hi : i < b) : GenScoped env rlps b (.bvar i) :=
  ⟨by simp [Expr.looseBVarsBounded, hi], rfl, rfl, rfl, rfl⟩

theorem GenScoped.sort {env : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b : Nat} {u : KLevel}
    (hu : u.allParamsDefined rlps = true) : GenScoped env rlps b (.sort u) :=
  ⟨rfl, hu, rfl, rfl, rfl⟩

theorem GenScoped.const_nonDefn {env : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b : Nat}
    {nm : KKey} {us : List KLevel}
    (hres : (env.find? nm).isSome = true)
    (hnot_defn : ∀ cv v hn, env.find? nm ≠ some (.defnInfo cv v hn))
    (hus : ∀ u ∈ us, u.allParamsDefined rlps = true) :
    GenScoped env rlps b (.const nm us) := by
  refine ⟨rfl, ?_, hres, rfl, ?_⟩
  · simp only [Expr.allLevelParamsDefined, List.all_eq_true]
    exact hus
  · simp only [defnAritiesOk]

theorem GenScoped.app {env : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b : Nat}
    {f a : KExpr} (hf : GenScoped env rlps b f) (ha : GenScoped env rlps b a) :
    GenScoped env rlps b (.app f a) :=
  ⟨by simp [Expr.looseBVarsBounded, hf.1, ha.1],
   by simp [Expr.allLevelParamsDefined, hf.2.1, ha.2.1],
   by simp [Expr.constsResolve, hf.2.2.1, ha.2.2.1],
   by simp [Expr.hasFvar, hf.2.2.2.1, ha.2.2.2.1],
   by simp [defnAritiesOk, hf.2.2.2.2, ha.2.2.2.2]⟩

theorem GenScoped.mkAppN {env : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b : Nat}
    {args : List KExpr} {f : KExpr}
    (hf : GenScoped env rlps b f) (has : ∀ a ∈ args, GenScoped env rlps b a) :
    GenScoped env rlps b (Expr.mkAppN f args) := by
  induction args generalizing f with
  | nil => exact hf
  | cons a as ih =>
    exact ih (hf.app (has a List.mem_cons_self))
      (fun x hx => has x (List.mem_cons_of_mem _ hx))

theorem GenScoped.forallE {env : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b : Nat}
    {ty bo : KExpr} {pw : Ix.Kernel.PropWhen}
    (hpw : pw.paramsDefined rlps = true)
    (hty : GenScoped env rlps b ty) (hbo : GenScoped env rlps (b + 1) bo) :
    GenScoped env rlps b (.forallE ty bo { pw }) :=
  ⟨by simp [Expr.looseBVarsBounded, hty.1, hbo.1],
   by simp [Expr.allLevelParamsDefined, hty.2.1, hbo.2.1, hpw],
   by simp [Expr.constsResolve, hty.2.2.1, hbo.2.2.1],
   by simp [Expr.hasFvar, hty.2.2.2.1, hbo.2.2.2.1],
   by simp [defnAritiesOk, hty.2.2.2.2, hbo.2.2.2.2]⟩

theorem GenScoped.lam {env : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b : Nat}
    {ty bo : KExpr} {pw : Ix.Kernel.PropWhen}
    (hpw : pw.paramsDefined rlps = true)
    (hty : GenScoped env rlps b ty) (hbo : GenScoped env rlps (b + 1) bo) :
    GenScoped env rlps b (.lam ty bo { pw }) :=
  ⟨by simp [Expr.looseBVarsBounded, hty.1, hbo.1],
   by simp [Expr.allLevelParamsDefined, hty.2.1, hbo.2.1, hpw],
   by simp [Expr.constsResolve, hty.2.2.1, hbo.2.2.1],
   by simp [Expr.hasFvar, hty.2.2.2.1, hbo.2.2.2.1],
   by simp [defnAritiesOk, hty.2.2.2.2, hbo.2.2.2.2]⟩

theorem GenScoped.liftLooseBVars {env : Ix.Kernel.Env .anon} {rlps : List LevelParam}
    (k : Nat) :
    ∀ {e : KExpr} {b c : Nat},
      GenScoped env rlps b e → GenScoped env rlps (b + k) (e.liftLooseBVars k c) := by
  have hall : ∀ (e : KExpr) (c : Nat),
      (e.liftLooseBVars k c).allLevelParamsDefined rlps = e.allLevelParamsDefined rlps ∧
      (e.liftLooseBVars k c).constsResolve env = e.constsResolve env ∧
      (e.liftLooseBVars k c).hasFvar = e.hasFvar := by
    intro e
    induction e with
    | bvar _ =>
      intro c
      simp only [Expr.liftLooseBVars]
      split <;> exact ⟨rfl, rfl, rfl⟩
    | fvar _ ty ih =>
      intro c
      obtain ⟨h1, h2, _⟩ := ih c
      simp [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Expr.constsResolve,
        Expr.hasFvar, h1, h2]
    | sort _ | const _ _ | lit _ => intro _; exact ⟨rfl, rfl, rfl⟩
    | app f a ihf iha =>
      intro c
      obtain ⟨f1, f2, f3⟩ := ihf c
      obtain ⟨a1, a2, a3⟩ := iha c
      simp [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Expr.constsResolve,
        Expr.hasFvar, f1, f2, f3, a1, a2, a3]
    | lam ty bo _ iht ihb | forallE ty bo _ iht ihb =>
      intro c
      obtain ⟨t1, t2, t3⟩ := iht c
      obtain ⟨b1, b2, b3⟩ := ihb (c + 1)
      simp [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Expr.constsResolve,
        Expr.hasFvar, t1, t2, t3, b1, b2, b3]
    | letE ty v bo _ iht ihv ihb =>
      intro c
      obtain ⟨t1, t2, t3⟩ := iht c
      obtain ⟨v1, v2, v3⟩ := ihv c
      obtain ⟨b1, b2, b3⟩ := ihb (c + 1)
      simp [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Expr.constsResolve,
        Expr.hasFvar, t1, t2, t3, v1, v2, v3, b1, b2, b3]
    | proj _ _ e₀ ih =>
      intro c
      obtain ⟨e1, e2, e3⟩ := ih c
      simp [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Expr.constsResolve,
        Expr.hasFvar, e1, e2, e3]
  intro e b c he
  obtain ⟨h1, h2, h3⟩ := hall e c
  exact ⟨Ix.Kernel.Expr.looseBVarsBounded_liftLooseBVars k e he.1,
    by rw [h1]; exact he.2.1,
    by rw [h2]; exact he.2.2.1,
    by rw [h3]; exact he.2.2.2.1,
    by rw [defnAritiesOk_liftLooseBVars]; exact he.2.2.2.2⟩

theorem GenScoped.getAppArgs {env : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b : Nat} :
    ∀ {e : KExpr}, GenScoped env rlps b e → ∀ a ∈ e.getAppArgs, GenScoped env rlps b a
  | .app f a, h, x, hx => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    have hf : GenScoped env rlps b f :=
      ⟨(Bool.and_eq_true _ _).mp h.1 |>.1,
       (Bool.and_eq_true _ _).mp h.2.1 |>.1,
       (Bool.and_eq_true _ _).mp h.2.2.1 |>.1,
       (Bool.or_eq_false_iff.mp h.2.2.2.1).1,
       (Bool.and_eq_true _ _).mp h.2.2.2.2 |>.1⟩
    have ha : GenScoped env rlps b a :=
      ⟨(Bool.and_eq_true _ _).mp h.1 |>.2,
       (Bool.and_eq_true _ _).mp h.2.1 |>.2,
       (Bool.and_eq_true _ _).mp h.2.2.1 |>.2,
       (Bool.or_eq_false_iff.mp h.2.2.2.1).2,
       (Bool.and_eq_true _ _).mp h.2.2.2.2 |>.2⟩
    rcases hx with hx | rfl
    · exact GenScoped.getAppArgs hf x hx
    · exact ha
  | .bvar _, _, _, hx | .fvar _ _, _, _, hx | .sort _, _, _, hx | .const _ _, _, _, hx
  | .lam _ _ _, _, _, hx | .forallE _ _ _, _, _, hx | .letE _ _ _ _, _, _, hx
  | .lit _, _, _, hx | .proj _ _ _, _, _, hx => by simp [Expr.getAppArgs] at hx

theorem stripPis_add :
    ∀ (a b : Nat) {e mid body : KExpr} {bs₁ bs₂ : List (KExpr × Ix.Kernel.BinderMeta)},
      e.stripPis a = some (bs₁, mid) →
      mid.stripPis b = some (bs₂, body) →
      e.stripPis (a + b) = some (bs₁ ++ bs₂, body)
  | 0, b, e, mid, body, bs₁, bs₂, h1, h2 => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simpa [Nat.zero_add] using h2
  | a + 1, b, .forallE ty bo m, mid, body, bs₁, bs₂, h1, h2 => by
    rw [Expr.stripPis, Option.map_eq_some_iff] at h1
    obtain ⟨⟨bs₁', mid'⟩, h1', heq⟩ := h1
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [Nat.succ_add, Expr.stripPis, stripPis_add a b h1' h2]
    rfl
  | _ + 1, _, .bvar _, _, _, _, _, h1, _ | _ + 1, _, .fvar _ _, _, _, _, _, h1, _
  | _ + 1, _, .sort _, _, _, _, _, h1, _ | _ + 1, _, .const _ _, _, _, _, _, h1, _
  | _ + 1, _, .app _ _, _, _, _, _, h1, _ | _ + 1, _, .lam _ _ _, _, _, _, _, h1, _
  | _ + 1, _, .letE _ _ _ _, _, _, _, _, h1, _ | _ + 1, _, .lit _, _, _, _, _, h1, _
  | _ + 1, _, .proj _ _ _, _, _, _, _, h1, _ => nomatch h1

theorem stripPis_length :
    ∀ (k : Nat) {e body : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)},
      e.stripPis k = some (bs, body) → bs.length = k
  | 0, _, _, _, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | k + 1, .forallE _ bo _, _, _, h => by
    rw [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs', _⟩, hbo, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    rw [← heq.1, List.length_cons, stripPis_length k hbo]
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, h | _ + 1, .lit _, _, _, h | _ + 1, .proj _ _ _, _, _, h =>
    nomatch h

theorem GenScoped.stripPis :
    ∀ (k : Nat) {env : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b : Nat}
      {e body : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)},
      e.stripPis k = some (bs, body) →
      GenScoped env rlps b e →
      bs.length = k ∧
      (∀ i < k, GenScoped env rlps (b + i) (bs.getD i default).1) ∧
      GenScoped env rlps (b + k) body
  | 0, _, _, b, e, body, bs, hs, he => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨rfl, (fun _ hi => nomatch hi), by rwa [Nat.add_zero]⟩
  | k + 1, env, rlps, b, .forallE ty rest m, body, bs, hs, he => by
    rw [Expr.stripPis, Option.map_eq_some_iff] at hs
    obtain ⟨⟨bs', body'⟩, hrest, hpair⟩ := hs
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    have hty : GenScoped env rlps b ty :=
      ⟨(Bool.and_eq_true _ _).mp he.1 |>.1,
       ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp he.2.1 |>.1)).1,
       (Bool.and_eq_true _ _).mp he.2.2.1 |>.1,
       (Bool.or_eq_false_iff.mp he.2.2.2.1).1,
       (Bool.and_eq_true _ _).mp he.2.2.2.2 |>.1⟩
    have hbo : GenScoped env rlps (b + 1) rest :=
      ⟨(Bool.and_eq_true _ _).mp he.1 |>.2,
       ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp he.2.1 |>.1)).2,
       (Bool.and_eq_true _ _).mp he.2.2.1 |>.2,
       (Bool.or_eq_false_iff.mp he.2.2.2.1).2,
       (Bool.and_eq_true _ _).mp he.2.2.2.2 |>.2⟩
    obtain ⟨hlen, hdoms, hbody⟩ := GenScoped.stripPis k hrest hbo
    refine ⟨by simp [hlen], fun i hi => ?_, ?_⟩
    · cases i with
      | zero =>
        rw [Nat.add_zero]
        exact hty
      | succ i' =>
        have h := hdoms i' (by omega)
        rw [show b + 1 + i' = b + (i' + 1) by omega] at h
        exact h
    · rw [show b + 1 + k = b + (k + 1) by omega] at hbody
      exact hbody
  | _ + 1, _, _, _, .bvar _, _, _, hs, _ | _ + 1, _, _, _, .fvar _ _, _, _, hs, _
  | _ + 1, _, _, _, .sort _, _, _, hs, _ | _ + 1, _, _, _, .const _ _, _, _, hs, _
  | _ + 1, _, _, _, .app _ _, _, _, hs, _ | _ + 1, _, _, _, .lam _ _ _, _, _, hs, _
  | _ + 1, _, _, _, .letE _ _ _ _, _, _, hs, _ | _ + 1, _, _, _, .lit _, _, _, hs, _
  | _ + 1, _, _, _, .proj _ _ _, _, _, hs, _ => nomatch hs

theorem GenScoped.piBinders :
    ∀ {env : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b : Nat} {e : KExpr},
      GenScoped env rlps b e →
      (∀ k < (e.piBinders).1.length, GenScoped env rlps (b + k) ((e.piBinders).1.getD k default).1) ∧
      GenScoped env rlps (b + (e.piBinders).1.length) (e.piBinders).2
  | env, rlps, b, .forallE ty rest m, he => by
    have hty : GenScoped env rlps b ty :=
      ⟨(Bool.and_eq_true _ _).mp he.1 |>.1,
       ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp he.2.1 |>.1)).1,
       (Bool.and_eq_true _ _).mp he.2.2.1 |>.1,
       (Bool.or_eq_false_iff.mp he.2.2.2.1).1,
       (Bool.and_eq_true _ _).mp he.2.2.2.2 |>.1⟩
    have hbo : GenScoped env rlps (b + 1) rest :=
      ⟨(Bool.and_eq_true _ _).mp he.1 |>.2,
       ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp he.2.1 |>.1)).2,
       (Bool.and_eq_true _ _).mp he.2.2.1 |>.2,
       (Bool.or_eq_false_iff.mp he.2.2.2.1).2,
       (Bool.and_eq_true _ _).mp he.2.2.2.2 |>.2⟩
    obtain ⟨hdoms, hlast⟩ := GenScoped.piBinders hbo
    simp only [Ix.Kernel.Expr.piBinders, List.length_cons]
    refine ⟨fun k hk => ?_, ?_⟩
    · cases k with
      | zero => rw [Nat.add_zero]; exact hty
      | succ k' =>
        have h := hdoms k' (by omega)
        rw [show b + 1 + k' = b + (k' + 1) by omega] at h
        exact h
    · rw [show b + 1 + (rest.piBinders).1.length = b + ((rest.piBinders).1.length + 1) by omega] at hlast
      exact hlast
  | _, _, b, .bvar _, he | _, _, b, .fvar _ _, he | _, _, b, .sort _, he
  | _, _, b, .const _ _, he | _, _, b, .app _ _, he | _, _, b, .lam _ _ _, he
  | _, _, b, .letE _ _ _ _, he | _, _, b, .lit _, he | _, _, b, .proj _ _ _, he =>
    ⟨(fun _ hk => nomatch hk), by simpa [Ix.Kernel.Expr.piBinders] using he⟩

theorem GenScoped.replacePisPw :
    ∀ (k : Nat) {env : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b : Nat}
      {pw : Ix.Kernel.PropWhen} {tele body r : KExpr},
      pw.paramsDefined rlps = true →
      Expr.replacePisPw pw k tele body = some r →
      GenScoped env rlps b tele →
      GenScoped env rlps (b + k) body →
      GenScoped env rlps b r
  | 0, _, _, b, _, _, body, r, _, hs, _, hbo => by
    simp only [Expr.replacePisPw, Option.some.injEq] at hs
    subst hs; rwa [Nat.add_zero] at hbo
  | k + 1, env, rlps, b, pw, .forallE ty rest m, body, r, hpw, hs, htele, hbo => by
    simp only [Expr.replacePisPw, Option.map_eq_some_iff] at hs
    obtain ⟨r', hr', rfl⟩ := hs
    have hty : GenScoped env rlps b ty :=
      ⟨(Bool.and_eq_true _ _).mp htele.1 |>.1,
       ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp htele.2.1 |>.1)).1,
       (Bool.and_eq_true _ _).mp htele.2.2.1 |>.1,
       (Bool.or_eq_false_iff.mp htele.2.2.2.1).1,
       (Bool.and_eq_true _ _).mp htele.2.2.2.2 |>.1⟩
    have hrest : GenScoped env rlps (b + 1) rest :=
      ⟨(Bool.and_eq_true _ _).mp htele.1 |>.2,
       ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp htele.2.1 |>.1)).2,
       (Bool.and_eq_true _ _).mp htele.2.2.1 |>.2,
       (Bool.or_eq_false_iff.mp htele.2.2.2.1).2,
       (Bool.and_eq_true _ _).mp htele.2.2.2.2 |>.2⟩
    have hbo' : GenScoped env rlps ((b + 1) + k) body := by
      rwa [show (b + 1) + k = b + (k + 1) by omega]
    exact GenScoped.forallE hpw hty (GenScoped.replacePisPw k hpw hr' hrest hbo')
  | _ + 1, _, _, _, _, .bvar _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .fvar _ _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .sort _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .const _ _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .app _ _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .lam _ _ _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .letE _ _ _ _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .lit _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .proj _ _ _, _, _, _, hs, _, _ => nomatch hs

theorem GenScoped.pisToLamsPw :
    ∀ (k : Nat) {env : Ix.Kernel.Env .anon} {rlps : List LevelParam} {b : Nat}
      {pw : Ix.Kernel.PropWhen} {tele body r : KExpr},
      pw.paramsDefined rlps = true →
      Expr.pisToLamsPw pw k tele body = some r →
      GenScoped env rlps b tele →
      GenScoped env rlps (b + k) body →
      GenScoped env rlps b r
  | 0, _, _, b, _, _, body, r, _, hs, _, hbo => by
    simp only [Expr.pisToLamsPw, Option.some.injEq] at hs
    subst hs; rwa [Nat.add_zero] at hbo
  | k + 1, env, rlps, b, pw, .forallE ty rest m, body, r, hpw, hs, htele, hbo => by
    simp only [Expr.pisToLamsPw, Option.map_eq_some_iff] at hs
    obtain ⟨r', hr', rfl⟩ := hs
    have hty : GenScoped env rlps b ty :=
      ⟨(Bool.and_eq_true _ _).mp htele.1 |>.1,
       ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp htele.2.1 |>.1)).1,
       (Bool.and_eq_true _ _).mp htele.2.2.1 |>.1,
       (Bool.or_eq_false_iff.mp htele.2.2.2.1).1,
       (Bool.and_eq_true _ _).mp htele.2.2.2.2 |>.1⟩
    have hrest : GenScoped env rlps (b + 1) rest :=
      ⟨(Bool.and_eq_true _ _).mp htele.1 |>.2,
       ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp htele.2.1 |>.1)).2,
       (Bool.and_eq_true _ _).mp htele.2.2.1 |>.2,
       (Bool.or_eq_false_iff.mp htele.2.2.2.1).2,
       (Bool.and_eq_true _ _).mp htele.2.2.2.2 |>.2⟩
    have hbo' : GenScoped env rlps ((b + 1) + k) body := by
      rwa [show (b + 1) + k = b + (k + 1) by omega]
    exact GenScoped.lam hpw hty (GenScoped.pisToLamsPw k hpw hr' hrest hbo')
  | _ + 1, _, _, _, _, .bvar _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .fvar _ _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .sort _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .const _ _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .app _ _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .lam _ _ _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .letE _ _ _ _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .lit _, _, _, _, hs, _, _
  | _ + 1, _, _, _, _, .proj _ _ _, _, _, _, hs, _, _ => nomatch hs

theorem GenScoped.structPsAt {env : Ix.Kernel.Env .anon} {rlps : List LevelParam}
    {b o n : Nat} (hb : o + n ≤ b) :
    ∀ a ∈ Ix.Kernel.structPsAt (md := .anon) o n, GenScoped env rlps b a := by
  intro a ha
  simp only [Ix.Kernel.structPsAt, List.mem_map, List.mem_range] at ha
  obtain ⟨k, hk, rfl⟩ := ha
  exact GenScoped.bvar (by omega)

theorem GenScoped.structTeleVars {env : Ix.Kernel.Env .anon} {rlps : List LevelParam}
    {b m : Nat} (hb : m ≤ b) :
    ∀ a ∈ Ix.Kernel.structTeleVars (md := .anon) m, GenScoped env rlps b a := by
  intro a ha
  simp only [Ix.Kernel.structTeleVars, List.mem_map, List.mem_range] at ha
  obtain ⟨k, hk, rfl⟩ := ha
  exact GenScoped.bvar (by omega)

theorem GenScoped.structIdxAt {env : Ix.Kernel.Env .anon} {rlps : List LevelParam}
    {nP nF o i l m : Nat} {e : KExpr} (hi : i < nF)
    (he : GenScoped env rlps (nP + i + m) e) :
    GenScoped env rlps (nP + o + nF + l + m) (Ix.Kernel.structIdxAt nF o i l m e) := by
  unfold Ix.Kernel.structIdxAt
  have h1 := GenScoped.liftLooseBVars (nF - i + l) (c := m) he
  have h2 := GenScoped.liftLooseBVars o (c := nF + l + m) h1
  rwa [show nP + i + m + (nF - i + l) + o = nP + o + nF + l + m by omega] at h2

theorem GenScoped.mkPisOf_structTeleAt {env : Ix.Kernel.Env .anon} {rlps : List LevelParam}
    {nP nF o i l : Nat} {pw : Ix.Kernel.PropWhen} {tele : List (KExpr × Ix.Kernel.BinderMeta)}
    {body : KExpr}
    (hpw : pw.paramsDefined rlps = true) (hi : i < nF)
    (htele : ∀ k < tele.length, GenScoped env rlps (nP + i + k) (tele.getD k default).1)
    (hbo : GenScoped env rlps (nP + o + nF + l + tele.length) body) :
    GenScoped env rlps (nP + o + nF + l)
      (Ix.Kernel.Expr.mkPisOf (Ix.Kernel.structTeleAt nF o i l pw tele) body) := by
  unfold Ix.Kernel.structTeleAt
  suffices hgo : ∀ (s : Nat) (rem : List Nat),
      s + rem.length = tele.length →
      rem = (List.range rem.length).map (s + ·) →
      GenScoped env rlps (nP + o + nF + l + s)
        (Ix.Kernel.Expr.mkPisOf
          (rem.map fun k => (Ix.Kernel.structIdxAt nF o i l k (tele.getD k default).1, { pw }))
          body) by
    have h0 := hgo 0 (List.range tele.length) (by simp) (by simp)
    simpa [Nat.add_zero] using h0
  intro s rem
  induction rem generalizing s with
  | nil =>
    intro hsum _
    have hs_eq : s = tele.length := by simpa using hsum
    subst hs_eq
    simpa [Ix.Kernel.Expr.mkPisOf] using hbo
  | cons k ks ih =>
    intro hsum hrem
    have hk_eq : k = s := by
      have := congrArg List.head? hrem
      simp [List.range_succ_eq_map] at this
      exact this
    subst hk_eq
    have hks : ks = (List.range ks.length).map ((k + 1) + ·) := by
      simp only [List.length_cons] at hrem
      rw [List.range_succ_eq_map, List.map_cons, List.map_map] at hrem
      injection hrem with _ htl
      rw [htl]
      simp only [List.length_map, List.length_range]
      apply List.map_congr_left; intro x _; omega
    simp only [List.map_cons, Ix.Kernel.Expr.mkPisOf]
    refine GenScoped.forallE hpw (GenScoped.structIdxAt hi (htele k (by simp at hsum; omega))) ?_
    exact ih (k + 1) (by simp at hsum; omega) hks

theorem GenScoped.mkLamsOf_structTeleAt {env : Ix.Kernel.Env .anon} {rlps : List LevelParam}
    {nP nF o i l : Nat} {pw : Ix.Kernel.PropWhen} {tele : List (KExpr × Ix.Kernel.BinderMeta)}
    {body : KExpr}
    (hpw : pw.paramsDefined rlps = true) (hi : i < nF)
    (htele : ∀ k < tele.length, GenScoped env rlps (nP + i + k) (tele.getD k default).1)
    (hbo : GenScoped env rlps (nP + o + nF + l + tele.length) body) :
    GenScoped env rlps (nP + o + nF + l)
      (Ix.Kernel.Expr.mkLamsOf (Ix.Kernel.structTeleAt nF o i l pw tele) body) := by
  unfold Ix.Kernel.structTeleAt
  suffices hgo : ∀ (s : Nat) (rem : List Nat),
      s + rem.length = tele.length →
      rem = (List.range rem.length).map (s + ·) →
      GenScoped env rlps (nP + o + nF + l + s)
        (Ix.Kernel.Expr.mkLamsOf
          (rem.map fun k => (Ix.Kernel.structIdxAt nF o i l k (tele.getD k default).1, { pw }))
          body) by
    have h0 := hgo 0 (List.range tele.length) (by simp) (by simp)
    simpa [Nat.add_zero] using h0
  intro s rem
  induction rem generalizing s with
  | nil =>
    intro hsum _
    have hs_eq : s = tele.length := by simpa using hsum
    subst hs_eq
    simpa [Ix.Kernel.Expr.mkLamsOf] using hbo
  | cons k ks ih =>
    intro hsum hrem
    have hk_eq : k = s := by
      have := congrArg List.head? hrem
      simp [List.range_succ_eq_map] at this
      exact this
    subst hk_eq
    have hks : ks = (List.range ks.length).map ((k + 1) + ·) := by
      simp only [List.length_cons] at hrem
      rw [List.range_succ_eq_map, List.map_cons, List.map_map] at hrem
      injection hrem with _ htl
      rw [htl]
      simp only [List.length_map, List.length_range]
      apply List.map_congr_left; intro x _; omega
    simp only [List.map_cons, Ix.Kernel.Expr.mkLamsOf]
    refine GenScoped.lam hpw (GenScoped.structIdxAt hi (htele k (by simp at hsum; omega))) ?_
    exact ih (k + 1) (by simp at hsum; omega) hks

theorem GenScoped.structIhPis {env : Ix.Kernel.Env .anon} {rlps : List LevelParam}
    {nP nF o : Nat} {pw : Ix.Kernel.PropWhen}
    {teleOf : Nat → List (KExpr × Ix.Kernel.BinderMeta)}
    {idxOf : Nat → List KExpr}
    (ho : 1 ≤ o) (hpw : pw.paramsDefined rlps = true) :
    ∀ {is : List Nat} {l : Nat} {body : KExpr},
      (∀ i ∈ is, i < nF ∧
        (∀ k < (teleOf i).length, GenScoped env rlps (nP + i + k) ((teleOf i).getD k default).1) ∧
        (∀ e ∈ idxOf i, GenScoped env rlps (nP + i + (teleOf i).length) e)) →
      GenScoped env rlps (nP + o + nF + l + is.length) body →
      GenScoped env rlps (nP + o + nF + l)
        (Ix.Kernel.structIhPis nF o pw teleOf idxOf is l body)
  | [], l, body, _, hbo => by simpa [Ix.Kernel.structIhPis] using hbo
  | i :: is, l, body, his, hbo => by
    obtain ⟨hi, htele, hidx⟩ := his i List.mem_cons_self
    simp only [Ix.Kernel.structIhPis]
    refine GenScoped.forallE hpw ?_ ?_
    · refine GenScoped.mkPisOf_structTeleAt hpw hi htele ?_
      refine GenScoped.mkAppN (GenScoped.bvar (by omega)) ?_
      intro a ha
      simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
      rcases ha with ⟨e, he, rfl⟩ | rfl
      · exact GenScoped.structIdxAt hi (hidx e he)
      · exact GenScoped.mkAppN (GenScoped.bvar (by omega))
          (GenScoped.structTeleVars (by omega))
    · have hbo' : GenScoped env rlps (nP + o + nF + (l + 1) + is.length) body := by
        simp only [List.length_cons] at hbo
        rwa [show nP + o + nF + (l + 1) + is.length = nP + o + nF + l + (is.length + 1) by omega]
      have hrec := GenScoped.structIhPis ho hpw
        (fun j hj => his j (List.mem_cons_of_mem _ hj)) hbo'
      rwa [show nP + o + nF + l + 1 = nP + o + nF + (l + 1) by omega]

theorem GenScoped.structMinorTyR {env : Ix.Kernel.Env .anon} {rlps lps : List LevelParam}
    {C : KKey} {nP nF o : Nat} {pw : Ix.Kernel.PropWhen} {cty mty : KExpr} {recIdx : List Nat}
    (ho : 1 ≤ o) (hpw : pw.paramsDefined rlps = true)
    (hlps_sub : ∀ x ∈ lps, x ∈ rlps)
    (hC_res : (env.find? C).isSome = true)
    (hC_not_defn : ∀ cv v hn, env.find? C ≠ some (.defnInfo cv v hn))
    (hcty : GenScoped env rlps 0 cty)
    (hrec_lt : ∀ i ∈ recIdx, i < nF)
    (hmty : Ix.Kernel.structMinorTyR C lps nP nF o pw cty recIdx = some mty) :
    GenScoped env rlps (nP + o) mty := by
  obtain ⟨cbs, fbs, crest0, res, hs, hr, hm⟩ := Ix.Kernel.structMinorTyR_unfold hmty
  have hsAll : cty.stripPis (nP + nF) = some (cbs ++ fbs, res) :=
    stripPis_add nP nF hs hr
  obtain ⟨_, hdomsP, hcrest0⟩ := GenScoped.stripPis nP hs hcty
  rw [Nat.zero_add] at hcrest0
  obtain ⟨_, _, hres⟩ := GenScoped.stripPis nF hr hcrest0
  obtain ⟨hcbs_len, hdomsAll, _⟩ := GenScoped.stripPis (nP + nF) hsAll hcty
  have htele_idx : ∀ i ∈ recIdx, i < nF ∧
      (∀ k < (Ix.Kernel.structFieldTeleOf cty nP nF i).length,
        GenScoped env rlps (nP + i + k) ((Ix.Kernel.structFieldTeleOf cty nP nF i).getD k default).1) ∧
      (∀ e ∈ Ix.Kernel.structFieldIdxOf cty nP nF i,
        GenScoped env rlps (nP + i + (Ix.Kernel.structFieldTeleOf cty nP nF i).length) e) := by
    intro i hi_mem
    have hi : i < nF := hrec_lt i hi_mem
    have hdom_i : GenScoped env rlps (nP + i) ((cbs ++ fbs).getD (nP + i) default).1 := by
      have h0 := hdomsAll (nP + i) (by omega)
      rwa [Nat.zero_add] at h0
    obtain ⟨hpb_doms, hpb_last⟩ := GenScoped.piBinders hdom_i
    refine ⟨hi, ?_, ?_⟩
    · intro k hk
      unfold Ix.Kernel.structFieldTeleOf at hk ⊢
      rw [hsAll] at hk ⊢
      exact hpb_doms k hk
    · intro e he
      unfold Ix.Kernel.structFieldIdxOf at he
      unfold Ix.Kernel.structFieldTeleOf
      rw [hsAll] at he ⊢
      exact GenScoped.getAppArgs hpb_last e (List.mem_of_mem_drop he)
  refine GenScoped.replacePisPw nF hpw hm (GenScoped.liftLooseBVars o hcrest0) ?_
  have hconcl : GenScoped env rlps (nP + o + nF)
      (Expr.mkAppN (.bvar (nF + o - 1))
        ((res.getAppArgs.drop nP).map (Expr.liftLooseBVars o nF) ++
          [Ix.Kernel.structCtorSpineAt C lps o nP nF])) := by
    refine GenScoped.mkAppN (GenScoped.bvar (by omega)) ?_
    intro a ha
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
    rcases ha with ⟨e, he, rfl⟩ | rfl
    · have he_sc := GenScoped.getAppArgs hres e (List.mem_of_mem_drop he)
      have hl := GenScoped.liftLooseBVars o (c := nF) he_sc
      rwa [show nP + nF + o = nP + o + nF by omega] at hl
    · unfold Ix.Kernel.structCtorSpineAt
      refine GenScoped.mkAppN
        (GenScoped.const_nonDefn hC_res hC_not_defn (fun u hu => by
          simp only [List.mem_map] at hu
          obtain ⟨p, hp, rfl⟩ := hu
          simp [Level.allParamsDefined, List.contains_iff_mem, hlps_sub p hp])) ?_
      intro x hx
      simp only [List.mem_append, List.mem_map, List.mem_range] at hx
      rcases hx with hx | ⟨j, hj, rfl⟩
      · exact GenScoped.structPsAt (by omega) x hx
      · exact GenScoped.bvar (by omega)
  have hconcl_lift := GenScoped.liftLooseBVars recIdx.length (c := 0) hconcl
  rw [show nP + o + nF + recIdx.length = nP + o + nF + 0 + recIdx.length by omega] at hconcl_lift
  have hih := GenScoped.structIhPis ho hpw htele_idx hconcl_lift
  rwa [Nat.add_zero] at hih

theorem GenScoped.structMinorsPisR {env : Ix.Kernel.Env .anon} {rlps lps : List LevelParam}
    {nP : Nat} {pw : Ix.Kernel.PropWhen}
    (hpw : pw.paramsDefined rlps = true)
    (hlps_sub : ∀ x ∈ lps, x ∈ rlps) :
    ∀ {ctors : List (KKey × Nat × KExpr × List Nat)} {o : Nat} {body mins : KExpr},
      1 ≤ o →
      Ix.Kernel.structMinorsPisR lps nP pw ctors o body = some mins →
      (∀ c ∈ ctors, (env.find? c.1).isSome = true ∧
        (∀ cv v hn, env.find? c.1 ≠ some (.defnInfo cv v hn)) ∧
        GenScoped env rlps 0 c.2.2.1 ∧
        (∀ i ∈ c.2.2.2, i < c.2.1)) →
      GenScoped env rlps (nP + o + ctors.length) body →
      GenScoped env rlps (nP + o) mins
  | [], o, body, mins, _, hm, _, hbo => by
    rw [Ix.Kernel.structMinorsPisR_nil hm]
    simpa using hbo
  | (C, nF, cty, recIdx) :: cs, o, body, mins, ho, hm, hcs, hbo => by
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := Ix.Kernel.structMinorsPisR_cons hm
    obtain ⟨hCres, hCnd, hcty, hrec_lt⟩ := hcs (C, nF, cty, recIdx) List.mem_cons_self
    have hbo' : GenScoped env rlps (nP + (o + 1) + cs.length) body := by
      simp only [List.length_cons] at hbo
      rwa [show nP + (o + 1) + cs.length = nP + o + (cs.length + 1) by omega]
    refine GenScoped.forallE hpw
      (GenScoped.structMinorTyR ho hpw hlps_sub hCres hCnd hcty hrec_lt hmty)
      (by
        have h := GenScoped.structMinorsPisR hpw hlps_sub (by omega) hrest
          (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hbo'
        rwa [show nP + o + 1 = nP + (o + 1) by omega])

theorem GenScoped.structMinorsLamsR {env : Ix.Kernel.Env .anon} {rlps lps : List LevelParam}
    {nP : Nat} {pw : Ix.Kernel.PropWhen}
    (hpw : pw.paramsDefined rlps = true)
    (hlps_sub : ∀ x ∈ lps, x ∈ rlps) :
    ∀ {ctors : List (KKey × Nat × KExpr × List Nat)} {o : Nat} {body mins : KExpr},
      1 ≤ o →
      Ix.Kernel.structMinorsLamsR lps nP pw ctors o body = some mins →
      (∀ c ∈ ctors, (env.find? c.1).isSome = true ∧
        (∀ cv v hn, env.find? c.1 ≠ some (.defnInfo cv v hn)) ∧
        GenScoped env rlps 0 c.2.2.1 ∧
        (∀ i ∈ c.2.2.2, i < c.2.1)) →
      GenScoped env rlps (nP + o + ctors.length) body →
      GenScoped env rlps (nP + o) mins
  | [], o, body, mins, _, hm, _, hbo => by
    rw [Ix.Kernel.structMinorsLamsR_nil hm]
    simpa using hbo
  | (C, nF, cty, recIdx) :: cs, o, body, mins, ho, hm, hcs, hbo => by
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := Ix.Kernel.structMinorsLamsR_cons hm
    obtain ⟨hCres, hCnd, hcty, hrec_lt⟩ := hcs (C, nF, cty, recIdx) List.mem_cons_self
    have hbo' : GenScoped env rlps (nP + (o + 1) + cs.length) body := by
      simp only [List.length_cons] at hbo
      rwa [show nP + (o + 1) + cs.length = nP + o + (cs.length + 1) by omega]
    refine GenScoped.lam hpw
      (GenScoped.structMinorTyR ho hpw hlps_sub hCres hCnd hcty hrec_lt hmty)
      (by
        have h := GenScoped.structMinorsLamsR hpw hlps_sub (by omega) hrest
          (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hbo'
        rwa [show nP + o + 1 = nP + (o + 1) by omega])

theorem GenScoped.structFamI {env : Ix.Kernel.Env .anon} {rlps lps : List LevelParam}
    {T : KKey} {nP nIdx e o b : Nat}
    (hb : o + e + nIdx + nP ≤ b)
    (hlps_sub : ∀ x ∈ lps, x ∈ rlps)
    (hT_res : (env.find? T).isSome = true)
    (hT_not_defn : ∀ cv v hn, env.find? T ≠ some (.defnInfo cv v hn)) :
    GenScoped env rlps b (Ix.Kernel.structFamI T lps nP nIdx e o) := by
  unfold Ix.Kernel.structFamI
  refine GenScoped.mkAppN
    (GenScoped.const_nonDefn hT_res hT_not_defn (fun u hu => by
      simp only [List.mem_map] at hu
      obtain ⟨p, hp, rfl⟩ := hu
      simp [Level.allParamsDefined, List.contains_iff_mem, hlps_sub p hp])) ?_
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact GenScoped.structPsAt (by omega) a ha
  · exact GenScoped.structPsAt (by omega) a ha

theorem GenScoped.structRecTyR {env : Ix.Kernel.Env .anon} {rlps lps : List LevelParam}
    {T : KKey} {elim : LevelParam} {large : Bool} {nP nIdx : Nat}
    {tty recTy : KExpr} {ctors : List (KKey × Nat × KExpr × List Nat)}
    (hlps_sub : ∀ x ∈ lps, x ∈ rlps)
    (helim : large = true → elim ∈ rlps)
    (hT_res : (env.find? T).isSome = true)
    (hT_not_defn : ∀ cv v hn, env.find? T ≠ some (.defnInfo cv v hn))
    (htty : GenScoped env rlps 0 tty)
    (hcs : ∀ c ∈ ctors, (env.find? c.1).isSome = true ∧
      (∀ cv v hn, env.find? c.1 ≠ some (.defnInfo cv v hn)) ∧
      GenScoped env rlps 0 c.2.2.1 ∧
      (∀ i ∈ c.2.2.2, i < c.2.1))
    (hrec : Ix.Kernel.structRecTyR T lps elim large nP nIdx tty ctors = some recTy) :
    GenScoped env rlps 0 recTy := by
  obtain ⟨tbs, itele, motiveTy, major, minors, hq, hmot, hmaj, hmin, hr⟩ :=
    Ix.Kernel.structRecTyR_unfold hrec
  have hℓ : (Ix.Kernel.structElimLevel elim large).allParamsDefined rlps = true := by
    cases large with
    | false => rfl
    | true => simp [Ix.Kernel.structElimLevel, Level.allParamsDefined, List.contains_iff_mem, helim rfl]
  have hpw : (Level.zeronessOf (Ix.Kernel.structElimLevel elim large)).paramsDefined rlps = true :=
    Level.zeronessOf_paramsDefined hℓ
  have hnever : Ix.Kernel.PropWhen.never.paramsDefined rlps = true :=
    Ix.Kernel.PropWhen.paramsDefined_never rlps
  obtain ⟨_, _, hitele⟩ := GenScoped.stripPis nP hq htty
  rw [Nat.zero_add] at hitele
  have hmotive : GenScoped env rlps nP motiveTy := by
    unfold Ix.Kernel.structMotiveTyI at hmot
    refine GenScoped.replacePisPw nIdx hnever hmot hitele ?_
    exact GenScoped.forallE hnever
      (GenScoped.structFamI (by omega) hlps_sub hT_res hT_not_defn)
      (GenScoped.sort hℓ)
  have hmajor : GenScoped env rlps (nP + 1 + ctors.length) major := by
    have hitele_lift := GenScoped.liftLooseBVars (ctors.length + 1) (c := 0) hitele
    rw [show nP + (ctors.length + 1) = nP + 1 + ctors.length by omega] at hitele_lift
    refine GenScoped.replacePisPw nIdx hpw hmaj hitele_lift ?_
    refine GenScoped.forallE hpw
      (GenScoped.structFamI (by omega) hlps_sub hT_res hT_not_defn) ?_
    refine GenScoped.mkAppN (GenScoped.bvar (by omega)) ?_
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact GenScoped.structPsAt (by omega) a ha
    · exact GenScoped.bvar (by omega)
  have hminors := GenScoped.structMinorsPisR hpw hlps_sub (by omega) hmin hcs hmajor
  exact GenScoped.replacePisPw nP hpw hr htty
    (by rw [Nat.zero_add]; exact GenScoped.forallE hpw hmotive hminors)

theorem GenScoped.structRecRhsR {envR : Ix.Kernel.Env .anon} {rlps lps : List LevelParam}
    {T recC : KKey} {elim : LevelParam} {large : Bool} {nP nIdx j : Nat}
    {tty rhs : KExpr} {ctors : List (KKey × Nat × KExpr × List Nat)}
    (hlps_sub : ∀ x ∈ lps, x ∈ rlps)
    (helim : large = true → elim ∈ rlps)
    (hT_res : (envR.find? T).isSome = true)
    (hT_not_defn : ∀ cv v hn, envR.find? T ≠ some (.defnInfo cv v hn))
    (hR_res : (envR.find? recC).isSome = true)
    (hR_not_defn : ∀ cv v hn, envR.find? recC ≠ some (.defnInfo cv v hn))
    (htty : GenScoped envR rlps 0 tty)
    (hcs : ∀ c ∈ ctors, (envR.find? c.1).isSome = true ∧
      (∀ cv v hn, envR.find? c.1 ≠ some (.defnInfo cv v hn)) ∧
      GenScoped envR rlps 0 c.2.2.1 ∧
      (∀ i ∈ c.2.2.2, i < c.2.1) ∧
      ∃ cbs cbody, c.2.2.1.stripPis (nP + c.2.1) = some (cbs, cbody))
    (hj_lt : j < ctors.length)
    (hrhs : Ix.Kernel.structRecRhsR T lps elim large nP nIdx tty ctors recC
      (rlps.map .param) j = some rhs) :
    GenScoped envR rlps 0 rhs := by
  obtain ⟨C, nF, cty, recIdx, tbs, cbs, itele, motiveTy, crest0, inner, minors,
    hcj, htq, hmot, hq, hinner, hminors, hr⟩ := Ix.Kernel.structRecRhsR_unfold hrhs
  obtain ⟨_, _, hcty, hrec_lt, cbsAll, cbodyAll, hsAll⟩ :=
    hcs (C, nF, cty, recIdx) (List.mem_of_getElem? hcj)
  have hℓ : (Ix.Kernel.structElimLevel elim large).allParamsDefined rlps = true := by
    cases large with
    | false => rfl
    | true => simp [Ix.Kernel.structElimLevel, Level.allParamsDefined, List.contains_iff_mem, helim rfl]
  have hpw : (Level.zeronessOf (Ix.Kernel.structElimLevel elim large)).paramsDefined rlps = true :=
    Level.zeronessOf_paramsDefined hℓ
  have hnever : Ix.Kernel.PropWhen.never.paramsDefined rlps = true :=
    Ix.Kernel.PropWhen.paramsDefined_never rlps
  obtain ⟨_, _, hitele⟩ := GenScoped.stripPis nP htq htty
  rw [Nat.zero_add] at hitele
  have hmotive : GenScoped envR rlps nP motiveTy := by
    unfold Ix.Kernel.structMotiveTyI at hmot
    refine GenScoped.replacePisPw nIdx hnever hmot hitele ?_
    exact GenScoped.forallE hnever
      (GenScoped.structFamI (by omega) hlps_sub hT_res hT_not_defn)
      (GenScoped.sort hℓ)
  obtain ⟨_, _, hcrest0⟩ := GenScoped.stripPis nP hq hcty
  rw [Nat.zero_add] at hcrest0
  obtain ⟨_, hdomsAll, _⟩ := GenScoped.stripPis (nP + nF) hsAll hcty
  have hinner_sc : GenScoped envR rlps (nP + 1 + ctors.length) inner := by
    have hcrest_lift := GenScoped.liftLooseBVars (ctors.length + 1) (c := 0) hcrest0
    rw [show nP + (ctors.length + 1) = nP + 1 + ctors.length by omega] at hcrest_lift
    refine GenScoped.pisToLamsPw nF hpw hinner hcrest_lift ?_
    unfold Ix.Kernel.structRuleBodyR
    refine GenScoped.mkAppN (GenScoped.bvar (by omega)) ?_
    intro a ha
    simp only [List.mem_append, List.mem_map, List.mem_range] at ha
    rcases ha with ⟨k, hk, rfl⟩ | ⟨i, hi_mem, rfl⟩
    · exact GenScoped.bvar (by omega)
    · have hi : i < nF := hrec_lt i hi_mem
      have hdom_i : GenScoped envR rlps (nP + i) (cbsAll.getD (nP + i) default).1 := by
        have h0 := hdomsAll (nP + i) (by omega)
        rwa [Nat.zero_add] at h0
      obtain ⟨hpb_doms, hpb_last⟩ := GenScoped.piBinders hdom_i
      let tele_i := Ix.Kernel.structFieldTeleOf cty nP nF i
      have htele_sc : ∀ k < tele_i.length,
          GenScoped envR rlps (nP + i + k) (tele_i.getD k default).1 := by
        intro k hk
        dsimp only [tele_i] at hk ⊢
        unfold Ix.Kernel.structFieldTeleOf at hk ⊢
        rw [hsAll] at hk ⊢
        exact hpb_doms k hk
      unfold Ix.Kernel.structIhApp
      have happ_body : GenScoped envR rlps (nP + (ctors.length + 1) + nF + 0 + tele_i.length)
          (Expr.mkAppN (.const recC (rlvls.map .param))
            (Ix.Kernel.structRecPrefixAt nP ctors.length nF tele_i.length ++
              (Ix.Kernel.structFieldIdxOf cty nP nF i).map
                (Ix.Kernel.structIdxAt nF (ctors.length + 1) i 0 tele_i.length) ++
              [Expr.mkAppN (.bvar (nF - 1 - i + tele_i.length))
                (Ix.Kernel.structTeleVars tele_i.length)])) := by
        refine GenScoped.mkAppN
          (GenScoped.const_nonDefn hR_res hR_not_defn (fun u hu => by
            simp only [List.mem_map] at hu
            obtain ⟨p, hp, rfl⟩ := hu
            simp [Level.allParamsDefined, List.contains_iff_mem, hp])) ?_
        intro x hx
        simp only [List.mem_append, List.mem_singleton, List.mem_map] at hx
        rcases hx with (hx | ⟨e, he, rfl⟩) | rfl
        · unfold Ix.Kernel.structRecPrefixAt at hx
          simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_range] at hx
          rcases hx with (hx | rfl) | ⟨l, hl, rfl⟩
          · exact GenScoped.structPsAt (by omega) x hx
          · exact GenScoped.bvar (by omega)
          · exact GenScoped.bvar (by omega)
        · unfold Ix.Kernel.structFieldIdxOf at he
          dsimp only [tele_i]
          unfold Ix.Kernel.structFieldTeleOf
          rw [hsAll] at he ⊢
          exact GenScoped.structIdxAt hi
            (GenScoped.getAppArgs hpb_last e (List.mem_of_mem_drop he))
        · exact GenScoped.mkAppN (GenScoped.bvar (by omega))
            (GenScoped.structTeleVars (by omega))
      have happ_lam := GenScoped.mkLamsOf_structTeleAt
        (o := ctors.length + 1) (l := 0) (tele := tele_i) hpw hi htele_sc happ_body
      rwa [show nP + (ctors.length + 1) + nF + 0 = nP + 1 + ctors.length + nF by omega] at happ_lam
  have hcs' : ∀ c ∈ ctors, (envR.find? c.1).isSome = true ∧
      (∀ cv v hn, envR.find? c.1 ≠ some (.defnInfo cv v hn)) ∧
      GenScoped envR rlps 0 c.2.2.1 ∧
      (∀ i ∈ c.2.2.2, i < c.2.1) :=
    fun c hc =>
      let q := hcs c hc
      ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1⟩
  have hmin_sc := GenScoped.structMinorsLamsR hpw hlps_sub (by omega) hminors hcs' hinner_sc
  exact GenScoped.pisToLamsPw nP hpw hr htty
    (by rw [Nat.zero_add]; exact GenScoped.lam hpw hmotive hmin_sc)

/-! ### Existence of `replacePisPw` / `pisToLamsPw` / `structRecTyR` / `structRecRhsR` -/

theorem replacePisPw_of_stripPis (pw : Ix.Kernel.PropWhen) :
    ∀ (k : Nat) {tele rest : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} (b : KExpr),
      tele.stripPis k = some (bs, rest) →
      ∃ r, Expr.replacePisPw pw k tele b = some r
  | 0, _, _, _, b, _ => ⟨b, rfl⟩
  | k + 1, .forallE ty bo m, rest, bs, b, hs => by
    rw [Expr.stripPis, Option.map_eq_some_iff] at hs
    obtain ⟨⟨bs', rest'⟩, hbo, _⟩ := hs
    obtain ⟨r', hr'⟩ := replacePisPw_of_stripPis pw k b hbo
    exact ⟨.forallE ty r' { pw }, by simp [Expr.replacePisPw, hr']⟩
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, hs | _ + 1, .sort _, _, _, _, hs
  | _ + 1, .const _ _, _, _, _, hs | _ + 1, .app _ _, _, _, _, hs | _ + 1, .lam _ _ _, _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, _, hs | _ + 1, .lit _, _, _, _, hs | _ + 1, .proj _ _ _, _, _, _, hs =>
    nomatch hs

theorem pisToLamsPw_of_stripPis (pw : Ix.Kernel.PropWhen) :
    ∀ (k : Nat) {tele rest : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} (b : KExpr),
      tele.stripPis k = some (bs, rest) →
      ∃ r, Expr.pisToLamsPw pw k tele b = some r
  | 0, _, _, _, b, _ => ⟨b, rfl⟩
  | k + 1, .forallE ty bo m, rest, bs, b, hs => by
    rw [Expr.stripPis, Option.map_eq_some_iff] at hs
    obtain ⟨⟨bs', rest'⟩, hbo, _⟩ := hs
    obtain ⟨r', hr'⟩ := pisToLamsPw_of_stripPis pw k b hbo
    exact ⟨.lam ty r' { pw }, by simp [Expr.pisToLamsPw, hr']⟩
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, hs | _ + 1, .sort _, _, _, _, hs
  | _ + 1, .const _ _, _, _, _, hs | _ + 1, .app _ _, _, _, _, hs | _ + 1, .lam _ _ _, _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, _, hs | _ + 1, .lit _, _, _, _, hs | _ + 1, .proj _ _ _, _, _, _, hs =>
    nomatch hs

theorem stripPis_liftLooseBVars (s : Nat) :
    ∀ (k : Nat) {e rest : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} (c : Nat),
      e.stripPis k = some (bs, rest) →
      ∃ bs', (e.liftLooseBVars s c).stripPis k = some (bs', rest.liftLooseBVars s (c + k))
  | 0, e, rest, bs, c, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨_, rfl⟩ := hs
    exact ⟨[], by simp [Expr.stripPis]⟩
  | k + 1, .forallE ty bo m, rest, bs, c, hs => by
    rw [Expr.stripPis, Option.map_eq_some_iff] at hs
    obtain ⟨⟨bs₀, rest₀⟩, hbo, hpair⟩ := hs
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨_, rfl⟩ := hpair
    obtain ⟨bs', hbo'⟩ := stripPis_liftLooseBVars s k (c + 1) hbo
    refine ⟨(ty.liftLooseBVars s c, m) :: bs', ?_⟩
    rw [show c + (k + 1) = c + 1 + k by omega]
    simp [Expr.liftLooseBVars, Expr.stripPis, hbo']
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, hs | _ + 1, .sort _, _, _, _, hs
  | _ + 1, .const _ _, _, _, _, hs | _ + 1, .app _ _, _, _, _, hs | _ + 1, .lam _ _ _, _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, _, hs | _ + 1, .lit _, _, _, _, hs | _ + 1, .proj _ _ _, _, _, _, hs =>
    nomatch hs

theorem structMinorTyR_exists (C : KKey) (lps : List LevelParam) (nP nF o : Nat)
    (pw : Ix.Kernel.PropWhen) (cty : KExpr) (recIdx : List Nat)
    (hs : ∃ cbs cbody, cty.stripPis (nP + nF) = some (cbs, cbody)) :
    ∃ mty, Ix.Kernel.structMinorTyR C lps nP nF o pw cty recIdx = some mty := by
  obtain ⟨cbs, cbody, hsAll⟩ := hs
  obtain ⟨cbs₁, crest0, cbs₂, hsP, hsF, _, _⟩ := stripPis_split nP nF hsAll
  obtain ⟨fbs', hsF_lift⟩ := stripPis_liftLooseBVars o nF 0 hsF
  obtain ⟨mty, hmty⟩ := replacePisPw_of_stripPis pw nF
    (Ix.Kernel.structIhPis nF o pw (Ix.Kernel.structFieldTeleOf cty nP nF)
      (Ix.Kernel.structFieldIdxOf cty nP nF) recIdx 0
      ((Expr.mkAppN (.bvar (nF + o - 1))
        ((cbody.getAppArgs.drop nP).map (Expr.liftLooseBVars o nF) ++
          [Ix.Kernel.structCtorSpineAt C lps o nP nF])).liftLooseBVars recIdx.length 0))
    hsF_lift
  exact ⟨mty, by
    unfold Ix.Kernel.structMinorTyR
    rw [hsP, Option.bind_some, hsF, Option.bind_some]
    exact hmty⟩

theorem structMinorsPisR_exists (lps : List LevelParam) (nP : Nat) (pw : Ix.Kernel.PropWhen) :
    ∀ (ctors : List (KKey × Nat × KExpr × List Nat)) (o : Nat) (body : KExpr),
      (∀ c ∈ ctors, ∃ cbs cbody, c.2.2.1.stripPis (nP + c.2.1) = some (cbs, cbody)) →
      ∃ mins, Ix.Kernel.structMinorsPisR lps nP pw ctors o body = some mins
  | [], _, body, _ => ⟨body, rfl⟩
  | (C, nF, cty, recIdx) :: cs, o, body, hcs => by
    obtain ⟨mty, hmty⟩ := structMinorTyR_exists C lps nP nF o pw cty recIdx
      (hcs (C, nF, cty, recIdx) List.mem_cons_self)
    obtain ⟨rest, hrest⟩ := structMinorsPisR_exists lps nP pw cs (o + 1) body
      (fun c hc => hcs c (List.mem_cons_of_mem _ hc))
    exact ⟨.forallE mty rest { pw }, by simp [Ix.Kernel.structMinorsPisR, hmty, hrest]⟩

theorem structMinorsLamsR_exists (lps : List LevelParam) (nP : Nat) (pw : Ix.Kernel.PropWhen) :
    ∀ (ctors : List (KKey × Nat × KExpr × List Nat)) (o : Nat) (body : KExpr),
      (∀ c ∈ ctors, ∃ cbs cbody, c.2.2.1.stripPis (nP + c.2.1) = some (cbs, cbody)) →
      ∃ mins, Ix.Kernel.structMinorsLamsR lps nP pw ctors o body = some mins
  | [], _, body, _ => ⟨body, rfl⟩
  | (C, nF, cty, recIdx) :: cs, o, body, hcs => by
    obtain ⟨mty, hmty⟩ := structMinorTyR_exists C lps nP nF o pw cty recIdx
      (hcs (C, nF, cty, recIdx) List.mem_cons_self)
    obtain ⟨rest, hrest⟩ := structMinorsLamsR_exists lps nP pw cs (o + 1) body
      (fun c hc => hcs c (List.mem_cons_of_mem _ hc))
    exact ⟨.lam mty rest { pw }, by simp [Ix.Kernel.structMinorsLamsR, hmty, hrest]⟩

theorem structRecTyR_exists (T : KKey) (lps : List LevelParam) (elim : LevelParam) (large : Bool)
    (nP nIdx : Nat) (tty : KExpr) (ctors : List (KKey × Nat × KExpr × List Nat))
    (htty : ∃ tbs tsort, tty.stripPis (nP + nIdx) = some (tbs, tsort))
    (hcs : ∀ c ∈ ctors, ∃ cbs cbody, c.2.2.1.stripPis (nP + c.2.1) = some (cbs, cbody)) :
    ∃ recTy, Ix.Kernel.structRecTyR T lps elim large nP nIdx tty ctors = some recTy := by
  obtain ⟨tbs, tsort, hsT⟩ := htty
  obtain ⟨tbsP, itele, tbsI, hsTP, hsTI, _, _⟩ := stripPis_split nP nIdx hsT
  let ℓ := Ix.Kernel.structElimLevel elim large
  let pw := Level.zeronessOf ℓ
  obtain ⟨motiveTy, hmot⟩ := replacePisPw_of_stripPis .never nIdx
    (.forallE (Ix.Kernel.structFamI T lps nP nIdx 0 0) (.sort ℓ) { pw := .never }) hsTI
  obtain ⟨ibs', hsTI_lift⟩ := stripPis_liftLooseBVars (ctors.length + 1) nIdx 0 hsTI
  obtain ⟨major, hmaj⟩ := replacePisPw_of_stripPis pw nIdx
    (.forallE (Ix.Kernel.structFamI T lps nP nIdx (ctors.length + 1) 0)
      (Expr.mkAppN (.bvar (nIdx + ctors.length + 1))
        (Ix.Kernel.structPsAt 1 nIdx ++ [.bvar 0])) { pw })
    hsTI_lift
  obtain ⟨minors, hmin⟩ := structMinorsPisR_exists lps nP pw ctors 1 major hcs
  obtain ⟨recTy, hrec⟩ := replacePisPw_of_stripPis pw nP
    (.forallE motiveTy minors { pw }) hsTP
  exact ⟨recTy, by
    unfold Ix.Kernel.structRecTyR Ix.Kernel.structMotiveTyI
    dsimp only [ℓ, pw] at *
    rw [hsTP, Option.bind_some, hmot, Option.bind_some, hmaj, Option.bind_some, hmin,
      Option.bind_some]
    exact hrec⟩

theorem structRecRhsR_exists (T : KKey) (lps : List LevelParam) (elim : LevelParam) (large : Bool)
    (nP nIdx : Nat) (tty : KExpr) (ctors : List (KKey × Nat × KExpr × List Nat))
    (recC : KKey) (rlvls : List KLevel) (j : Nat)
    (hj : j < ctors.length)
    (htty : ∃ tbs tsort, tty.stripPis (nP + nIdx) = some (tbs, tsort))
    (hcs : ∀ c ∈ ctors, ∃ cbs cbody, c.2.2.1.stripPis (nP + c.2.1) = some (cbs, cbody)) :
    ∃ rhs, Ix.Kernel.structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j = some rhs := by
  obtain ⟨c, hcj⟩ : ∃ c, ctors[j]? = some c :=
    ⟨ctors[j]'hj, List.getElem?_eq_getElem hj⟩
  obtain ⟨C, nF, cty, recIdx⟩ := c
  obtain ⟨tbs, tsort, hsT⟩ := htty
  obtain ⟨tbsP, itele, tbsI, hsTP, hsTI, _, _⟩ := stripPis_split nP nIdx hsT
  let ℓ := Ix.Kernel.structElimLevel elim large
  let pw := Level.zeronessOf ℓ
  obtain ⟨motiveTy, hmot⟩ := replacePisPw_of_stripPis .never nIdx
    (.forallE (Ix.Kernel.structFamI T lps nP nIdx 0 0) (.sort ℓ) { pw := .never }) hsTI
  obtain ⟨cbs, cbody, hsC⟩ := hcs (C, nF, cty, recIdx) (List.mem_of_getElem? hcj)
  obtain ⟨cbsP, crest0, cbsF, hsCP, hsCF, _, _⟩ := stripPis_split nP nF hsC
  obtain ⟨fbs', hsCF_lift⟩ := stripPis_liftLooseBVars (ctors.length + 1) nF 0 hsCF
  obtain ⟨inner, hinner⟩ := pisToLamsPw_of_stripPis pw nF
    (Ix.Kernel.structRuleBodyR recC rlvls pw nP ctors.length nF j recIdx
      (Ix.Kernel.structFieldTeleOf cty nP nF) (Ix.Kernel.structFieldIdxOf cty nP nF))
    hsCF_lift
  obtain ⟨minors, hmin⟩ := structMinorsLamsR_exists lps nP pw ctors 1 inner hcs
  obtain ⟨rhs, hrhs⟩ := pisToLamsPw_of_stripPis pw nP
    (.lam motiveTy minors { pw }) hsTP
  exact ⟨rhs, by
    unfold Ix.Kernel.structRecRhsR Ix.Kernel.structMotiveTyI
    dsimp only [ℓ, pw] at *
    rw [hcj]
    dsimp only
    rw [hsTP, Option.bind_some, hmot, Option.bind_some, hsCP, Option.bind_some, hinner,
      Option.bind_some, hmin, Option.bind_some]
    exact hrhs⟩

/-! ## Section 5a: `RawTm` and Native Recursor Generator Circuit Specifications -/

theorem tm_bvarLocal_nat {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k addr n : Nat}
    (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field (n : F)]))
    (hsm : n < 4294967296) (hlt : n < k) :
    Tm κ d Γ h k (.bvar n) (.ptr (.enum kexprEnum) addr) := by
  have hval : ZMod.val (n : F) = n :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hsm (by decide))
  rw [← hval]
  exact .bvarLocal cell (by rw [hval]; exact Nat.lt_trans hsm (by decide)) (by rw [hval]; exact hlt)

/-- Dual raw + ζ-reduced heap representation with semantic level equivalence (`LvEq` / `LvEqList`),
preserving raw `.letE` nodes on `R` so `collect_spine` and `nat_pi_binders` see the exact raw
application / binder structure even after `expr_inst_levels`. -/
inductive RawTm (κ : _root_.Address → KKey) (d : Nat) (Γ : Nat → KExpr) (h : Heap F) :
    Nat → KExpr → KExpr → SourceValue F → Prop where
  | bvarLocal {k addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i]))
      (hsmall : ZMod.val i < 9223372036854775808) (hi : ZMod.val i < k) :
      RawTm κ d Γ h k (.bvar (ZMod.val i)) (.bvar (ZMod.val i)) (.ptr (.enum kexprEnum) addr)
  | bvarFree {k addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i]))
      (hsmall : ZMod.val i < 9223372036854775808) (hk : k ≤ ZMod.val i)
      (hd : ZMod.val i - k < d) :
      RawTm κ d Γ h k
        (.fvar (fvIdx d k (ZMod.val i)) (Γ (fvIdx d k (ZMod.val i))))
        (.fvar (fvIdx d k (ZMod.val i)) (Γ (fvIdx d k (ZMod.val i))))
        (.ptr (.enum kexprEnum) addr)
  | sort {k addr : Nat} {lp : SourceValue F} {l u : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Srt" [lp]))
      (rl : RepKLevel h l lp) (eq : LvEq u l) :
      RawTm κ d Γ h k (.sort u) (.sort u) (.ptr (.enum kexprEnum) addr)
  | const {k addr : Nat} {ap lsp : SourceValue F} {a : Bytes.Address} {ls us : List KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Const" [ap, lsp]))
      (ra : Bytes.RepAddressRef addrTy h a ap) (rls : RepKLevelList h ls lsp)
      (eq : LvEqList us ls) :
      RawTm κ d Γ h k (.const (κ (ixAddr a)) us) (.const (κ (ixAddr a)) us)
        (.ptr (.enum kexprEnum) addr)
  | app {k addr : Nat} {Rf Ra Ef Ea : KExpr} {pf pa : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "App" [pf, pa]))
      (rf : RawTm κ d Γ h k Rf Ef pf) (ra : RawTm κ d Γ h k Ra Ea pa) :
      RawTm κ d Γ h k (.app Rf Ra) (.app Ef Ea) (.ptr (.enum kexprEnum) addr)
  | lam {k addr : Nat} {Rt Rb T B : KExpr} {ℓ : KLevel} {mR : Ix.Kernel.BinderMeta}
      {pt pb pm : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Lam" [pt, pb, pm]))
      (rt : RawTm κ d Γ h k Rt T pt) (rb : RawTm κ d Γ h (k + 1) Rb B pb)
      (rl : RepKLevel h ℓ pm) :
      RawTm κ d Γ h k (.lam Rt Rb mR) (.lam T B (bmeta ℓ)) (.ptr (.enum kexprEnum) addr)
  | forallE {k addr : Nat} {Rt Rb T B : KExpr} {ℓ : KLevel} {mR : Ix.Kernel.BinderMeta}
      {pt pb pm : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [pt, pb, pm]))
      (rt : RawTm κ d Γ h k Rt T pt) (rb : RawTm κ d Γ h (k + 1) Rb B pb)
      (rl : RepKLevel h ℓ pm) :
      RawTm κ d Γ h k (.forallE Rt Rb mR) (.forallE T B (bmeta ℓ))
        (.ptr (.enum kexprEnum) addr)
  | letE {k addr : Nat} {Rt Rv Rb T V B : KExpr} {mR : Ix.Kernel.LetMeta}
      {pt pv pb : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Let" [pt, pv, pb]))
      (rt : RawTm κ d Γ h k Rt T pt) (rv : RawTm κ d Γ h k Rv V pv)
      (rb : RawTm κ d Γ h (k + 1) Rb B pb) :
      RawTm κ d Γ h k (.letE Rt Rv Rb mR) (instShift V 0 B)
        (.ptr (.enum kexprEnum) addr)
  | litNat {k addr : Nat} {lp : SourceValue F} {limbs : List UInt64}
      (cell : h[addr]? = some (.construct kexprEnum "Lit"
        [.construct klitEnum "Nat" [lp]]))
      (rl : RepList limbListEnum RepU64 h limbs lp) (hc : limbs.getLast? ≠ some 0) :
      RawTm κ d Γ h k (.lit (.natVal (limbsVal limbs))) (.lit (.natVal (limbsVal limbs)))
        (.ptr (.enum kexprEnum) addr)
  | litStr {k addr : Nat} {bp : SourceValue F} {bytes : List UInt8} {s : String}
      (cell : h[addr]? = some (.construct kexprEnum "Lit"
        [.construct klitEnum "Str" [bp]]))
      (rb : Bytes.RepByteStream byteListEnum h bytes bp) (hs : StrBytes s bytes) :
      RawTm κ d Γ h k (.lit (.strVal s)) (.lit (.strVal s)) (.ptr (.enum kexprEnum) addr)
  | proj {k addr : Nat} {ap ep : SourceValue F} {a : Bytes.Address} {i : F} {Re E : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Proj" [ap, .field i, ep]))
      (ra : Bytes.RepAddressRef addrTy h a ap) (re : RawTm κ d Γ h k Re E ep) :
      RawTm κ d Γ h k (.proj (κ (ixAddr a)) (ZMod.val i) Re)
        (.proj (κ (ixAddr a)) (ZMod.val i) E)
        (.ptr (.enum kexprEnum) addr)

theorem RawTmExact.toRawTm {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p) : RawTm κ d Γ h k R E p := by
  induction rep with
  | bvarLocal cell hsm hlt => exact .bvarLocal cell hsm hlt
  | bvarFree cell hsm hge hd => exact .bvarFree cell hsm hge hd
  | sort cell rl => exact .sort cell rl (LvEq.refl _)
  | const cell ra rls => exact .const cell ra rls (LvEqList.refl _)
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

theorem RawTm.toTm {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (rep : RawTm κ d Γ h k R E p) : Tm κ d Γ h k E p := by
  induction rep with
  | bvarLocal cell hsm hlt => exact .bvarLocal cell hsm hlt
  | bvarFree cell hsm hge hd => exact .bvarFree cell hsm hge hd
  | sort cell rl eq => exact .sort cell rl eq
  | const cell ra rls eq => exact .const cell ra rls eq
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

theorem RawTm.mono {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h h' : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (ext : Heap.Extends h h') (rep : RawTm κ d Γ h k R E p) : RawTm κ d Γ h' k R E p := by
  induction rep with
  | bvarLocal cell hsm hlt => exact .bvarLocal (ext.getElem?_eq cell) hsm hlt
  | bvarFree cell hsm hge hd => exact .bvarFree (ext.getElem?_eq cell) hsm hge hd
  | sort cell rl eq => exact .sort (ext.getElem?_eq cell) (repKLevel_heapMono₂ ext rl) eq
  | const cell ra rls eq =>
    exact .const (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra)
      (rls.mono ext) eq
  | app cell _ _ ihf iha => exact .app (ext.getElem?_eq cell) ihf iha
  | lam cell _ _ rl iht ihb =>
    exact .lam (ext.getElem?_eq cell) iht ihb (repKLevel_heapMono₂ ext rl)
  | forallE cell _ _ rl iht ihb =>
    exact .forallE (ext.getElem?_eq cell) iht ihb (repKLevel_heapMono₂ ext rl)
  | letE cell _ _ _ iht ihv ihb => exact .letE (ext.getElem?_eq cell) iht ihv ihb
  | litNat cell rl hc =>
    exact .litNat (ext.getElem?_eq cell)
      (repList_heapMono₂ limbListEnum repU64_heapMono₂ ext rl) hc
  | litStr cell rb hs =>
    exact .litStr (ext.getElem?_eq cell)
      (Bytes.repByteStream_heapMono₂ byteListEnum ext rb) hs
  | proj cell ra _ ihe =>
    exact .proj (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra) ihe

theorem RawTm.load {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p v : SourceValue F}
    (rep : RawTm κ d Γ h k R E p) (ld : loadValue h p = .ok v) :
    ∃ addr, p = .ptr (.enum kexprEnum) addr ∧ h[addr]? = some v := by
  cases rep with
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
  | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _
  | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    rw [loadValue_enum_cell cell] at ld
    injection ld with hv
    exact ⟨_, rfl, by rw [← hv]; exact cell⟩

/-- `KernelLevels::expr_inst_levels` and `expr_inst_levels_walk` preserve `RawTm` at `d = 0`. -/
theorem expr_inst_levels_rawTm_aux (κ : _root_.Address → KKey) :
    ∀ (n : Nat) (isWalk : Bool) {e params r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ n →
      IxVM.Consistency.Bounded cs →
      (if isWalk then ObsFn W "KernelLevels::expr_inst_levels_walk" [e, params] h r h' cs
       else ObsFn W "KernelLevels::expr_inst_levels" [e, params] h r h' cs) →
      ∀ {Γ : Nat → KExpr} {k : Nat} {R E : KExpr} {us : List KLevel},
        RawTm κ 0 Γ h k R E e →
        LvListRep h us params →
        RawTm κ 0 Γ h' k
          (R.instantiateLevelParams (List.range us.length) us)
          (E.instantiateLevelParams (List.range us.length) us) r
  | n, false, e, params, r, h, h', cs, hlen, bd, ev, Γ, k, R, E, us, hRE, hus => by
    match Obs.«KernelLevels::expr_inst_levels».obs ev with
    | .Nil (ld12 := ld) (he21 := hr) (he22 := hh) .. =>
      subst hr hh
      obtain ⟨ls, hls, hul⟩ := hus
      have e' : (Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» : String) =
          KernelLevels.klevelListEnum := klevelListEnum_eq
      rw [e'] at ld
      obtain rfl := RepList.nil_of_load hls ld
      obtain rfl : us = [] := by
        cases us with
        | nil => rfl
        | cons _ _ => exact False.elim (hul (fun _ => 0))
      have hR0 : R.instantiateLevelParams [] [] = R := instantiateLevelParams_self [] R
      rw [List.length_nil, List.range_zero, hR0, SubstAux.tm_ilp_nil hRE.toTm]
      exact hRE
    | .other (ev33 := evw) (hc50 := hc) .. =>
      subst hc
      cases n with
      | zero => simp at hlen
      | succ n' =>
        exact expr_inst_levels_rawTm_aux κ n' true (by simp at hlen; omega)
          (RomBound.bounded_mono bd (fun x hx => List.mem_cons_of_mem _ hx)) evw hRE hus
  | n, true, e, params, r, h, h', cs, hlen, bd, ev, Γ, k, R, E, us, hRE, hus => by
    obtain ⟨ls, hls, hul⟩ := hus
    match Obs.«KernelLevels::expr_inst_levels_walk».obs ev with
    | .BVar (ld12 := ld) (he29 := hr) (hm28 := hm) .. =>
      subst hr hm
      cases hRE with
      | bvarLocal cell hsm hlt =>
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with h1; subst h1
        exact .bvarLocal (by simp) hsm hlt
      | bvarFree _ _ _ hd => omega
      | sort cell _ _ | const cell _ _ _ | app cell _ _ | lam cell _ _ _
      | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
      | proj cell _ _ =>
        exact (load_cell_ne cell ld (by decide)).elim
    | .Srt (ld12 := ld) (ev74 := e1) (he58 := hr) (hm57 := hm) (hc91 := hc) .. =>
      subst hc hr hm
      cases hRE with
      | sort cell rl eq =>
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with h1; subst h1
        obtain ⟨-, rl', -⟩ := IxVM.Refinement.Levels.levelInstParams_obs e1
          (RomBound.bounded_mono bd (fun x hx => List.mem_cons_of_mem _ hx)) rl hls
        exact .sort (by simp) (repKLevel_heapMono₂ (Heap.Extends.snoc _ _) rl')
          (SubstAux.lvEq_subst eq hul)
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | const cell _ _ _ | app cell _ _
      | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
      | litStr cell _ _ | proj cell _ _ =>
        exact (load_cell_ne cell ld (by decide)).elim
    | .Const (ld12 := ld) (ev137 := e1) (he113 := hr) (hm112 := hm) (hc154 := hc) .. =>
      subst hc hr hm
      cases hRE with
      | const cell ra rls eq =>
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with h1 hxs; injection hxs with h2; subst h1 h2
        obtain ⟨-, rls'', ext⟩ := IxVM.Refinement.Levels.levelListInst_obs e1
          (RomBound.bounded_mono bd (fun x hx => List.mem_cons_of_mem _ hx)) rls hls
        have ext_end := ext.trans (Heap.Extends.snoc _ _)
        exact .const (by simp) (Bytes.repAddressRef_heapMono₂ addrTy ext_end ra)
          (rls''.mono (Heap.Extends.snoc _ _))
          (SubstAux.lvEqList_subst eq hul)
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | app cell _ _
      | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
      | litStr cell _ _ | proj cell _ _ =>
        exact (load_cell_ne cell ld (by decide)).elim
    | .App (ld12 := ld) (he176 := hr) (hm175 := hm) (ev193 := e1) (ev221 := e2)
        (hc238 := hc) .. =>
      subst hc hr hm
      cases hRE with
      | app cell rf ra =>
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with h1 hxs; injection hxs with h2; subst h1 h2
        cases n with
        | zero => simp at hlen
        | succ n' =>
          have sf := expr_inst_levels_rawTm_aux κ n' false (by simp at hlen; omega)
            (RomBound.bounded_mono bd (fun x hx => by simp [hx])) e1 rf ⟨ls, hls, hul⟩
          have sa := expr_inst_levels_rawTm_aux κ n' false (by simp at hlen; omega)
            (RomBound.bounded_mono bd (fun x hx => by simp [hx])) e2
            (ra.mono e1.heap_extends) ⟨ls, hls.mono e1.heap_extends, hul⟩
          exact .app (by simp) ((sf.mono e2.heap_extends).mono (Heap.Extends.snoc _ _))
            (sa.mono (Heap.Extends.snoc _ _))
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
      | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
      | litStr cell _ _ | proj cell _ _ =>
        exact (load_cell_ne cell ld (by decide)).elim
    | .Lam (ld12 := ld) (he265 := hr) (hm264 := hm) (ev283 := e1) (ev311 := e2) (ev339 := e3)
        (hc356 := hc) .. =>
      subst hc hr hm
      cases hRE with
      | lam cell rt rb rl =>
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3; subst h1 h2 h3
        cases n with
        | zero => simp at hlen
        | succ n' =>
          have st := expr_inst_levels_rawTm_aux κ n' false (by simp at hlen; omega)
            (RomBound.bounded_mono bd (fun x hx => by simp [hx])) e1 rt ⟨ls, hls, hul⟩
          have sb := expr_inst_levels_rawTm_aux κ n' false (by simp at hlen; omega)
            (RomBound.bounded_mono bd (fun x hx => by simp [hx])) e2
            (rb.mono e1.heap_extends) ⟨ls, hls.mono e1.heap_extends, hul⟩
          have ext12 := e1.heap_extends.trans e2.heap_extends
          obtain ⟨-, rl', -⟩ := IxVM.Refinement.Levels.levelInstParams_obs e3
            (RomBound.bounded_mono bd (fun x hx => by simp [hx]))
            (repKLevel_heapMono₂ ext12 rl) (hls.mono ext12)
          simp only [Expr.instantiateLevelParams, SubstAux.bmeta_subst hul]
          exact .lam (by simp)
            (st.mono (e2.heap_extends.trans (e3.heap_extends.trans (Heap.Extends.snoc _ _))))
            (sb.mono (e3.heap_extends.trans (Heap.Extends.snoc _ _)))
            (repKLevel_heapMono₂ (Heap.Extends.snoc _ _) rl')
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
      | app cell _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
      | litStr cell _ _ | proj cell _ _ =>
        exact (load_cell_ne cell ld (by decide)).elim
    | .Forall (ld12 := ld) (he383 := hr) (hm382 := hm) (ev401 := e1) (ev429 := e2) (ev457 := e3)
        (hc474 := hc) .. =>
      subst hc hr hm
      cases hRE with
      | forallE cell rt rb rl =>
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3; subst h1 h2 h3
        cases n with
        | zero => simp at hlen
        | succ n' =>
          have st := expr_inst_levels_rawTm_aux κ n' false (by simp at hlen; omega)
            (RomBound.bounded_mono bd (fun x hx => by simp [hx])) e1 rt ⟨ls, hls, hul⟩
          have sb := expr_inst_levels_rawTm_aux κ n' false (by simp at hlen; omega)
            (RomBound.bounded_mono bd (fun x hx => by simp [hx])) e2
            (rb.mono e1.heap_extends) ⟨ls, hls.mono e1.heap_extends, hul⟩
          have ext12 := e1.heap_extends.trans e2.heap_extends
          obtain ⟨-, rl', -⟩ := IxVM.Refinement.Levels.levelInstParams_obs e3
            (RomBound.bounded_mono bd (fun x hx => by simp [hx]))
            (repKLevel_heapMono₂ ext12 rl) (hls.mono ext12)
          simp only [Expr.instantiateLevelParams, SubstAux.bmeta_subst hul]
          exact .forallE (by simp)
            (st.mono (e2.heap_extends.trans (e3.heap_extends.trans (Heap.Extends.snoc _ _))))
            (sb.mono (e3.heap_extends.trans (Heap.Extends.snoc _ _)))
            (repKLevel_heapMono₂ (Heap.Extends.snoc _ _) rl')
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
      | app cell _ _ | lam cell _ _ _ | letE cell _ _ _ | litNat cell _ _
      | litStr cell _ _ | proj cell _ _ =>
        exact (load_cell_ne cell ld (by decide)).elim
    | .Let (ld12 := ld) (he501 := hr) (hm500 := hm) (ev519 := e1) (ev547 := e2) (ev575 := e3)
        (hc592 := hc) .. =>
      subst hc hr hm
      cases hRE with
      | letE cell rt rv rb =>
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3; subst h1 h2 h3
        cases n with
        | zero => simp at hlen
        | succ n' =>
          have st := expr_inst_levels_rawTm_aux κ n' false (by simp at hlen; omega)
            (RomBound.bounded_mono bd (fun x hx => by simp [hx])) e1 rt ⟨ls, hls, hul⟩
          have sv := expr_inst_levels_rawTm_aux κ n' false (by simp at hlen; omega)
            (RomBound.bounded_mono bd (fun x hx => by simp [hx])) e2
            (rv.mono e1.heap_extends) ⟨ls, hls.mono e1.heap_extends, hul⟩
          have ext12 := e1.heap_extends.trans e2.heap_extends
          have sb := expr_inst_levels_rawTm_aux κ n' false (by simp at hlen; omega)
            (RomBound.bounded_mono bd (fun x hx => by simp [hx])) e3
            (rb.mono ext12) ⟨ls, hls.mono ext12, hul⟩
          simp only [Expr.instantiateLevelParams, SubstAux.ilp_instShift]
          exact .letE (by simp)
            (st.mono (e2.heap_extends.trans (e3.heap_extends.trans (Heap.Extends.snoc _ _))))
            (sv.mono (e3.heap_extends.trans (Heap.Extends.snoc _ _)))
            (sb.mono (Heap.Extends.snoc _ _))
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
      | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | litNat cell _ _
      | litStr cell _ _ | proj cell _ _ =>
        exact (load_cell_ne cell ld (by decide)).elim
    | .Lit (ld12 := ld) (he609 := hr) (hm608 := hm) .. =>
      subst hr hm
      cases hRE with
      | litNat cell rl hc =>
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with h1; subst h1
        exact .litNat (by simp)
          (repList_heapMono₂ limbListEnum repU64_heapMono₂ (Heap.Extends.snoc _ _) rl) hc
      | litStr cell rb hs =>
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with h1; subst h1
        exact .litStr (by simp)
          (Bytes.repByteStream_heapMono₂ byteListEnum (Heap.Extends.snoc _ _) rb) hs
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
      | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _
      | proj cell _ _ =>
        exact (load_cell_ne cell ld (by decide)).elim
    | .Proj (ld12 := ld) (he648 := hr) (hm647 := hm) (ev680 := e1) (hc697 := hc) .. =>
      subst hc hr hm
      cases hRE with
      | proj cell ra re =>
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3; subst h1 h2 h3
        cases n with
        | zero => simp at hlen
        | succ n' =>
          have se := expr_inst_levels_rawTm_aux κ n' false (by simp at hlen; omega)
            (RomBound.bounded_mono bd (fun x hx => by simp [hx])) e1 re ⟨ls, hls, hul⟩
          exact .proj (by simp)
            (Bytes.repAddressRef_heapMono₂ addrTy
              (e1.heap_extends.trans (Heap.Extends.snoc _ _)) ra)
            (se.mono (Heap.Extends.snoc _ _))
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
      | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _
      | litNat cell _ _ | litStr cell _ _ =>
        exact (load_cell_ne cell ld (by decide)).elim

theorem expr_inst_levels_rawTm {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {e params r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {k : Nat} {R E : KExpr} {us : List KLevel}
    (bd : IxVM.Consistency.Bounded cs)
    (hRE : RawTm κ 0 Γ h k R E e)
    (hus : LvListRep h us params)
    (ev : ObsFn W "KernelLevels::expr_inst_levels" [e, params] h r h' cs) :
    RawTm κ 0 Γ h' k
      (R.instantiateLevelParams (List.range us.length) us)
      (E.instantiateLevelParams (List.range us.length) us) r :=
  expr_inst_levels_rawTm_aux κ cs.length false (Nat.le_refl _) bd ev hRE hus

theorem peel_n_foralls_rawTm_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {k : Nat} {R E : KExpr} {pe r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      n < 4294967296 →
      RawTm κ d Γ h k R E pe →
      ObsFn W "KernelCheck::peel_n_foralls" [pe, .field (n : F)] h r h' cs →
      h' = h ∧ ∃ rbs ebs rbody ebody,
        R.stripPis n = some (rbs, rbody) ∧
        E.stripPis n = some (ebs, ebody) ∧
        RawTm κ d Γ h (k + n) rbody ebody r
  | 0, k, R, E, pe, r, h, h', cs, _, hRE, ev => by
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨rfl, [], [], R, E, rfl, rfl, by rwa [Nat.add_zero]⟩
    | .other (hne19 := hne) .. =>
      exact absurd rfl hne
  | m + 1, k, R, E, pe, r, h, h', cs, hlt, hRE, ev => by
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (hv14 := hv) .. =>
      exact absurd hv (succ_field_ne_zero (by omega))
    | .other (ld34 := ld34) (op87 := op87) (ev64 := ev64) .. =>
      cases hRE with
      | forallE cell rt rb rl =>
        obtain ⟨-, hxs⟩ := load_cell cell ld34
        injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3; subst h1 h2 h3
        rw [evalBinOp_sub_succ m op87] at ev64
        obtain ⟨hh, rbs, ebs, rbody, ebody, hsR, hsE, hbody⟩ :=
          peel_n_foralls_rawTm_spec m (by omega) rb ev64
        refine ⟨hh, (_, _) :: rbs, (_, _) :: ebs, rbody, ebody,
          by simp [Expr.stripPis, hsR], by simp [Expr.stripPis, hsE], ?_⟩
        rwa [show k + (m + 1) = k + 1 + m by omega]
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
      | app cell _ _ | lam cell _ _ _ | letE cell _ _ _ | litNat cell _ _
      | litStr cell _ _ | proj cell _ _ =>
        exact (load_cell_ne cell ld34 (by decide)).elim

theorem collect_spine_rawTm_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {R E : KExpr} {pe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hRE : RawTm κ d Γ h k R E pe)
    (ev : ObsFn W "KernelTypes::collect_spine" [pe] h r h' cs) :
    ∃ (hd sp : SourceValue F) (Rh Eh : KExpr) (Ras Eas : List KExpr),
      r = .tuple [hd, sp] ∧
      RawTm κ d Γ h' k Rh Eh hd ∧
      RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h' Eas sp ∧
      Ras.length = Eas.length ∧
      R = Expr.mkAppN Rh Ras ∧
      E = Expr.mkAppN Eh Eas ∧
      (∀ f a, Rh ≠ .app f a) := by
  match Obs.«KernelTypes::collect_spine».obs ev with
  | .App (ld12 := ld) (ev43 := e1) (he69 := hr) (ev88 := e2) (he105 := hh) (hc106 := hc) .. =>
    subst hc hr hh
    cases hRE with
    | app cell rf ra =>
      obtain ⟨-, hxs⟩ := load_cell cell ld
      injection hxs with h1 hxs; injection hxs with h2; subst h1 h2
      obtain ⟨hd, sp, Rh, Eh, Ras, Eas, htup, hH, hAs, hlen, hR, hE, hnot_app⟩ :=
        collect_spine_rawTm_spec rf e1
      injection htup with hl; injection hl with h1 hl; injection hl with h2
      subst h1 h2
      exact ⟨_, _, Rh, Eh, Ras ++ [_], Eas ++ [_], rfl, hH.mono e2.heap_extends,
        SubstAux.ksnoc (R := fun h E p => Tm κ d Γ h k E p)
          (fun _ _ _ _ ext r => Tm.mono ext r) e2 hAs (ra.toTm.mono e1.heap_extends),
        by simp [hlen], by rw [hR]; exact (mkAppN_snoc Ras Rh _).symm,
        by rw [hE]; exact (mkAppN_snoc Eas Eh _).symm, hnot_app⟩
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
    | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
    | litStr cell _ _ | proj cell _ _ =>
      exact (load_cell_ne cell ld (by decide)).elim
  | .other (ld12 := ld) (hne107 := hne) (he115 := hr) (hm132 := hm) (he136 := hh) .. =>
    subst hr hm hh
    refine ⟨pe, _, R, E, [], [], rfl, hRE.mono (Heap.Extends.snoc _ _), .nil (by simp),
      rfl, rfl, rfl, ?_⟩
    intro f a hR_app
    cases hRE with
    | app cell _ _ =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv
      exact hne [_, _] rfl hv.symm
    | bvarLocal _ _ _ | bvarFree _ _ _ _ | sort _ _ _ | const _ _ _ _
    | lam _ _ _ _ | forallE _ _ _ _ | letE _ _ _ _ | litNat _ _ _
    | litStr _ _ _ | proj _ _ _ =>
      exact nomatch hR_app

theorem mkAppN_const_inj {T₁ T₂ : KKey} {us₁ us₂ : List KLevel} {as₁ as₂ : List KExpr}
    (h : Expr.mkAppN (.const T₁ us₁) as₁ = Expr.mkAppN (.const T₂ us₂) as₂) :
    T₁ = T₂ ∧ us₁ = us₂ ∧ as₁ = as₂ := by
  have hfn := congrArg Expr.getAppFn h
  rw [getAppFn_mkAppN, getAppFn_mkAppN] at hfn
  simp only [Expr.getAppFn] at hfn
  injection hfn with hT hus
  have hargs := congrArg Expr.getAppArgs h
  rw [getAppArgs_mkAppN_const, getAppArgs_mkAppN_const] at hargs
  exact ⟨hT, hus, hargs⟩

theorem rawRecSpine_ilp {T : KKey} (ks : List LevelParam) (us : List KLevel) :
    ∀ {R E : KExpr}, RawRecSpine T R E →
      RawRecSpine T (R.instantiateLevelParams ks us) (E.instantiateLevelParams ks us)
  | _, _, .app => by
    rw [ilp_mkAppN, ilp_mkAppN]
    exact .app
  | _, _, .forallE hrb => .forallE (rawRecSpine_ilp ks us hrb)

theorem RawTm.const_left_inv {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {nm : KKey} {us : List KLevel} {E : KExpr} {p : SourceValue F}
    (rep : RawTm κ d Γ h k (.const nm us) E p) : E = .const nm us := by
  cases rep; rfl

theorem RawTm.forallE_of_load {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {pe pt pb pm : SourceValue F}
    (rep : RawTm κ d Γ h k R E pe)
    (ld : loadValue h pe = .ok (.construct kexprEnum "Forall" [pt, pb, pm])) :
    ∃ Rt Rb mR T B ℓ,
      R = .forallE Rt Rb mR ∧ E = .forallE T B (bmeta ℓ) ∧
      RawTm κ d Γ h k Rt T pt ∧ RawTm κ d Γ h (k + 1) Rb B pb ∧ RepKLevel h ℓ pm := by
  cases rep with
  | forallE cell rt rb rl =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3; subst h1 h2 h3
    exact ⟨_, _, _, _, _, _, rfl, rfl, rt, rb, rl⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
  | app cell _ _ | lam cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

theorem RawTm.not_forallE_of_load {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {pe v1 : SourceValue F}
    (rep : RawTm κ d Γ h k R E pe)
    (ld : loadValue h pe = .ok v1)
    (hne : ∀ vs : List (SourceValue F), vs.length = 3 →
      v1 ≠ .construct kexprEnum "Forall" vs) :
    ∀ Rt Rb mR, R ≠ .forallE Rt Rb mR := by
  intro Rt Rb mR hR
  cases rep with
  | forallE cell _ _ _ =>
    rw [loadValue_enum_cell cell] at ld
    injection ld with hv
    exact hne [_, _, _] rfl hv.symm
  | bvarLocal _ _ _ | bvarFree _ _ _ _ | sort _ _ _ | const _ _ _ _
  | app _ _ _ | lam _ _ _ _ | letE _ _ _ _ | litNat _ _ _
  | litStr _ _ _ | proj _ _ _ =>
    exact nomatch hR

/-! ### Helper circuit specs: `build_param_lvls_range`, `build_rec_lvls_list`, `projection_addr_ctor` -/

theorem build_param_lvls_range_go :
    ∀ (rem start i : Nat) {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      start + i + rem < 4294967296 →
      ObsFn W "KernelCheck::build_param_lvls_range"
        [.field (start : F), .field ((i + rem : Nat) : F), .field (i : F)] h r h' cs →
      RepKLevelList h' ((List.range rem).map fun k => Level.param (start + (i + k))) r
  | 0, start, i, r, h, h', cs, _, ev => by
    match Obs.«KernelCheck::build_param_lvls_range».obs ev with
    | .n0 (he28 := hr) (hm27 := hh) .. =>
      subst hr hh
      have hnil : RepKLevelList
          (h ++ [.construct KernelLevels.klevelListEnum "Nil" []]) []
          (.ptr (.enum KernelLevels.klevelListEnum) h.length) := .nil (by simp)
      rwa [← klevelListEnum_eq] at hnil
    | .other (op17 := op17) (hne33 := hne33) .. =>
      simp only [Nat.add_zero, evalBinOp, sub_self, Except.ok.injEq] at op17
      exact absurd op17.symm hne33
  | rem + 1, start, i, r, h, h', cs, hlt, ev => by
    have hdiff_ne : ((i + (rem + 1) : Nat) : F) - (i : F) ≠ 0 := by
      rw [Nat.cast_add, add_sub_cancel_left]
      exact succ_field_ne_zero (by omega)
    match Obs.«KernelCheck::build_param_lvls_range».obs ev with
    | .n0 (op17 := op17) .. =>
      simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op17
      exact absurd op17 hdiff_ne
    | .other (v46 := v46) (m48 := m48) (v60 := v60) (m78 := m78) (v91 := v91)
        (he41 := hr) (hm40 := hh) (hm56 := hm56) (op74 := op74) (op119 := op119)
        (ev88 := ev88) .. =>
      subst hr hh
      have hv60 : v60 = .field ((start + i : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op74
        rw [← op74, Nat.cast_add]
      have hv91 : v91 = .field ((i + 1 : Nat) : F) := evalBinOp_add_one i op119
      rw [hv91, show i + (rem + 1) = (i + 1) + rem by omega] at ev88
      have htl := build_param_lvls_range_go rem start (i + 1) (by omega) ev88
      have hhd_m48 : RepKLevel m48 (.param (start + i))
          (.ptr (.enum "KernelTypes::KLevelNode") h.length) := by
        rw [hm56, hv60]
        exact .param (by omega) (by simp)
      have hhd_m78 := repKLevel_heapMono₂ ev88.heap_extends hhd_m48
      have ext_end : Heap.Extends m78
          (m78 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Cons"
            [.ptr (.enum "KernelTypes::KLevelNode") h.length, v46]]) := Heap.Extends.snoc _ _
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      have hmap_eq :
          List.map ((fun k => Level.param (start + (i + k))) ∘ (· + 1)) (List.range rem) =
          List.map (fun k => Level.param (start + (i + 1 + k))) (List.range rem) := by
        apply List.map_congr_left; intro k _; simp [Function.comp_def, Nat.add_assoc]
      rw [Nat.add_zero, hmap_eq]
      have hcons : RepKLevelList
          (m78 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Cons"
            [.ptr (.enum "KernelTypes::KLevelNode") h.length, v46]])
          (.param (start + i) :: (List.range rem).map fun k => Level.param (start + (i + 1 + k)))
          (.ptr (.enum KernelLevels.klevelListEnum) m78.length) :=
        .cons (by rw [← klevelListEnum_eq]; simp)
          (repKLevel_heapMono₂ ext_end hhd_m78)
          (htl.mono ext_end)
      rwa [← klevelListEnum_eq] at hcons

theorem build_param_lvls_range_spec {start count : Nat} {r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hlt : start + count < 4294967296)
    (ev : ObsFn W "KernelCheck::build_param_lvls_range"
      [.field (start : F), .field (count : F), .field 0] h r h' cs) :
    RepKLevelList h' ((List.range count).map fun k => Level.param (start + k)) r := by
  have ev' : ObsFn W "KernelCheck::build_param_lvls_range"
      [.field (start : F), .field ((0 + count : Nat) : F), .field ((0 : Nat) : F)] h r h' cs := by
    simpa using ev
  simpa using build_param_lvls_range_go count start 0 (by omega) ev'

theorem build_rec_lvls_list_go :
    ∀ (rem i : Nat) {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      i + rem < 4294967296 →
      ObsFn W "KernelCheck::build_rec_lvls_list"
        [.field ((i + rem : Nat) : F), .field (i : F)] h r h' cs →
      RepKLevelList h' ((List.range rem).map fun k => Level.param (i + k)) r
  | 0, i, r, h, h', cs, _, ev => by
    match Obs.«KernelCheck::build_rec_lvls_list».obs ev with
    | .n0 (he28 := hr) (hm27 := hh) .. =>
      subst hr hh
      have hnil : RepKLevelList
          (h ++ [.construct KernelLevels.klevelListEnum "Nil" []]) []
          (.ptr (.enum KernelLevels.klevelListEnum) h.length) := .nil (by simp)
      rwa [← klevelListEnum_eq] at hnil
    | .other (op17 := op17) (hne33 := hne33) .. =>
      simp only [Nat.add_zero, evalBinOp, sub_self, Except.ok.injEq] at op17
      exact absurd op17.symm hne33
  | rem + 1, i, r, h, h', cs, hlt, ev => by
    have hdiff_ne : ((i + (rem + 1) : Nat) : F) - (i : F) ≠ 0 := by
      rw [Nat.cast_add, add_sub_cancel_left]
      exact succ_field_ne_zero (by omega)
    match Obs.«KernelCheck::build_rec_lvls_list».obs ev with
    | .n0 (op17 := op17) .. =>
      simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op17
      exact absurd op17 hdiff_ne
    | .other (v46 := v46) (m48 := m48) (m69 := m69) (v81 := v81)
        (he41 := hr) (hm40 := hh) (hm56 := hm56) (op102 := op102) (ev79 := ev79) .. =>
      subst hr hh
      have hv81 : v81 = .field ((i + 1 : Nat) : F) := evalBinOp_add_one i op102
      rw [hv81, show i + (rem + 1) = (i + 1) + rem by omega] at ev79
      have htl := build_rec_lvls_list_go rem (i + 1) (by omega) ev79
      have hhd_m48 : RepKLevel m48 (.param i)
          (.ptr (.enum "KernelTypes::KLevelNode") h.length) := by
        rw [hm56]; exact .param (by omega) (by simp)
      have hhd_m69 := repKLevel_heapMono₂ ev79.heap_extends hhd_m48
      have ext_end : Heap.Extends m69
          (m69 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Cons"
            [.ptr (.enum "KernelTypes::KLevelNode") h.length, v46]]) := Heap.Extends.snoc _ _
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      have hmap_eq :
          List.map ((fun k => Level.param (i + k)) ∘ (· + 1)) (List.range rem) =
          List.map (fun k => Level.param (i + 1 + k)) (List.range rem) := by
        apply List.map_congr_left; intro k _; simp [Function.comp_def, Nat.add_assoc]
      rw [Nat.add_zero, hmap_eq]
      have hcons : RepKLevelList
          (m69 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Cons"
            [.ptr (.enum "KernelTypes::KLevelNode") h.length, v46]])
          (.param i :: (List.range rem).map fun k => Level.param (i + 1 + k))
          (.ptr (.enum KernelLevels.klevelListEnum) m69.length) :=
        .cons (by rw [← klevelListEnum_eq]; simp)
          (repKLevel_heapMono₂ ext_end hhd_m69)
          (htl.mono ext_end)
      rwa [← klevelListEnum_eq] at hcons

theorem build_rec_lvls_list_spec {total : Nat} {r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hlt : total < 4294967296)
    (ev : ObsFn W "KernelCheck::build_rec_lvls_list"
      [.field (total : F), .field 0] h r h' cs) :
    RepKLevelList h' ((List.range total).map Level.param) r := by
  have ev' : ObsFn W "KernelCheck::build_rec_lvls_list"
      [.field ((0 + total : Nat) : F), .field ((0 : Nat) : F)] h r h' cs := by
    simpa using ev
  simpa using build_rec_lvls_list_go total 0 (by omega) ev'

/-- Standalone `KernelCheck::projection_addr_ctor` specification under `Good`. -/
theorem projection_addr_ctor_spec {c : Ctx} {bp r : SourceValue F} {b : Bytes.Address}
    {idx cidx : Nat} {h h' : Heap F} {cs : List (Call F)}
    (hidx : idx < 4294967296) (hcidx : cidx < 4294967296)
    (hb : Bytes.RepAddressRef addrTy h b bp)
    (hgood : Good c cs)
    (ev : ObsFn W "KernelCheck::projection_addr_ctor"
      [.field (idx : F), .field (cidx : F), bp] h r h' cs) :
    ∃ a : Bytes.Address, Bytes.RepAddressRef addrTy h' a r ∧
      ixAddr a = cprjAddr (ixAddr b) idx cidx := by
  obtain ⟨v1, m2, cs12, v23, m24, cs34, m114, m127, m140, m153, v165, m166, cs176, m189, cs204,
    ev14, ev36, hm122, hm135, hm148, hm161, hm197, ev178, ev206, hc215⟩ :=
    Obs.«KernelCheck::projection_addr_ctor».obs ev
  obtain ⟨n1, hn1, hx1, rfl, hm2⟩ := Lib.u64_from_field_spec ev14
  obtain ⟨n2, hn2, hx2, rfl, hm24⟩ := Lib.u64_from_field_spec ev36
  injection hx1 with hx1
  injection hx2 with hx2
  have hval_idx : ZMod.val (idx : F) = idx :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hidx (by decide))
  have hval_n1 : ZMod.val (idx : F) = n1 := by
    rw [hx1]; exact ZMod.val_natCast_of_lt (Nat.lt_trans hn1 (by decide))
  have hn1_eq : idx = n1 := hval_idx.symm.trans hval_n1
  have hval_cidx : ZMod.val (cidx : F) = cidx :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hcidx (by decide))
  have hval_n2 : ZMod.val (cidx : F) = n2 := by
    rw [hx2]; exact ZMod.val_natCast_of_lt (Nat.lt_trans hn2 (by decide))
  have hn2_eq : cidx = n2 := hval_cidx.symm.trans hval_n2
  have e1 : Heap.Extends m24 m114 := by rw [hm122]; exact Heap.Extends.snoc _ _
  have e2 : Heap.Extends m114 m127 := by rw [hm135]; exact Heap.Extends.snoc _ _
  have e3 : Heap.Extends m127 m140 := by rw [hm148]; exact Heap.Extends.snoc _ _
  have e4 : Heap.Extends m140 m153 := by rw [hm161]; exact Heap.Extends.snoc _ _
  have e5 : Heap.Extends m153 m189 := by rw [hm197]; exact Heap.Extends.snoc _ _
  have E : Heap.Extends h m189 := by
    rw [← hm2, ← hm24]
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
  have c1 : m189[m24.length]? = some (.construct Specs.Callees.ixExprListEnum "Nil" []) :=
    (e2.trans (e3.trans (e4.trans e5))).getElem?_eq (by rw [hm122]; simp)
  have c2 : m189[m114.length]? = some (.construct addrListEnum "Nil" []) :=
    (e3.trans (e4.trans e5)).getElem?_eq (by rw [hm135]; simp)
  have c3 : m189[m127.length]? = some (.construct Specs.Callees.ixUnivListEnum "Nil" []) :=
    (e4.trans e5).getElem?_eq (by rw [hm148]; simp)
  have c4 : m189[m140.length]? = some (.construct Specs.Callees.ixBinderListEnum "Nil" []) :=
    e5.getElem?_eq (by rw [hm161]; simp)
  have c5 : m189[m153.length]? = some (.construct byteListEnum "Nil" []) := by
    rw [hm197]; simp
  have hrep1 : RepU64 m189 idx.toUInt64 (TagN.u64Value n1) := by
    rw [hn1_eq]
    have e := Lib.repU64_ofNatLT m189 (m := n1) (Nat.lt_trans hn1 (by decide))
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hrep2 : RepU64 m189 cidx.toUInt64 (TagN.u64Value n2) := by
    rw [hn2_eq]
    have e := Lib.repU64_ofNatLT m189 (m := n2) (Nat.lt_trans hn2 (by decide))
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hinfo : Specs.Callees.ProjInfoRep m189 (.cPrj ⟨idx.toUInt64, cidx.toUInt64, ixAddr b⟩)
      (.construct "Ixon::ConstantInfo" "CPrj"
        [.construct "Ixon::ConstructorProj" "Mk" [TagN.u64Value n1, TagN.u64Value n2, bp]]) := by
    simp only [Specs.Callees.ProjInfoRep]
    exact ⟨TagN.u64Value n1, TagN.u64Value n2, bp, b, rfl, hrep1, hrep2,
      Bytes.repAddressRef_heapMono₂ addrTy E hb, rfl⟩
  have hbytes := put_constant_step c ev178 _ _
    (.cPrj ⟨idx.toUInt64, cidx.toUInt64, ixAddr b⟩) [] rfl
    ⟨_, _, _, _, _, rfl, hinfo, RepLinkedList.nil c1, RepLinkedList.nil c2,
      RepLinkedList.nil c3, RepLinkedList.nil c4⟩
    (RepLinkedList.nil c5)
  have hgood_bta : Good c cs204 :=
    hgood.sub (by rw [hc215]; intro x hx; simp [hx])
  obtain ⟨a, ha, haddr⟩ := bytes_to_addr_step c ev206 v165 _ rfl hgood_bta hbytes
  refine ⟨a, ha, ?_⟩
  rw [haddr, ProjAddrAux.bytes_mk_toList]
  rfl

/-! ### `nat_*` expression generator specifications (`nat_ps_at` through `nat_minor_ty`) -/

private theorem kexpr_list_concat_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {xs ys : List KExpr} {l₁ l₂ r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::concat<&KernelTypes::KExprNode>» [l₁, l₂] h r h' cs)
    (h₁ : RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h xs l₁)
    (h₂ : RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h ys l₂) :
    RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h' (xs ++ ys) r := by
  have ev' : ObsFn W (Instance.mk "Lists::concat" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      [l₁, l₂] h r h' cs := by
    rw [Obs.Names.«Lists::concat<&KernelTypes::KExprNode>».symbol]; exact ev
  have h₁' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      (fun h E p => Tm κ d Γ h k E p) h xs l₁ := by
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact h₁
  have h₂' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      (fun h E p => Tm κ d Γ h k E p) h ys l₂ := by
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact h₂
  have hres := Lib.Lists.concat_spec (R := fun h E p => Tm κ d Γ h k E p)
    (fun _ _ _ _ ext r => Tm.mono ext r) ev' h₁' h₂'
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hres

private theorem kexpr_list_drop_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k n : Nat} {xs : List KExpr} {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hn : n < 4294967296)
    (ev : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [l, .field (n : F)] h r h' cs)
    (hl : RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h xs l) :
    n ≤ xs.length ∧
      RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h (xs.drop n) r ∧ h' = h := by
  have hval : ZMod.val (n : F) = n :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hn (by decide))
  have hres := Lib.Lists.drop_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (R := fun h₀ X p₀ => Tm κ d Γ h₀ k X p₀) n hval
    (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol, hval] at hres
  exact hres

/-- `KernelCheck::nat_ps_at(o, n)` builds `Ix.Kernel.structPsAt o n`. -/
theorem nat_ps_at_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (n o k : Nat) {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      o + n ≤ k → k < 4294967296 →
      ObsFn W "KernelCheck::nat_ps_at" [.field (o : F), .field (n : F)] h r h' cs →
      RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h' (Ix.Kernel.structPsAt o n) r
  | 0, o, k, r, h, h', cs, _, _, ev => by
    match Obs.«KernelCheck::nat_ps_at».obs ev with
    | .n0 (he19 := hr) (hm18 := hh) .. =>
      subst hr hh
      exact .nil (by simp)
    | .other (hne24 := hne) .. =>
      exact absurd rfl hne
  | m + 1, o, k, r, h, h', cs, hle, hk, ev => by
    match Obs.«KernelCheck::nat_ps_at».obs ev with
    | .n0 (hv14 := hv) .. =>
      exact absurd hv (succ_field_ne_zero (by omega))
    | .other (v37 := v37) (m39 := m39) (v51 := v51) (x58 := x58) (m77 := m77) (v89 := v89)
        (he32 := hr) (hm31 := hh) (hm47 := hm47) (op73 := op73) (op65 := op65)
        (op110 := op110) (ev87 := ev87) .. =>
      subst hr hh
      have hx58 : x58 = .field ((o + (m + 1) : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op73
        rw [← op73, Nat.cast_add]
      rw [hx58] at op65
      have hv51 : v51 = .field ((o + m : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op65
        rw [← op65, show o + (m + 1) = (o + m) + 1 by omega, Nat.cast_add, Nat.cast_one,
          add_sub_cancel_right]
      have hv89 : v89 = .field (m : F) := evalBinOp_sub_succ m op110
      rw [hv89] at ev87
      have htl := nat_ps_at_spec m o k (by omega) hk ev87
      have hhd_m39 : Tm κ d Γ m39 k (.bvar (o + m)) (.ptr (.enum kexprEnum) h.length) := by
        rw [hm47, hv51]
        exact tm_bvarLocal_nat (by simp) (by omega) (by omega)
      have ext_end : Heap.Extends m77
          (m77 ++ [.construct kexprListEnum "Cons"
            [.ptr (.enum kexprEnum) h.length, v37]]) := Heap.Extends.snoc _ _
      have hstruct : Ix.Kernel.structPsAt (md := .anon) o (m + 1) =
          .bvar (o + m) :: Ix.Kernel.structPsAt o m := by
        simp only [Ix.Kernel.structPsAt, List.range_succ_eq_map, List.map_cons, List.map_map]
        rw [show o + (m + 1) - 1 - 0 = o + m by omega]
        congr 1
        apply List.map_congr_left; intro j _; simp [Function.comp_def]; omega
      rw [hstruct]
      exact .cons (by simp) ((hhd_m39.mono ev87.heap_extends).mono ext_end) (htl.mono ext_end)

/-- `KernelCheck::nat_app_n(f, args)` builds `Expr.mkAppN F Args`. -/
theorem nat_app_n_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {k : Nat} :
    ∀ {Args : List KExpr} {Ef : KExpr} {pf pargs r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      Tm κ d Γ h k Ef pf →
      RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h Args pargs →
      ObsFn W "KernelCheck::nat_app_n" [pf, pargs] h r h' cs →
      Tm κ d Γ h' k (Expr.mkAppN Ef Args) r := by
  intro Args
  induction Args with
  | nil =>
    intro Ef pf pargs r h h' cs hf hargs ev
    match Obs.«KernelCheck::nat_app_n».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. =>
      subst hr hh
      exact hf
    | .Cons (ld12 := ld12) .. =>
      have ld12' : loadValue h pargs = .ok (.construct kexprListEnum "Cons" [_, _]) := ld12
      cases hargs with | nil cell => exact (load_cell_ne cell ld12' (by decide)).elim
  | cons Ea Eas ih =>
    intro Ef pf pargs r h h' cs hf hargs ev
    match Obs.«KernelCheck::nat_app_n».obs ev with
    | .Nil (ld12 := ld12) .. =>
      have ld12' : loadValue h pargs = .ok (.construct kexprListEnum "Nil" []) := ld12
      cases hargs with | cons cell _ _ => exact (load_cell_ne cell ld12' (by decide)).elim
    | .Cons (m50 := m50) (ld12 := ld12) (hm58 := hm58) (ev46 := ev46) .. =>
      obtain ⟨Ea', Eas', heq, ha, has⟩ := RepList.cons_of_load hargs ld12
      injection heq with h1 h2; subst h1 h2
      have ext50 : Heap.Extends h m50 := by rw [hm58]; exact Heap.Extends.snoc _ _
      have happ : Tm κ d Γ m50 k (.app Ef Ea) (.ptr (.enum kexprEnum) h.length) := by
        rw [hm58]; exact .app (by simp) (hf.mono ext50) (ha.mono ext50)
      exact ih happ (has.mono ext50) ev46

private theorem mentionsConst_mkAppN_of_head {T : KKey} :
    ∀ (as : List KExpr) {f : KExpr}, f.mentionsConst T = true →
      (Expr.mkAppN f as).mentionsConst T = true
  | [], _, hf => hf
  | _ :: as, _, hf =>
    mentionsConst_mkAppN_of_head as (by simp [Ix.Kernel.Expr.mentionsConst, hf])

/-- `KernelCheck::nat_mentions` always returns `.field 0` or `.field 1` without modifying the heap. -/
theorem nat_mentions_ret_bit {κ : _root_.Address → KKey} {bT : Bytes.Address} :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {k : Nat} {E : KExpr} {pe pt r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ n →
      Tm κ d Γ h k E pe →
      Bytes.RepAddressRef addrTy h bT pt →
      ObsFn W "KernelCheck::nat_mentions" [pe, pt] h r h' cs →
      (r = .field 0 ∨ r = .field 1) ∧ h' = h
  | n, d, Γ, k, E, pe, pt, r, h, h', cs, hlen, hE, hpt, ev => by
    match Obs.«KernelCheck::nat_mentions».obs ev with
    | .Const (ld12 := ld) (ev36 := ev_eq) .. =>
      obtain ⟨a, _, _, ra, _, _, _⟩ := hE.const_of_load ld
      obtain ⟨hr, rfl⟩ := Lib.address_eq_spec ev_eq ra hpt
      refine ⟨?_, rfl⟩
      by_cases hab : a = bT
      · exact Or.inr (by simp [hr, hab])
      · exact Or.inl (by simp [hr, hab])
    | .App_n1 (ld12 := ld) (ev85 := ev1) (he106 := hr) (he107 := hh) (hc108 := hc) .. =>
      subst hc hr hh
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨Ef, _, _, hf, _⟩ := hE.app_of_load ld
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) hf hpt ev1
        exact ⟨Or.inr rfl, rfl⟩
    | .App_other (ld12 := ld) (ev85 := ev1) (ev118 := ev2) (hc135 := hc) .. =>
      subst hc
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨Ef, Ea, _, hf, ha⟩ := hE.app_of_load ld
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) hf hpt ev1
        exact nat_mentions_ret_bit n' (by simp at hlen; omega) ha hpt ev2
    | .Lam_n1 (ld12 := ld) (ev173 := ev1) (he194 := hr) (he195 := hh) (hc196 := hc) .. =>
      subst hc hr hh
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨T', _, _, _, ht, _, _⟩ := hE.lam_of_load ld
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) ht hpt ev1
        exact ⟨Or.inr rfl, rfl⟩
    | .Lam_other (ld12 := ld) (ev173 := ev1) (ev206 := ev2) (hc223 := hc) .. =>
      subst hc
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨_, B', _, _, ht, hb, _⟩ := hE.lam_of_load ld
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) ht hpt ev1
        exact nat_mentions_ret_bit n' (by simp at hlen; omega) hb hpt ev2
    | .Forall_n1 (ld12 := ld) (ev261 := ev1) (he282 := hr) (he283 := hh) (hc284 := hc) .. =>
      subst hc hr hh
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨_, _, _, _, ht, _, _⟩ := hE.forallE_of_load ld
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) ht hpt ev1
        exact ⟨Or.inr rfl, rfl⟩
    | .Forall_other (ld12 := ld) (ev261 := ev1) (ev294 := ev2) (hc311 := hc) .. =>
      subst hc
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨_, _, _, _, ht, hb, _⟩ := hE.forallE_of_load ld
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) ht hpt ev1
        exact nat_mentions_ret_bit n' (by simp at hlen; omega) hb hpt ev2
    | .Let_n1 (ld12 := ld) (ev348 := ev1) (he369 := hr) (he370 := hh) (hc371 := hc) .. =>
      subst hc hr hh
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨_, _, _, _, ht, _, _⟩ := hE.letE_of_load ld
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) ht hpt ev1
        exact ⟨Or.inr rfl, rfl⟩
    | .Let_other_n1 (ld12 := ld) (ev348 := ev1) (ev390 := ev2) (he411 := hr) (he412 := hh)
        (hc413 := hc) .. =>
      subst hc hr hh
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨_, _, _, _, ht, hv, _⟩ := hE.letE_of_load ld
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) ht hpt ev1
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) hv hpt ev2
        exact ⟨Or.inr rfl, rfl⟩
    | .Let_other_other (ld12 := ld) (ev348 := ev1) (ev390 := ev2) (ev423 := ev3) (hc440 := hc) .. =>
      subst hc
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨_, _, _, _, ht, hv, hb⟩ := hE.letE_of_load ld
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) ht hpt ev1
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) hv hpt ev2
        exact nat_mentions_ret_bit n' (by simp at hlen; omega) hb hpt ev3
    | .Proj (ld12 := ld) (ev470 := ev1) (hc487 := hc) .. =>
      subst hc
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨_, _, _, _, rfl, _, hes⟩ := hE.proj_of_load ld
        exact nat_mentions_ret_bit n' (by simp at hlen; omega) hes hpt ev1
    | .other (he492 := hr) (he493 := hh) .. =>
      exact ⟨Or.inl hr, hh⟩

private theorem field0_of_bit_ne1 {v : SourceValue F}
    (hbit : v = .field 0 ∨ v = .field 1) (hne : v ≠ .field 1) : v = .field 0 := by
  rcases hbit with rfl | rfl
  · rfl
  · exact absurd rfl hne

/-- `KernelCheck::nat_mentions(e, t) = .field 0` certifies `E.mentionsConst T = false`. -/
theorem nat_mentions_zero_spec {κ : _root_.Address → KKey} {T : KKey} {bT : Bytes.Address}
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = bT) :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {k : Nat} {E : KExpr} {pe pt : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ n →
      Tm κ d Γ h k E pe →
      Bytes.RepAddressRef addrTy h bT pt →
      noProjAt T E = true →
      (∀ i < d, (Γ i).mentionsConst T = false) →
      ObsFn W "KernelCheck::nat_mentions" [pe, pt] h (.field 0) h' cs →
      E.mentionsConst T = false ∧ h' = h
  | n, d, Γ, k, E, pe, pt, h, h', cs, hlen, hE, hpt, hnoProj, hΓ, ev => by
    have field1_ne_0 : ((.field 0 : SourceValue F) = .field 1) → False := by
      intro h01; injection h01 with h01'; exact zero_ne_one h01'
    match Obs.«KernelCheck::nat_mentions».obs ev with
    | .Const (ld12 := ld) (ev36 := ev_eq) .. =>
      obtain ⟨a, us, rfl, ra, _, _, _⟩ := hE.const_of_load ld
      obtain ⟨hr, rfl⟩ := Lib.address_eq_spec ev_eq ra hpt
      have hne_a : a ≠ bT := by
        intro hab
        subst hab
        simp only [beq_self_eq_true, ↓reduceIte] at hr
        exact field1_ne_0 hr
      have hne_T : (κ (ixAddr a) == T) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun heq => hne_a (hκ_inj a heq)
      exact ⟨hne_T, rfl⟩
    | .App_n1 (he106 := hr) .. => exact (field1_ne_0 hr).elim
    | .App_other (ld12 := ld) (ev85 := ev1) (hne109 := hne1) (ev118 := ev2) (hc135 := hc) .. =>
      subst hc
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
        simp only [noProjAt, Bool.and_eq_true] at hnoProj
        obtain ⟨hb1, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) hf hpt ev1
        rw [field0_of_bit_ne1 hb1 hne1] at ev1
        obtain ⟨hf0, _⟩ := nat_mentions_zero_spec hκ_inj n' (by simp at hlen; omega) hf hpt hnoProj.1 hΓ ev1
        obtain ⟨ha0, rfl⟩ := nat_mentions_zero_spec hκ_inj n' (by simp at hlen; omega) ha hpt hnoProj.2 hΓ ev2
        exact ⟨by simp [Ix.Kernel.Expr.mentionsConst, hf0, ha0], rfl⟩
    | .Lam_n1 (he194 := hr) .. => exact (field1_ne_0 hr).elim
    | .Lam_other (ld12 := ld) (ev173 := ev1) (hne197 := hne1) (ev206 := ev2) (hc223 := hc) .. =>
      subst hc
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨Ed, Eb, _, rfl, hd, hb, _⟩ := hE.lam_of_load ld
        simp only [noProjAt, Bool.and_eq_true] at hnoProj
        obtain ⟨hb1, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) hd hpt ev1
        rw [field0_of_bit_ne1 hb1 hne1] at ev1
        obtain ⟨hd0, _⟩ := nat_mentions_zero_spec hκ_inj n' (by simp at hlen; omega) hd hpt hnoProj.1 hΓ ev1
        obtain ⟨hb0, rfl⟩ := nat_mentions_zero_spec hκ_inj n' (by simp at hlen; omega) hb hpt hnoProj.2 hΓ ev2
        exact ⟨by simp [Ix.Kernel.Expr.mentionsConst, hd0, hb0], rfl⟩
    | .Forall_n1 (he282 := hr) .. => exact (field1_ne_0 hr).elim
    | .Forall_other (ld12 := ld) (ev261 := ev1) (hne285 := hne1) (ev294 := ev2) (hc311 := hc) .. =>
      subst hc
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨Ed, Eb, _, rfl, hd, hb, _⟩ := hE.forallE_of_load ld
        simp only [noProjAt, Bool.and_eq_true] at hnoProj
        obtain ⟨hb1, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) hd hpt ev1
        rw [field0_of_bit_ne1 hb1 hne1] at ev1
        obtain ⟨hd0, _⟩ := nat_mentions_zero_spec hκ_inj n' (by simp at hlen; omega) hd hpt hnoProj.1 hΓ ev1
        obtain ⟨hb0, rfl⟩ := nat_mentions_zero_spec hκ_inj n' (by simp at hlen; omega) hb hpt hnoProj.2 hΓ ev2
        exact ⟨by simp [Ix.Kernel.Expr.mentionsConst, hd0, hb0], rfl⟩
    | .Let_n1 (he369 := hr) .. => exact (field1_ne_0 hr).elim
    | .Let_other_n1 (he411 := hr) .. => exact (field1_ne_0 hr).elim
    | .Let_other_other (ld12 := ld) (ev348 := ev1) (ev390 := ev2) (hne414 := hne2)
        (ev423 := ev3) (hc440 := hc) .. =>
      subst hc
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨Ed, Ev, Eb, rfl, hd, hv, hb⟩ := hE.letE_of_load ld
        obtain ⟨hnoB, hnoV⟩ := noProjAt_of_instantiate1Lift hnoProj
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) hd hpt ev1
        obtain ⟨hb2, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) hv hpt ev2
        rw [field0_of_bit_ne1 hb2 hne2] at ev2
        obtain ⟨hb0, rfl⟩ := nat_mentions_zero_spec hκ_inj n' (by simp at hlen; omega) hb hpt hnoB hΓ ev3
        refine ⟨mentionsConst_instantiate1Lift_false hb0 (fun hhas => ?_), rfl⟩
        exact (nat_mentions_zero_spec hκ_inj n' (by simp at hlen; omega) hv hpt (hnoV hhas) hΓ ev2).1
    | .Proj (ld12 := ld) (ev470 := ev1) (hc487 := hc) .. =>
      subst hc
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨a, _, Es, _, rfl, _, hes⟩ := hE.proj_of_load ld
        simp only [noProjAt, Bool.and_eq_true, bne_iff_ne] at hnoProj
        obtain ⟨hs0, rfl⟩ := nat_mentions_zero_spec hκ_inj n' (by simp at hlen; omega) hes hpt hnoProj.2 hΓ ev1
        exact ⟨by simp [Ix.Kernel.Expr.mentionsConst, beq_eq_false_iff_ne.mpr hnoProj.1, hs0], rfl⟩
    | .other (ld12 := ld) (hne54 := hneC) (hne136 := hneA) (hne224 := hneL)
        (hne312 := hneF) (hne441 := hneLet) (hne488 := hneP) (he493 := hh) .. =>
      refine ⟨?_, hh⟩
      cases hE with
      | bvarLocal _ _ _ => rfl
      | bvarFree _ _ _ hd_lt =>
        exact hΓ _ (by unfold fvIdx; omega)
      | sort _ _ _ | litNat _ _ _ | litStr _ _ _ => rfl
      | const cell _ _ _ =>
        rw [loadValue_enum_cell cell] at ld
        injection ld with hv
        exact (hneC [_, _] rfl hv.symm).elim
      | app cell _ _ =>
        rw [loadValue_enum_cell cell] at ld
        injection ld with hv
        exact (hneA [_, _] rfl hv.symm).elim
      | lam cell _ _ _ =>
        rw [loadValue_enum_cell cell] at ld
        injection ld with hv
        exact (hneL [_, _, _] rfl hv.symm).elim
      | forallE cell _ _ _ =>
        rw [loadValue_enum_cell cell] at ld
        injection ld with hv
        exact (hneF [_, _, _] rfl hv.symm).elim
      | letE cell _ _ _ =>
        rw [loadValue_enum_cell cell] at ld
        injection ld with hv
        exact (hneLet [_, _, _] rfl hv.symm).elim
      | proj cell _ _ =>
        rw [loadValue_enum_cell cell] at ld
        injection ld with hv
        exact (hneP [_, _, _] rfl hv.symm).elim

/-- Whenever `KernelCheck::nat_positivity` returns `r ≠ .field 3`, it returns `.field 1` or `.field 2`
(hence `r ≠ .field 0`) and `E` mentions `T`. -/
theorem nat_positivity_ok_spec {κ : _root_.Address → KKey} {T : KKey} {bT : Bytes.Address}
    (hT : κ (ixAddr bT) = T) :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {k : Nat} {R E : KExpr}
      {pe pt plps pnp pni po pk r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ n →
      r ≠ .field 3 →
      RawTm κ d Γ h k R E pe →
      Bytes.RepAddressRef addrTy h bT pt →
      ObsFn W "KernelCheck::nat_positivity" [pe, pt, plps, pnp, pni, po, pk] h r h' cs →
      (r = .field 1 ∨ r = .field 2) ∧ E.mentionsConst T = true
  | n, d, Γ, k, R, E, pe, pt, plps, pnp, pni, po, pk, r, h, h', cs, hlen, hr3, hRE, hpt, ev => by
    match Obs.«KernelCheck::nat_positivity».obs ev with
    | .Forall_n1 (he71 := hr) .. => exact absurd hr hr3
    | .Forall_other (ld12 := ld) (ev50 := ev_m) (ev83 := ev_p) (hc148 := hc) .. =>
      subst hc
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨_, _, _, Ed, Eb, _, _, rfl, hd, hb, _⟩ := hRE.forallE_of_load ld
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) hd.toTm hpt ev_m
        obtain ⟨hr12, hmen⟩ := nat_positivity_ok_spec hT n' (by simp at hlen; omega) hr3 hb hpt ev_p
        exact ⟨hr12, by simp [Ix.Kernel.Expr.mentionsConst, hmen]⟩
    | .other_Const_n1_n1_n0 (ev166 := ev_sp) (ld199 := ld_h) (ev246 := ev_eq)
        (op240 := op_m1) (op232 := op_m2) (he495 := hr) .. =>
      obtain ⟨hd, _, _, Eh, _, Eas, htup, hH, _, _, _, hE_eq, _⟩ := collect_spine_rawTm_spec hRE ev_sp
      injection htup with hl; injection hl with h1 _; subst h1
      obtain ⟨a, us, hEh, ra, _, _, _⟩ := hH.toTm.const_of_load ld_h
      have hpt' := Bytes.repAddressRef_heapMono₂ addrTy ev_sp.heap_extends hpt
      obtain ⟨hx233, _⟩ := Lib.address_eq_spec ev_eq ra hpt'
      have hab : a = bT := by
        by_cases h_eq : a = bT
        · exact h_eq
        · rw [ite_eq_right h_eq] at hx233
          rw [hx233] at op_m1
          simp only [evalBinOp, zero_mul, Except.ok.injEq] at op_m1
          rw [← op_m1] at op_m2
          simp only [evalBinOp, zero_mul, Except.ok.injEq, Value.field.injEq] at op_m2
          exact (zero_ne_one op_m2).elim
      subst hab
      rw [hE_eq, hEh, hT]
      exact ⟨Or.inl hr, mentionsConst_mkAppN_of_head Eas (by simp [Ix.Kernel.Expr.mentionsConst])⟩
    | .other_Const_n1_n1_other (ev166 := ev_sp) (ld199 := ld_h) (ev246 := ev_eq)
        (op240 := op_m1) (op232 := op_m2) (he502 := hr) .. =>
      obtain ⟨hd, _, _, Eh, _, Eas, htup, hH, _, _, _, hE_eq, _⟩ := collect_spine_rawTm_spec hRE ev_sp
      injection htup with hl; injection hl with h1 _; subst h1
      obtain ⟨a, us, hEh, ra, _, _, _⟩ := hH.toTm.const_of_load ld_h
      have hpt' := Bytes.repAddressRef_heapMono₂ addrTy ev_sp.heap_extends hpt
      obtain ⟨hx233, _⟩ := Lib.address_eq_spec ev_eq ra hpt'
      have hab : a = bT := by
        by_cases h_eq : a = bT
        · exact h_eq
        · rw [ite_eq_right h_eq] at hx233
          rw [hx233] at op_m1
          simp only [evalBinOp, zero_mul, Except.ok.injEq] at op_m1
          rw [← op_m1] at op_m2
          simp only [evalBinOp, zero_mul, Except.ok.injEq, Value.field.injEq] at op_m2
          exact (zero_ne_one op_m2).elim
      subst hab
      rw [hE_eq, hEh, hT]
      exact ⟨Or.inr hr, mentionsConst_mkAppN_of_head Eas (by simp [Ix.Kernel.Expr.mentionsConst])⟩
    | .other_Const_n1_other (he509 := hr) .. => exact absurd hr hr3
    | .other_Const_other (he516 := hr) .. => exact absurd hr hr3
    | .other_other (he523 := hr) .. => exact absurd hr hr3

/-! ### Graded telescope binder-list representation `TeleRep` -/

abbrev teleListEnum : String :=
  Obs.Names.«Lists::Node<(&KernelTypes::KExprNode, &KernelTypes::KLevelNode)>»

abbrev fieldListEnum : String :=
  Obs.Names.«Lists::Node<Field>»

/-- Heap representation of a binder telescope `[(T₀, bmeta ℓ₀), (T₁, bmeta ℓ₁), ...]`
at graded local binder depths `k, k + 1, ...`. -/
inductive TeleRep (κ : _root_.Address → KKey) (d : Nat) (Γ : Nat → KExpr) (h : Heap F) :
    Nat → List (KExpr × Ix.Kernel.BinderMeta) → SourceValue F → Prop where
  | nil {k addr : Nat} (cell : h[addr]? = some (.construct teleListEnum "Nil" [])) :
      TeleRep κ d Γ h k [] (.ptr (.enum teleListEnum) addr)
  | cons {k addr : Nat} {T : KExpr} {ℓ : KLevel} {bs : List (KExpr × Ix.Kernel.BinderMeta)}
      {pt pm rest : SourceValue F}
      (cell : h[addr]? = some (.construct teleListEnum "Cons" [.tuple [pt, pm], rest]))
      (ht : Tm κ d Γ h k T pt)
      (hl : RepKLevel h ℓ pm)
      (hbs : TeleRep κ d Γ h (k + 1) bs rest) :
      TeleRep κ d Γ h k ((T, bmeta ℓ) :: bs) (.ptr (.enum teleListEnum) addr)

theorem TeleRep.mono {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h h' : Heap F} {k : Nat} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {p : SourceValue F}
    (ext : Heap.Extends h h') (rep : TeleRep κ d Γ h k bs p) : TeleRep κ d Γ h' k bs p := by
  induction rep with
  | nil cell => exact .nil (ext.getElem?_eq cell)
  | cons cell ht hl _ ih =>
    exact .cons (ext.getElem?_eq cell) (ht.mono ext) (repKLevel_heapMono₂ ext hl) ih

theorem TeleRep.toRepListTrue {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {p : SourceValue F}
    (rep : TeleRep κ d Γ h k bs p) :
    RepList teleListEnum (fun _ _ _ => True) h bs p := by
  induction rep with
  | nil cell => exact .nil cell
  | cons cell _ _ _ ih => exact .cons cell trivial ih

theorem tele_length_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {p r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<(&KernelTypes::KExprNode, &KernelTypes::KLevelNode)>»
      [p] h r h' cs)
    (hbs : TeleRep κ d Γ h k bs p) :
    r = .field (bs.length : F) ∧ h' = h := by
  have ev' : ObsFn W
      (Instance.mk "Lists::length"
        [(.tuple [(.ptr (.named "KernelTypes::KExprNode" [])),
          (.ptr (.named "KernelTypes::KLevelNode" []))])]).symbol
      [p] h r h' cs := by
    rw [Obs.Names.«Lists::length<(&KernelTypes::KExprNode, &KernelTypes::KLevelNode)>».symbol]
    exact ev
  have hl' : RepList
      (Instance.mk "Lists::Node"
        [(.tuple [(.ptr (.named "KernelTypes::KExprNode" [])),
          (.ptr (.named "KernelTypes::KLevelNode" []))])]).symbol
      (fun _ _ _ => True) h bs p := by
    rw [Obs.Names.«Lists::Node<(&KernelTypes::KExprNode, &KernelTypes::KLevelNode)>».symbol]
    exact hbs.toRepListTrue
  exact Lib.Lists.length_spec ev' hl'

theorem field_list_length_spec {R : Heap F → Nat → SourceValue F → Prop}
    {xs : List Nat} {p r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<Field>» [p] h r h' cs)
    (hxs : RepList fieldListEnum R h xs p) :
    r = .field (xs.length : F) ∧ h' = h := by
  have ev' : ObsFn W (Instance.mk "Lists::length" [.field]).symbol [p] h r h' cs := by
    rw [Obs.Names.«Lists::length<Field>».symbol]; exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [.field]).symbol R h xs p := by
    rw [Obs.Names.«Lists::Node<Field>».symbol]; exact hxs
  exact Lib.Lists.length_spec ev' hl'

/-! ### `nat_replace_pis`, `nat_pi_binders`, `nat_mk_binders`, `nat_field_dom` -/

/-- `KernelCheck::nat_replace_pis` computes `Expr.replacePisPw` (`lam = 0`) or `Expr.pisToLamsPw` (`lam ≠ 0`). -/
theorem nat_replace_pis_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (cnt : Nat) {k : Nat} {ℓ : KLevel} {tele body : KExpr}
      {ppw ptele pb plam r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cnt < 4294967296 →
      RepKLevel h ℓ ppw →
      Tm κ d Γ h k tele ptele →
      Tm κ d Γ h (k + cnt) body pb →
      ObsFn W "KernelCheck::nat_replace_pis"
        [ppw, .field (cnt : F), ptele, pb, plam] h r h' cs →
      ∃ out,
        (if plam = .field 0
         then Expr.replacePisPw ℓ.zeronessOf cnt tele body
         else Expr.pisToLamsPw ℓ.zeronessOf cnt tele body) = some out ∧
        Tm κ d Γ h' k out r
  | 0, k, _, _, body, _, _, pb, plam, r, h, h', cs, _, _, _, hbody, ev => by
    match Obs.«KernelCheck::nat_replace_pis».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      refine ⟨body, ?_, by rwa [Nat.add_zero] at hbody⟩
      by_cases hl : plam = .field 0 <;> simp [hl, Expr.replacePisPw, Expr.pisToLamsPw]
    | .other_n0 (hne19 := hne) .. => exact absurd rfl hne
    | .other_other (hne19 := hne) .. => exact absurd rfl hne
  | m + 1, k, ℓ, tele, body, ppw, ptele, pb, plam, r, h, h', cs, hlt, hpw, htele, hbody, ev => by
    have hne0 : (.field ((m + 1 : Nat) : F) : SourceValue F) ≠ .field 0 :=
      succ_field_ne_zero (by omega)
    match Obs.«KernelCheck::nat_replace_pis».obs ev with
    | .n0 (hv14 := hv) .. => exact absurd hv hne0
    | .other_n0 (x_ty := xty) (v54 := v54) (m55 := m55) (ld33 := ld) (op93 := op) (ev67 := ev')
        (hv129 := hlam0) (he134 := hr) (hm133 := hm) .. =>
      subst hlam0 hr hm
      obtain ⟨T, B, _, rfl, ht, hb, _⟩ := htele.forallE_of_load ld
      rw [evalBinOp_sub_succ m op] at ev'
      have hbody' : Tm κ d Γ h (k + 1 + m) body pb := by
        rwa [show k + 1 + m = k + (m + 1) by omega]
      obtain ⟨out', hout', htm'⟩ := nat_replace_pis_spec m (by omega) hpw hb hbody' ev'
      simp only [↓reduceIte] at hout' ⊢
      have ext_end : Heap.Extends m55
          (m55 ++ [.construct kexprEnum "Forall" [xty, v54, ppw]]) := Heap.Extends.snoc _ _
      exact ⟨.forallE T out' (bmeta ℓ),
        by simp [Expr.replacePisPw, hout', bmeta],
        .forallE (by simp) ((ht.mono ev'.heap_extends).mono ext_end)
          (htm'.mono ext_end) (repKLevel_heapMono₂ (ev'.heap_extends.trans ext_end) hpw)⟩
    | .other_other (x_ty := xty) (v54 := v54) (m55 := m55) (ld33 := ld) (op93 := op) (ev67 := ev')
        (hne163 := hlam_ne) (he171 := hr) (hm170 := hm) .. =>
      subst hr hm
      obtain ⟨T, B, _, rfl, ht, hb, _⟩ := htele.forallE_of_load ld
      rw [evalBinOp_sub_succ m op] at ev'
      have hbody' : Tm κ d Γ h (k + 1 + m) body pb := by
        rwa [show k + 1 + m = k + (m + 1) by omega]
      obtain ⟨out', hout', htm'⟩ := nat_replace_pis_spec m (by omega) hpw hb hbody' ev'
      simp only [ite_eq_right hlam_ne] at hout' ⊢
      have ext_end : Heap.Extends m55
          (m55 ++ [.construct kexprEnum "Lam" [xty, v54, ppw]]) := Heap.Extends.snoc _ _
      exact ⟨.lam T out' (bmeta ℓ),
        by simp [Expr.pisToLamsPw, hout', bmeta],
        .lam (by simp) ((ht.mono ev'.heap_extends).mono ext_end)
          (htm'.mono ext_end) (repKLevel_heapMono₂ (ev'.heap_extends.trans ext_end) hpw)⟩

/-- On a strictly-positive recursive field domain (`RawRecSpine`), `KernelCheck::nat_pi_binders`
peels `E.piBinders = (bs, efb)` and returns a `TeleRep` for `bs` together with a `RawTm` on `efb`. -/
theorem nat_pi_binders_rawRecSpine_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {T : KKey} :
    ∀ {R E : KExpr}, RawRecSpine T R E →
      ∀ {k : Nat} {pe pbs plast : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        RawTm κ d Γ h k R E pe →
        ObsFn W "KernelCheck::nat_pi_binders" [pe] h (.tuple [pbs, plast]) h' cs →
        ∃ us rAs eAs,
          E.piBinders = (E.piBinders.1, Expr.mkAppN (.const T us) eAs) ∧
          TeleRep κ d Γ h' k E.piBinders.1 pbs ∧
          RawTm κ d Γ h' (k + E.piBinders.1.length)
            (Expr.mkAppN (.const T us) rAs) (Expr.mkAppN (.const T us) eAs) plast
  | _, _, .app (us := us) (rAs := rAs) (eAs := eAs), k, pe, pbs, plast, h, h', cs, hRaw, ev => by
    have hpb : (Expr.mkAppN (.const T us) eAs).piBinders = ([], Expr.mkAppN (.const T us) eAs) := by
      cases heq : Expr.mkAppN (.const T us) eAs with
      | forallE dom bo bi => exact (mkAppN_const_not_forallE T us eAs dom bo bi heq).elim
      | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
      | lit _ | proj _ _ _ => rfl
    match Obs.«KernelCheck::nat_pi_binders».obs ev with
    | .Forall (ld12 := ld) .. =>
      obtain ⟨RT, RB, _, _, _, _, hR_eq, _, _, _, _⟩ := hRaw.forallE_of_load ld
      exact (mkAppN_const_not_forallE T us rAs RT RB _ hR_eq).elim
    | .other (he138 := hr) (hm148 := hm) (he159 := hh) .. =>
      subst hh hm
      injection hr with hl; injection hl with hpbs hl; injection hl with hpe
      subst hpbs hpe
      rw [hpb]
      exact ⟨us, rAs, eAs, rfl, .nil (by simp),
        by simpa using hRaw.mono (Heap.Extends.snoc h _)⟩
  | _, _, .forallE (rd := rd) (rb := rb) (ed := ed) (eb := eb) (m := m) hrb,
      k, pe, pbs, plast, h, h', cs, hRaw, ev => by
    match Obs.«KernelCheck::nat_pi_binders».obs ev with
    | .Forall (x_d := xd) (x_m := xm) (m36 := m1) (x_bs := xbs) (x_r := xr) (m76 := m2)
        (ld12 := ld) (ev48 := ev') (he74 := hr) (hm84 := hm2) (he128 := hh) .. =>
      subst hh hm2
      obtain ⟨_, _, _, T', B', ℓ, hR_eq, hE_eq, ht, hb, hl_rep⟩ := hRaw.forallE_of_load ld
      injection hR_eq with _ hrb_eq _
      injection hE_eq with hT_eq heb_eq hm_eq
      subst hrb_eq hT_eq heb_eq
      injection hr with hl; injection hl with hpbs hl; injection hl with hxr
      subst hpbs hxr
      obtain ⟨us, rAs, eAs, hpb_sub, htele_sub, hlast⟩ :=
        nat_pi_binders_rawRecSpine_spec hrb hb ev'
      have ext_end : Heap.Extends m1
          (m1 ++ [.construct teleListEnum "Cons" [.tuple [xd, xm], xbs]]) := Heap.Extends.snoc _ _
      have hpb_cons : (Expr.forallE ed eb m).piBinders =
          ((ed, m) :: eb.piBinders.1, Expr.mkAppN (.const T us) eAs) := by
        unfold Ix.Kernel.Expr.piBinders
        rw [hpb_sub]
      rw [hpb_cons]
      refine ⟨us, rAs, eAs, rfl, ?_, ?_⟩
      · rw [← hm_eq]
        exact .cons (by simp) ((ht.toTm.mono ev'.heap_extends).mono ext_end)
          (repKLevel_heapMono₂ (ev'.heap_extends.trans ext_end) hl_rep)
          (htele_sub.mono ext_end)
      · simpa [Nat.add_assoc, Nat.add_comm 1] using hlast.mono ext_end
    | .other (ld12 := ld) (hne130 := hne) .. =>
      exact (hRaw.not_forallE_of_load ld hne rd rb m rfl).elim

/-- `KernelCheck::nat_mk_binders` wraps `bs` as `Expr.mkPisOf` (`lam = 0`) or `Expr.mkLamsOf` (`lam ≠ 0`). -/
theorem nat_mk_binders_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ {bs : List (KExpr × Ix.Kernel.BinderMeta)} {k : Nat} {body : KExpr}
      {pbs pbody plam r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      TeleRep κ d Γ h k bs pbs →
      Tm κ d Γ h (k + bs.length) body pbody →
      ObsFn W "KernelCheck::nat_mk_binders" [pbs, pbody, plam] h r h' cs →
      Tm κ d Γ h' k (if plam = .field 0 then Expr.mkPisOf bs body else Expr.mkLamsOf bs body) r := by
  intro bs
  induction bs with
  | nil =>
    intro k body pbs pbody plam r h h' cs hbs hbody ev
    match Obs.«KernelCheck::nat_mk_binders».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. =>
      subst hr hh
      by_cases hl : plam = .field 0 <;>
        simpa [hl, Expr.mkPisOf, Expr.mkLamsOf] using hbody
    | .Cons_n0 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      cases hbs with | nil cell => exact (load_cell_ne cell ld (by decide)).elim
  | cons b rest ih =>
    intro k body pbs pbody plam r h h' cs hbs hbody ev
    cases hbs with
    | cons cell ht hl hrest =>
      have hbody' : Tm κ d Γ h (k + 1 + rest.length) body pbody := by
        simpa [Nat.add_assoc, Nat.add_comm 1] using hbody
      match Obs.«KernelCheck::nat_mk_binders».obs ev with
      | .Nil (ld12 := ld) .. => exact (load_cell_ne cell ld (by decide)).elim
      | .Cons_n0 (x_ty := xty) (x_m := xm) (v67 := v67) (m68 := m68)
          (ld12 := ld) (ev80 := ev') (hv118 := hlam0) (he123 := hr) (hm122 := hm) .. =>
        subst hlam0 hr hm
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with htup hxs; injection hxs with hrest_eq
        injection htup with h1 htup; injection htup with h2
        subst h1 h2 hrest_eq
        have hsub := ih hrest hbody' ev'
        simp only [↓reduceIte] at hsub ⊢
        have ext_end : Heap.Extends m68
            (m68 ++ [.construct kexprEnum "Forall" [xty, v67, xm]]) := Heap.Extends.snoc _ _
        exact .forallE (by simp) ((ht.mono ev'.heap_extends).mono ext_end)
          (hsub.mono ext_end) (repKLevel_heapMono₂ (ev'.heap_extends.trans ext_end) hl)
      | .Cons_other (x_ty := xty) (x_m := xm) (v67 := v67) (m68 := m68)
          (ld12 := ld) (ev80 := ev') (hne152 := hlam_ne) (he160 := hr) (hm159 := hm) .. =>
        subst hr hm
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with htup hxs; injection hxs with hrest_eq
        injection htup with h1 htup; injection htup with h2
        subst h1 h2 hrest_eq
        have hsub := ih hrest hbody' ev'
        simp only [ite_eq_right hlam_ne] at hsub ⊢
        have ext_end : Heap.Extends m68
            (m68 ++ [.construct kexprEnum "Lam" [xty, v67, xm]]) := Heap.Extends.snoc _ _
        exact .lam (by simp) ((ht.mono ev'.heap_extends).mono ext_end)
          (hsub.mono ext_end) (repKLevel_heapMono₂ (ev'.heap_extends.trans ext_end) hl)

theorem stripPis_at_lt :
    ∀ (a rem : Nat) {e body mid : KExpr}
      {bs bs₁ : List (KExpr × Ix.Kernel.BinderMeta)},
      e.stripPis (a + (rem + 1)) = some (bs, body) →
      e.stripPis a = some (bs₁, mid) →
      ∃ rest, mid = .forallE (bs.getD a default).1 rest (bs.getD a default).2
  | 0, rem, .forallE ty rest m, body, mid, bs, bs₁, hs_all, hs_a => by
    rw [show 0 + (rem + 1) = rem + 1 by omega] at hs_all
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hs_all
    obtain ⟨⟨bs', body'⟩, _, hbs_eq⟩ := hs_all
    injection hbs_eq with hbs _
    subst hbs
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs_a
    obtain ⟨_, rfl⟩ := hs_a
    exact ⟨rest, rfl⟩
  | 0, rem, .bvar _, _, _, _, _, hs, _ | 0, rem, .fvar _ _, _, _, _, _, hs, _
  | 0, rem, .sort _, _, _, _, _, hs, _ | 0, rem, .const _ _, _, _, _, _, hs, _
  | 0, rem, .app _ _, _, _, _, _, hs, _ | 0, rem, .lam _ _ _, _, _, _, _, hs, _
  | 0, rem, .letE _ _ _ _, _, _, _, _, hs, _ | 0, rem, .lit _, _, _, _, _, hs, _
  | 0, rem, .proj _ _ _, _, _, _, _, hs, _ => nomatch hs
  | a + 1, rem, .forallE ty rest m, body, mid, bs, bs₁, hs_all, hs_a => by
    rw [show a + 1 + (rem + 1) = (a + (rem + 1)) + 1 by omega] at hs_all
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hs_all hs_a
    obtain ⟨⟨bs', body'⟩, hs_all', hbs_eq⟩ := hs_all
    injection hbs_eq with hbs _
    subst hbs
    obtain ⟨⟨bs₁', mid'⟩, hs_a', hmid_eq⟩ := hs_a
    injection hmid_eq with _ hmid
    subst hmid
    simpa [List.getD_cons_succ] using stripPis_at_lt a rem hs_all' hs_a'
  | a + 1, rem, .bvar _, _, _, _, _, hs, _ | a + 1, rem, .fvar _ _, _, _, _, _, hs, _
  | a + 1, rem, .sort _, _, _, _, _, hs, _ | a + 1, rem, .const _ _, _, _, _, _, hs, _
  | a + 1, rem, .app _ _, _, _, _, _, hs, _ | a + 1, rem, .lam _ _ _, _, _, _, _, hs, _
  | a + 1, rem, .letE _ _ _ _, _, _, _, _, hs, _ | a + 1, rem, .lit _, _, _, _, _, hs, _
  | a + 1, rem, .proj _ _ _, _, _, _, _, hs, _ => nomatch hs

/-- `KernelCheck::nat_field_dom(cty, np, i)` returns the `i`-th field domain `(bs.getD (nP + i) default).1`
at local binder depth `k + (nP + i)`, preserving `RawTm` without modifying the heap. -/
theorem nat_field_dom_rawTm_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k nP nF i : Nat} {Rcty Ecty rbody ebody : KExpr}
    {rcbs ecbs : List (KExpr × Ix.Kernel.BinderMeta)}
    {pcty r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hi : i < nF)
    (hlt : nP + nF < 4294967296)
    (hRaw : RawTm κ d Γ h k Rcty Ecty pcty)
    (hsR : Rcty.stripPis (nP + nF) = some (rcbs, rbody))
    (hsE : Ecty.stripPis (nP + nF) = some (ecbs, ebody))
    (ev : ObsFn W "KernelCheck::nat_field_dom"
      [pcty, .field (nP : F), .field (i : F)] h r h' cs) :
    h' = h ∧
      RawTm κ d Γ h (k + (nP + i))
        (rcbs.getD (nP + i) default).1 (ecbs.getD (nP + i) default).1 r := by
  rcases Obs.«KernelCheck::nat_field_dom».obs ev with
    ⟨_, _, _, v19, _, _, _, op40, ev17, ld11, rfl, rfl, _⟩
  rw [evalBinOp_add_nat nP i op40] at ev17
  obtain ⟨rfl, rbs₁, ebs₁, rmid, emid, hsR₁, hsE₁, hmid⟩ :=
    peel_n_foralls_rawTm_spec (nP + i) (by omega) hRaw ev17
  have hsplit : nP + nF = (nP + i) + ((nF - 1 - i) + 1) := by omega
  rw [hsplit] at hsR hsE
  obtain ⟨_, hrmid⟩ := stripPis_at_lt (nP + i) (nF - 1 - i) hsR hsR₁
  obtain ⟨_, hemid⟩ := stripPis_at_lt (nP + i) (nF - 1 - i) hsE hsE₁
  obtain ⟨Rt, _, _, T, _, _, hR_eq, hE_eq, hdom, _, _⟩ := hmid.forallE_of_load ld11
  rw [hrmid] at hR_eq; injection hR_eq with hRt_eq _ _
  rw [hemid] at hE_eq; injection hE_eq with hT_eq _ _
  subst hRt_eq hT_eq
  exact ⟨rfl, hdom⟩

/-! ### `nat_idx_at`, `nat_map_idx_at`, `nat_map_lift`, `nat_tele_at`, `nat_field_tele`, `nat_ih_pis`, `nat_minor_ty` -/

/-- `KernelCheck::nat_idx_at` computes `Ix.Kernel.structIdxAt nF o i l m E`, moving local binder
depth from `k_base + i + m` to `k_base + o + nF + l + m`. -/
theorem nat_idx_at_spec {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {k_base nF o i l m : Nat} {E : KExpr} {pe r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hi : i ≤ nF)
    (hlt : k_base + o + nF + l + m < 4294967296)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hE : Tm κ 0 Γ₀ h (k_base + i + m) E pe)
    (ev : ObsFn W "KernelCheck::nat_idx_at"
      [.field (nF : F), .field (o : F), .field (i : F), .field (l : F), .field (m : F), pe]
      h r h' cs) :
    Tm κ 0 Γ₀ h' (k_base + o + nF + l + m) (Ix.Kernel.structIdxAt nF o i l m E) r := by
  rcases Obs.«KernelCheck::nat_idx_at».obs ev with
    ⟨cs4, v7, v9, m11, cs19, v23, x38, x77, op53, op45, ev21, op92, op84, ev6, hc⟩
  subst hc
  rw [evalBinOp_sub_nat hi op53] at op45
  rw [evalBinOp_add_nat (nF - i) l op45] at ev21
  rw [evalBinOp_add_nat nF l op92] at op84
  rw [evalBinOp_add_nat (nF + l) m op84] at ev6
  have hbnd1 : IxVM.Consistency.Bounded cs19 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hbnd2 : IxVM.Consistency.Bounded cs4 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have h1 := expr_lift_local_spec (by omega) (by omega) (by omega) hbnd1 hE ev21
  have h1' : Tm κ 0 Γ₀ m11 (k_base + nF + l + m) (E.liftLooseBVars (nF - i + l) m) v7 := by
    rwa [show k_base + nF + l + m = (k_base + i + m) + (nF - i + l) by omega]
  have h2 := expr_lift_local_spec (by omega) (by omega) (by omega) hbnd2 h1' ev6
  rwa [show k_base + o + nF + l + m = (k_base + nF + l + m) + o by omega]

theorem nat_map_idx_at_spec {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {k_base nF o i l m : Nat} (hi : i ≤ nF) (hlt : k_base + o + nF + l + m < 4294967296) :
    ∀ {es : List KExpr} {pes r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      IxVM.Consistency.Bounded cs →
      RepList kexprListEnum (fun h E p => Tm κ 0 Γ₀ h (k_base + i + m) E p) h es pes →
      ObsFn W "KernelCheck::nat_map_idx_at"
        [.field (nF : F), .field (o : F), .field (i : F), .field (l : F), .field (m : F), pes]
        h r h' cs →
      RepList kexprListEnum
        (fun h E p => Tm κ 0 Γ₀ h (k_base + o + nF + l + m) E p)
        h' (es.map (Ix.Kernel.structIdxAt nF o i l m)) r := by
  intro es
  induction es with
  | nil =>
    intro pes r h h' cs _ hes ev
    match Obs.«KernelCheck::nat_map_idx_at».obs ev with
    | .Nil (he24 := hr) (hm23 := hm) .. =>
      subst hr hm
      exact .nil (by simp)
    | .Cons (ld12 := ld) .. =>
      have ld' : loadValue h pes = .ok (.construct kexprListEnum "Cons" [_, _]) := ld
      cases hes with | nil cell => exact (load_cell_ne cell ld' (by decide)).elim
  | cons Ea Eas ih =>
    intro pes r h h' cs hbnd hes ev
    match Obs.«KernelCheck::nat_map_idx_at».obs ev with
    | .Nil (ld12 := ld) .. =>
      have ld' : loadValue h pes = .ok (.construct kexprListEnum "Nil" []) := ld
      cases hes with | cons cell _ _ => exact (load_cell_ne cell ld' (by decide)).elim
    | .Cons (v54 := v54) (v55 := v55) (cs65 := cs1) (m117 := m117) (cs125 := cs2)
        (ld12 := ld) (he50 := hr) (hm49 := hm) (ev67 := ev1) (ev127 := ev2) (hc176 := hc) .. =>
      subst hc hr hm
      obtain ⟨Ea', Eas', heq, ha, has⟩ := RepList.cons_of_load hes ld
      injection heq with h1 h2; subst h1 h2
      have hbnd1 : IxVM.Consistency.Bounded cs1 :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hbnd2 : IxVM.Consistency.Bounded cs2 :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hhd := nat_idx_at_spec hi hlt hbnd1 ha ev1
      have htl := ih hbnd2 (has.mono ev1.heap_extends) ev2
      have ext_end : Heap.Extends m117
          (m117 ++ [.construct kexprListEnum "Cons" [v54, v55]]) := Heap.Extends.snoc _ _
      exact .cons (by simp) ((hhd.mono ev2.heap_extends).mono ext_end) (htl.mono ext_end)

theorem nat_map_lift_spec {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {k shift cut : Nat} (hcut_le : cut ≤ k)
    (hshift_lt : shift < 4611686018427387904) (hcut_lt : cut < 4294967296) :
    ∀ {es : List KExpr} {pes r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      IxVM.Consistency.Bounded cs →
      RepList kexprListEnum (fun h E p => Tm κ 0 Γ₀ h k E p) h es pes →
      ObsFn W "KernelCheck::nat_map_lift"
        [pes, .field (shift : F), .field (cut : F)] h r h' cs →
      RepList kexprListEnum
        (fun h E p => Tm κ 0 Γ₀ h (k + shift) E p)
        h' (es.map (Expr.liftLooseBVars shift cut)) r := by
  intro es
  induction es with
  | nil =>
    intro pes r h h' cs _ hes ev
    match Obs.«KernelCheck::nat_map_lift».obs ev with
    | .Nil (he24 := hr) (hm23 := hm) .. =>
      subst hr hm
      exact .nil (by simp)
    | .Cons (ld12 := ld) .. =>
      have ld' : loadValue h pes = .ok (.construct kexprListEnum "Cons" [_, _]) := ld
      cases hes with | nil cell => exact (load_cell_ne cell ld' (by decide)).elim
  | cons Ea Eas ih =>
    intro pes r h h' cs hbnd hes ev
    match Obs.«KernelCheck::nat_map_lift».obs ev with
    | .Nil (ld12 := ld) .. =>
      have ld' : loadValue h pes = .ok (.construct kexprListEnum "Nil" []) := ld
      cases hes with | cons cell _ _ => exact (load_cell_ne cell ld' (by decide)).elim
    | .Cons (v54 := v54) (v55 := v55) (cs65 := cs1) (m93 := m93) (cs101 := cs2)
        (ld12 := ld) (he50 := hr) (hm49 := hm) (ev67 := ev1) (ev103 := ev2) (hc128 := hc) .. =>
      subst hc hr hm
      obtain ⟨Ea', Eas', heq, ha, has⟩ := RepList.cons_of_load hes ld
      injection heq with h1 h2; subst h1 h2
      have hbnd1 : IxVM.Consistency.Bounded cs1 :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hbnd2 : IxVM.Consistency.Bounded cs2 :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hhd := expr_lift_local_spec hcut_le hshift_lt hcut_lt hbnd1 ha ev1
      have htl := ih hbnd2 (has.mono ev1.heap_extends) ev2
      have ext_end : Heap.Extends m93
          (m93 ++ [.construct kexprListEnum "Cons" [v54, v55]]) := Heap.Extends.snoc _ _
      exact .cons (by simp) ((hhd.mono ev2.heap_extends).mono ext_end) (htl.mono ext_end)

theorem nat_tele_at_go {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {k_base nF o i l : Nat} {ℓ : KLevel} (hi : i ≤ nF) :
    ∀ {tele_rem : List (KExpr × Ix.Kernel.BinderMeta)} (m : Nat)
      {ppw ptele r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      k_base + o + nF + l + m + tele_rem.length < 4294967296 →
      IxVM.Consistency.Bounded cs →
      RepKLevel h ℓ ppw →
      TeleRep κ 0 Γ₀ h (k_base + i + m) tele_rem ptele →
      ObsFn W "KernelCheck::nat_tele_at"
        [.field (nF : F), .field (o : F), .field (i : F), .field (l : F),
          ppw, ptele, .field (m : F)] h r h' cs →
      TeleRep κ 0 Γ₀ h' (k_base + o + nF + l + m)
        ((List.range tele_rem.length).map fun idx =>
          (Ix.Kernel.structIdxAt nF o i l (m + idx) (tele_rem.getD idx default).1, bmeta ℓ)) r := by
  intro tele_rem
  induction tele_rem with
  | nil =>
    intro m ppw ptele r h h' cs _ _ _ htele ev
    match Obs.«KernelCheck::nat_tele_at».obs ev with
    | .Nil (he24 := hr) (hm23 := hm) .. =>
      subst hr hm
      exact .nil (by simp)
    | .Cons (ld12 := ld) .. =>
      cases htele with | nil cell => exact (load_cell_ne cell ld (by decide)).elim
  | cons b rest ih =>
    intro m ppw ptele r h h' cs hlt hbnd hpw htele ev
    cases htele with
    | cons cell ht _ hrest =>
      match Obs.«KernelCheck::nat_tele_at».obs ev with
      | .Nil (ld12 := ld) .. => exact (load_cell_ne cell ld (by decide)).elim
      | .Cons (v82 := v82) (v91 := v91) (cs102 := cs1) (m161 := m161) (cs169 := cs2)
          (ld12 := ld) (he77 := hr) (hm76 := hm) (ev104 := ev1) (op234 := op)
          (ev171 := ev2) (hc236 := hc) .. =>
        subst hc hr hm
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with htup hxs; injection hxs with hrest_eq
        injection htup with h1 _
        subst h1 hrest_eq
        rw [evalBinOp_add_one m op] at ev2
        have hbnd1 : IxVM.Consistency.Bounded cs1 :=
          RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
        have hbnd2 : IxVM.Consistency.Bounded cs2 :=
          RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
        have hhd := nat_idx_at_spec hi (by simp at hlt; omega) hbnd1 ht ev1
        have hrest' : TeleRep κ 0 Γ₀ _ (k_base + i + (m + 1)) rest _ := by
          simpa [Nat.add_assoc] using hrest.mono ev1.heap_extends
        have htl := ih (m + 1)
          (by simp at hlt; omega) hbnd2
          (repKLevel_heapMono₂ ev1.heap_extends hpw) hrest' ev2
        have ext_end : Heap.Extends m161
            (m161 ++ [.construct teleListEnum "Cons" [.tuple [v91, ppw], v82]]) :=
          Heap.Extends.snoc _ _
        simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
          Nat.add_zero, List.getD_cons_zero]
        have hmap_eq :
            List.map
              ((fun idx => (Ix.Kernel.structIdxAt nF o i l (m + idx)
                (((_, bmeta _) :: rest).getD idx default).1, bmeta ℓ)) ∘ (· + 1))
              (List.range rest.length) =
            List.map
              (fun idx => (Ix.Kernel.structIdxAt nF o i l (m + 1 + idx)
                (rest.getD idx default).1, bmeta ℓ))
              (List.range rest.length) := by
          apply List.map_congr_left
          intro idx _
          simp [Function.comp_def, Nat.add_assoc, List.getD_cons_succ]
        rw [hmap_eq]
        have htl' : TeleRep κ 0 Γ₀ _ (k_base + o + nF + l + m + 1) _ v82 := by
          simpa [Nat.add_assoc] using htl.mono ext_end
        exact .cons (by simp) ((hhd.mono ev2.heap_extends).mono ext_end)
          (repKLevel_heapMono₂ (ev1.heap_extends.trans (ev2.heap_extends.trans ext_end)) hpw)
          htl'

/-- `KernelCheck::nat_tele_at` at `k = 0` computes `Ix.Kernel.structTeleAt nF o i l ℓ.zeronessOf tele`. -/
theorem nat_tele_at_spec {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {k_base nF o i l : Nat} {ℓ : KLevel} {tele : List (KExpr × Ix.Kernel.BinderMeta)}
    {ppw ptele r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hi : i ≤ nF)
    (hlt : k_base + o + nF + l + tele.length < 4294967296)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hpw : RepKLevel h ℓ ppw)
    (htele : TeleRep κ 0 Γ₀ h (k_base + i) tele ptele)
    (ev : ObsFn W "KernelCheck::nat_tele_at"
      [.field (nF : F), .field (o : F), .field (i : F), .field (l : F),
        ppw, ptele, .field 0] h r h' cs) :
    TeleRep κ 0 Γ₀ h' (k_base + o + nF + l)
      (Ix.Kernel.structTeleAt nF o i l ℓ.zeronessOf tele) r := by
  have ev' : ObsFn W "KernelCheck::nat_tele_at"
      [.field (nF : F), .field (o : F), .field (i : F), .field (l : F),
        ppw, ptele, .field ((0 : Nat) : F)] h r h' cs := by
    simpa using ev
  have hgo := nat_tele_at_go hi 0 (by omega) hbnd hpw (by simpa using htele) ev'
  simpa [Ix.Kernel.structTeleAt, bmeta] using hgo

/-- `KernelCheck::nat_field_tele(cty, np, i)` on a strictly-positive recursive field `i < nF`
returns `(structFieldTeleOf Ecty nP nF i, structFieldIdxOf Ecty nP nF i)`. -/
theorem nat_field_tele_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {T : KKey} {k nP nF i : Nat} {Rcty Ecty rbody ebody : KExpr}
    {rcbs ecbs : List (KExpr × Ix.Kernel.BinderMeta)}
    {pcty r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hi : i < nF)
    (hlt : nP + nF < 4294967296)
    (hRaw : RawTm κ d Γ h k Rcty Ecty pcty)
    (hsR : Rcty.stripPis (nP + nF) = some (rcbs, rbody))
    (hsE : Ecty.stripPis (nP + nF) = some (ecbs, ebody))
    (hspine : RawRecSpine T (rcbs.getD (nP + i) default).1 (ecbs.getD (nP + i) default).1)
    (ev : ObsFn W "KernelCheck::nat_field_tele"
      [pcty, .field (nP : F), .field (i : F)] h r h' cs) :
    ∃ ptele pidx,
      r = .tuple [ptele, pidx] ∧
      TeleRep κ d Γ h' (k + (nP + i)) (Ix.Kernel.structFieldTeleOf Ecty nP nF i) ptele ∧
      RepList kexprListEnum
        (fun h E p => Tm κ d Γ h (k + (nP + i) + (Ix.Kernel.structFieldTeleOf Ecty nP nF i).length) E p)
        h' (Ix.Kernel.structFieldIdxOf Ecty nP nF i) pidx := by
  rcases Obs.«KernelCheck::nat_field_tele».obs ev with
    ⟨m2, _, v15, m17, _, x_tele, x_fb, m66, _, w90, x_fargs, v104, m114, _,
      ev27, ev14, ev78, rfl, ev124, rfl, _⟩
  obtain ⟨rfl, hdom⟩ := nat_field_dom_rawTm_spec hi hlt hRaw hsR hsE ev27
  obtain ⟨us, rAs, eAs, hpb, htele_rep, hfb_raw⟩ := nat_pi_binders_rawRecSpine_spec hspine hdom ev14
  obtain ⟨hd, sp, Rh, Eh, Ras, Eas, htup, hH, hEas, _, hR_eq, hE_eq, hnot_app⟩ :=
    collect_spine_rawTm_spec hfb_raw ev78
  injection htup with hl; injection hl with h1 hl; injection hl with h2
  subst h1 h2
  have hRh_args : Rh.getAppArgs = [] := by
    cases Rh with
    | app f a => exact (hnot_app f a rfl).elim
    | bvar _ | fvar _ _ | sort _ | const _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ _
    | lit _ | proj _ _ _ => rfl
  have hRh_fn : Rh = .const T us := by
    have hfn := congrArg Expr.getAppFn hR_eq
    rw [getAppFn_mkAppN, getAppFn_mkAppN] at hfn
    cases Rh with
    | app f a => exact (hnot_app f a rfl).elim
    | bvar _ | fvar _ _ | sort _ | const _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ _
    | lit _ | proj _ _ _ => exact hfn.symm
  subst hRh_fn
  have hEh := hH.const_left_inv
  subst hEh
  obtain ⟨-, rfl, rfl⟩ := mkAppN_const_inj hE_eq
  obtain ⟨_, hdrop, rfl⟩ := kexpr_list_drop_spec (by omega) ev124 hEas
  have htele_eq : Ix.Kernel.structFieldTeleOf Ecty nP nF i =
      (ecbs.getD (nP + i) default).1.piBinders.1 := by
    simp [Ix.Kernel.structFieldTeleOf, hsE]
  have hidx_eq : Ix.Kernel.structFieldIdxOf Ecty nP nF i = Eas.drop nP := by
    unfold Ix.Kernel.structFieldIdxOf
    rw [hsE]
    simp only [Option.map_some, Option.getD_some]
    have hpb2 : ((ecbs.getD (nP + i) default).1.piBinders).2 = Expr.mkAppN (.const T us) Eas :=
      congrArg Prod.snd hpb
    rw [hpb2, getAppArgs_mkAppN_const]
  rw [htele_eq, hidx_eq]
  exact ⟨x_tele, v104, rfl, htele_rep.mono ev78.heap_extends, hdrop⟩

theorem stripPis_binder_lt_bound :
    ∀ (n k : Nat) {e body : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {b : Nat},
      e.looseBVarsBounded b = true →
      e.stripPis n = some (bs, body) →
      k < bs.length →
      (bs.getD k default).1.looseBVarsBounded (b + k) = true
  | 0, _, _, _, _, _, _, hs, hk => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, _⟩; simp at hk
  | n + 1, 0, .forallE ty rest m, body, bs, b, hbnd, hs, _ => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
    obtain ⟨⟨bs', _⟩, _, hbs⟩ := hs
    injection hbs with hbs_eq _; subst hbs_eq
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbnd
    simpa using hbnd.1
  | n + 1, k + 1, .forallE ty rest m, body, bs, b, hbnd, hs, hk => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
    obtain ⟨⟨bs', body'⟩, hs', hbs⟩ := hs
    injection hbs with hbs_eq _; subst hbs_eq
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbnd
    have hrest : rest.looseBVarsBounded (b + 1) = true := hbnd.2
    have ih := stripPis_binder_lt_bound n k hrest hs' (by simp at hk; omega)
    simpa [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm 1] using ih
  | _ + 1, _, .bvar _, _, _, _, _, hs, _ | _ + 1, _, .fvar _ _, _, _, _, _, hs, _
  | _ + 1, _, .sort _, _, _, _, _, hs, _ | _ + 1, _, .const _ _, _, _, _, _, hs, _
  | _ + 1, _, .app _ _, _, _, _, _, hs, _ | _ + 1, _, .lam _ _ _, _, _, _, _, hs, _
  | _ + 1, _, .letE _ _ _ _, _, _, _, _, hs, _ | _ + 1, _, .lit _, _, _, _, _, hs, _
  | _ + 1, _, .proj _ _ _, _, _, _, _, hs, _ => nomatch hs

theorem structPsAt_zero_eq_structTeleVars (m : Nat) :
    Ix.Kernel.structPsAt (md := .anon) 0 m = Ix.Kernel.structTeleVars m := by
  simp [Ix.Kernel.structPsAt, Ix.Kernel.structTeleVars]

/-- `KernelCheck::nat_ih_pis` builds `Ix.Kernel.structIhPis` on `Ecty`. -/
theorem nat_ih_pis_spec {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {T : KKey} {nP nF o : Nat} {ℓ : KLevel} {Rcty Ecty rbody ebody : KExpr}
    {rcbs ecbs : List (KExpr × Ix.Kernel.BinderMeta)}
    (ho : 1 ≤ o)
    (hsR : Rcty.stripPis (nP + nF) = some (rcbs, rbody))
    (hsE : Ecty.stripPis (nP + nF) = some (ecbs, ebody)) :
    ∀ {is : List Nat} (l : Nat) {body : KExpr}
      {ppw pcty pis pbody r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ i ∈ is, i < nF ∧
        RawRecSpine T (rcbs.getD (nP + i) default).1 (ecbs.getD (nP + i) default).1 ∧
        nP + o + nF + l + is.length + (Ix.Kernel.structFieldTeleOf Ecty nP nF i).length <
          4294967296) →
      nP + o + nF + l + is.length < 4294967296 →
      IxVM.Consistency.Bounded cs →
      RepKLevel h ℓ ppw →
      RawTm κ 0 Γ₀ h 0 Rcty Ecty pcty →
      RepList fieldListEnum (fun _ idx v => v = .field (idx : F)) h is pis →
      Tm κ 0 Γ₀ h (nP + o + nF + l + is.length) body pbody →
      ObsFn W "KernelCheck::nat_ih_pis"
        [.field (nF : F), .field (o : F), ppw, pcty, .field (nP : F),
          pis, .field (l : F), pbody] h r h' cs →
      Tm κ 0 Γ₀ h' (nP + o + nF + l)
        (Ix.Kernel.structIhPis nF o ℓ.zeronessOf
          (Ix.Kernel.structFieldTeleOf Ecty nP nF)
          (Ix.Kernel.structFieldIdxOf Ecty nP nF) is l body) r := by
  intro is
  induction is with
  | nil =>
    intro l body ppw pcty pis pbody r h h' cs _ _ _ _ _ his hbody ev
    match Obs.«KernelCheck::nat_ih_pis».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. =>
      subst hr hh
      simpa [Ix.Kernel.structIhPis] using hbody
    | .Cons (ld12 := ld) .. =>
      have ld' : loadValue h pis = .ok (.construct fieldListEnum "Cons" [_, _]) := ld
      cases his with | nil cell => exact (load_cell_ne cell ld' (by decide)).elim
  | cons i rest ih =>
    intro l body ppw pcty pis pbody r h h' cs hall hlt_base hbnd hpw hRaw his hbody ev
    match Obs.«KernelCheck::nat_ih_pis».obs ev with
    | .Nil (ld12 := ld) .. =>
      have ld' : loadValue h pis = .ok (.construct fieldListEnum "Nil" []) := ld
      cases his with | cons cell _ _ => exact (load_cell_ne cell ld' (by decide)).elim
    | .Cons (m42 := m42) (x_tele := x_tele) (x_idx := x_idx) (v92 := v92) (m93 := m93)
        (v114 := v114) (m115 := m115) (v129 := v129) (m131 := m131) (v143 := v143)
        (x150 := x150) (x158 := x158) (x166 := x166) (m187 := m187)
        (v213 := v213) (m214 := m214) (v228 := v228) (m230 := m230) (v242 := v242)
        (x249 := x249) (x257 := x257) (x265 := x265) (m286 := m286)
        (v297 := v297) (m300 := m300) (cs308 := cs_map)
        (v366 := v366) (m367 := m367) (v380 := v380) (m384 := m384) (cs392 := cs_ta)
        (v472 := v472) (m482 := m482) (cs490 := cs_rec) (v499 := v499)
        (ld12 := ld) (ev54 := ev_ft) (ev105 := ev_len) (hm139 := hm131)
        (op181 := op181) (op173 := op173) (op165 := op165) (op157 := op157)
        (ev197 := ev_ps) (ev127 := ev_app1) (hm238 := hm230)
        (op280 := op280) (op272 := op272) (op264 := op264) (op256 := op256)
        (ev310 := ev_map) (ev296 := ev_snoc) (ev226 := ev_app2)
        (ev394 := ev_ta) (ev379 := ev_mk) (he467 := hr) (hm466 := hm_end)
        (op556 := op_l1) (ev492 := ev_rec) (hc572 := hc) .. =>
      subst hc hr hm_end
      obtain ⟨i', rest', heq, hi_eq, hrest_rep⟩ := RepList.cons_of_load his ld
      injection heq with h1 h2; subst h1 h2; subst hi_eq
      obtain ⟨hi_lt, hspine_i, hlt_m⟩ := hall i List.mem_cons_self
      let tele_i := Ix.Kernel.structFieldTeleOf Ecty nP nF i
      let idx_i := Ix.Kernel.structFieldIdxOf Ecty nP nF i
      let m := tele_i.length
      have hlt_m' : nP + o + nF + l + m < 4294967296 := by
        dsimp only [m, tele_i]
        simp only [List.length_cons] at hlt_m
        omega
      obtain ⟨ptele, pidx, htup_ft, htele_m42, hidx_m42⟩ :=
        nat_field_tele_spec hi_lt (by omega) hRaw hsR hsE hspine_i ev_ft
      injection htup_ft with hl_ft; injection hl_ft with h1 hl_ft; injection hl_ft with h2
      subst h1 h2
      obtain ⟨hv92, hm93⟩ := tele_length_spec ev_len htele_m42
      rw [hm93] at hm131 ev_app1
      have hv92' : v92 = .field (m : F) := hv92
      rw [hv92'] at op157 ev_ps op256 ev_map
      -- Arithmetic for `v143 = nF - 1 - i + l + m`
      rw [evalBinOp_sub_nat (by omega : 1 ≤ nF) op181] at op173
      rw [evalBinOp_sub_nat (by omega : i ≤ nF - 1) op173] at op165
      rw [evalBinOp_add_nat (nF - 1 - i) l op165] at op157
      rw [evalBinOp_add_nat (nF - 1 - i + l) m op157] at hm131
      -- Arithmetic for `v242 = nF + o - 1 + l + m`
      rw [evalBinOp_add_nat nF o op280] at op272
      rw [evalBinOp_sub_nat (by omega : 1 ≤ nF + o) op272] at op264
      rw [evalBinOp_add_nat (nF + o - 1) l op264] at op256
      rw [evalBinOp_add_nat (nF + o - 1 + l) m op256] at hm230
      -- `f_i a⃗` = `Expr.mkAppN (.bvar (nF - 1 - i + l + m)) (structTeleVars m)`
      have ext_m131 : Heap.Extends m42 m131 := by rw [hm131]; exact Heap.Extends.snoc _ _
      have hbvar_fi : Tm κ 0 Γ₀ m131 (nP + o + nF + l + m)
          (.bvar (nF - 1 - i + l + m)) (.ptr (.enum kexprEnum) m42.length) := by
        rw [hm131]; exact tm_bvarLocal_nat (by simp) (by omega) (by omega)
      have hps_m := nat_ps_at_spec m 0 (nP + o + nF + l + m) (by omega) hlt_m' ev_ps
      rw [structPsAt_zero_eq_structTeleVars] at hps_m
      have hfi_app := nat_app_n_spec (hbvar_fi.mono ev_ps.heap_extends) hps_m ev_app1
      -- `motive e⃗_i(a⃗) (f_i a⃗)`
      have ext_m230 : Heap.Extends m115 m230 := by rw [hm230]; exact Heap.Extends.snoc _ _
      have hbvar_mot : Tm κ 0 Γ₀ m230 (nP + o + nF + l + m)
          (.bvar (nF + o - 1 + l + m)) (.ptr (.enum kexprEnum) m115.length) := by
        rw [hm230]; exact tm_bvarLocal_nat (by simp) (by omega) (by omega)
      have ext_42_230 := ext_m131.trans (ev_ps.heap_extends.trans
        (ev_app1.heap_extends.trans ext_m230))
      have hidx_230 : RepList kexprListEnum (fun h E p => Tm κ 0 Γ₀ h (nP + i + m) E p)
          m230 idx_i x_idx := by
        simpa [Nat.zero_add] using hidx_m42.mono ext_42_230
      have hbnd_map : IxVM.Consistency.Bounded cs_map :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hmap_idx := nat_map_idx_at_spec (by omega : i ≤ nF) hlt_m' hbnd_map hidx_230 ev_map
      have hsnoc := SubstAux.ksnoc (R := fun h E p => Tm κ 0 Γ₀ h (nP + o + nF + l + m) E p)
        (fun _ _ _ _ ext r => Tm.mono ext r) ev_snoc hmap_idx
        ((hfi_app.mono ext_m230).mono ev_map.heap_extends)
      have hmot_app := nat_app_n_spec
        ((hbvar_mot.mono ev_map.heap_extends).mono ev_snoc.heap_extends) hsnoc ev_app2
      -- `mkPisOf (structTeleAt nF o i l pw tele_i) (...)`
      have ext_h_214 := ev_ft.heap_extends.trans (ext_42_230.trans
        (ev_map.heap_extends.trans (ev_snoc.heap_extends.trans ev_app2.heap_extends)))
      have ext_42_214 := ext_42_230.trans
        (ev_map.heap_extends.trans (ev_snoc.heap_extends.trans ev_app2.heap_extends))
      have hbnd_ta : IxVM.Consistency.Bounded cs_ta :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hta := nat_tele_at_spec (by omega : i ≤ nF) hlt_m' hbnd_ta
        (repKLevel_heapMono₂ ext_h_214 hpw)
        (by simpa [Nat.zero_add] using htele_m42.mono ext_42_214) ev_ta
      have hta_len : (Ix.Kernel.structTeleAt nF o i l ℓ.zeronessOf tele_i).length = m := by
        simp [Ix.Kernel.structTeleAt, m]
      have hmot_app' : Tm κ 0 Γ₀ m384
          (nP + o + nF + l + (Ix.Kernel.structTeleAt nF o i l ℓ.zeronessOf tele_i).length) _ v213 := by
        rw [hta_len]; exact hmot_app.mono ev_ta.heap_extends
      have hih_dom := nat_mk_binders_spec hta hmot_app' ev_mk
      simp only [↓reduceIte] at hih_dom
      -- Recursive `nat_ih_pis` on `rest` at `l + 1`
      rw [evalBinOp_add_one l op_l1] at ev_rec
      have ext_h_367 := ext_h_214.trans (ev_ta.heap_extends.trans ev_mk.heap_extends)
      have hbnd_rec : IxVM.Consistency.Bounded cs_rec :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hbody_367 : Tm κ 0 Γ₀ m367 (nP + o + nF + (l + 1) + rest.length) body pbody := by
        rw [show nP + o + nF + (l + 1) + rest.length = nP + o + nF + l + (i :: rest).length by
          simp; omega]
        exact hbody.mono ext_h_367
      have hall_rest : ∀ k ∈ rest, k < nF ∧
          RawRecSpine T (rcbs.getD (nP + k) default).1 (ecbs.getD (nP + k) default).1 ∧
          nP + o + nF + (l + 1) + rest.length +
            (Ix.Kernel.structFieldTeleOf Ecty nP nF k).length < 4294967296 := by
        intro k hk
        obtain ⟨hk1, hk2, hk3⟩ := hall k (List.mem_cons_of_mem _ hk)
        exact ⟨hk1, hk2, by simp only [List.length_cons] at hk3; omega⟩
      have hrest_ih := ih (l + 1) hall_rest
        (by simp only [List.length_cons] at hlt_base; omega)
        hbnd_rec (repKLevel_heapMono₂ ext_h_367 hpw)
        (hRaw.mono ext_h_367) (hrest_rep.mono ext_h_367) hbody_367 ev_rec
      have ext_end : Heap.Extends m482
          (m482 ++ [.construct kexprEnum "Forall" [v366, v472, ppw]]) := Heap.Extends.snoc _ _
      exact .forallE (by simp)
        ((hih_dom.mono ev_rec.heap_extends).mono ext_end)
        (hrest_ih.mono ext_end)
        (repKLevel_heapMono₂ (ext_h_367.trans (ev_rec.heap_extends.trans ext_end)) hpw)

/-- Circuit-frame minor premise generator (`structMinorTyR` instantiated at concrete `clvls : List KLevel`). -/
def cMinorTy (C : KKey) (clvls : List KLevel) (nP nF o : Nat) (pw : Ix.Kernel.PropWhen)
    (cty : KExpr) (recIdx : List Nat) : Option KExpr :=
  (cty.stripPis nP).bind fun q =>
  (q.2.stripPis nF).bind fun r =>
    Expr.replacePisPw pw nF (q.2.liftLooseBVars o 0)
      (Ix.Kernel.structIhPis nF o pw (Ix.Kernel.structFieldTeleOf cty nP nF)
        (Ix.Kernel.structFieldIdxOf cty nP nF) recIdx 0
        ((Expr.mkAppN (.bvar (nF + o - 1))
          ((r.2.getAppArgs.drop nP).map (Expr.liftLooseBVars o nF) ++
            [Expr.mkAppN (.const C clvls)
              (Ix.Kernel.structPsAt (o + nF) nP ++ Ix.Kernel.structPsAt 0 nF)])).liftLooseBVars
          recIdx.length 0))

theorem posOf_structMinorTyR (rlps : List LevelParam) (C : KKey) (lps : List LevelParam)
    (nP nF o : Nat) (pw₀ : Ix.Kernel.PropWhen) (cty₀ : KExpr) (recIdx : List Nat)
    (hs : ∃ cbs cbody, cty₀.stripPis (nP + nF) = some (cbs, cbody))
    (hrec : ∀ i ∈ recIdx, i < nF) :
    (Ix.Kernel.structMinorTyR C lps nP nF o pw₀ cty₀ recIdx).map (posOf rlps) =
      cMinorTy C ((lps.map .param).map (Level.subst rlps (posLevels rlps))) nP nF o
        (Level.substPW rlps (posLevels rlps) pw₀) (posOf rlps cty₀) recIdx := by
  obtain ⟨cbs, cbody, hstrip_all⟩ := hs
  obtain ⟨bsP, q2, bsF, hstripP, hstripF, rfl, hlenP⟩ := stripPis_split nP nF hstrip_all
  have hlenF : bsF.length = nF := stripPis_length nF hstripF
  have hfg : ∀ i ∈ recIdx,
      Ix.Kernel.structFieldTeleOf (posOf rlps cty₀) nP nF i =
        (Ix.Kernel.structFieldTeleOf cty₀ nP nF i).map
          (fun b => (b.1.instantiateLevelParams rlps (posLevels rlps),
            { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw })) ∧
      Ix.Kernel.structFieldIdxOf (posOf rlps cty₀) nP nF i =
        (Ix.Kernel.structFieldIdxOf cty₀ nP nF i).map
          (·.instantiateLevelParams rlps (posLevels rlps)) := by
    intro i hi
    have hlt_i : nP + i < (bsP ++ bsF).length := by
      rw [List.length_append, hlenP, hlenF]; have := hrec i hi; omega
    exact ⟨ilp_structFieldTeleOf rlps (posLevels rlps) cty₀ nP nF i ⟨_, _, hstrip_all, hlt_i⟩,
      ilp_structFieldIdxOf rlps (posLevels rlps) cty₀ nP nF i ⟨_, _, hstrip_all, hlt_i⟩⟩
  unfold Ix.Kernel.structMinorTyR cMinorTy posOf
  rw [hstripP, ilp_stripPis rlps (posLevels rlps) nP hstripP]
  simp only [Option.bind_some]
  rw [hstripF, ilp_stripPis rlps (posLevels rlps) nF hstripF]
  simp only [Option.bind_some]
  rw [option_map_ilp_replacePisPw, ilp_liftLooseBVars,
    ilp_structIhPis rlps (posLevels rlps) nF o pw₀ _ _ _ _ recIdx 0 _ hfg,
    ilp_liftLooseBVars, ilp_mkAppN, List.map_append, List.map_map, List.map_cons, List.map_nil,
    ilp_getAppArgs, ← List.map_drop, List.map_map]
  have hmap_lift :
      List.map (Expr.instantiateLevelParams rlps (posLevels rlps) ∘ Expr.liftLooseBVars o nF)
        (cbody.getAppArgs.drop nP) =
      List.map (Expr.liftLooseBVars o nF ∘ Expr.instantiateLevelParams rlps (posLevels rlps))
        (cbody.getAppArgs.drop nP) := by
    apply List.map_congr_left
    intro e _
    simp [Function.comp_def, ilp_liftLooseBVars]
  have hspine_eq :
      (Ix.Kernel.structCtorSpineAt C lps o nP nF).instantiateLevelParams rlps (posLevels rlps) =
      Expr.mkAppN (.const C ((lps.map .param).map (Level.subst rlps (posLevels rlps))))
        (Ix.Kernel.structPsAt (o + nF) nP ++ Ix.Kernel.structPsAt 0 nF) := by
    unfold Ix.Kernel.structCtorSpineAt
    rw [ilp_mkAppN, List.map_append, ilp_structPsAt]
    simp only [Expr.instantiateLevelParams, Ix.Kernel.structPsAt, Nat.zero_add, List.map_map]
    rfl
  rw [hmap_lift, hspine_eq]
  rfl

/-- `KernelCheck::nat_minor_ty` builds `cMinorTy C clvls nP nF o ℓ.zeronessOf Ecty recIdx`. -/
theorem nat_minor_ty_spec {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {T C : KKey} {bC : Bytes.Address} {clvls : List KLevel} {nP nF o : Nat} {ℓ : KLevel}
    {Rcty Ecty : KExpr} {rus eus : List KLevel} {rargs eargs : List KExpr}
    {rcbs ecbs : List (KExpr × Ix.Kernel.BinderMeta)} {recIdx : List Nat}
    {pcprj plps ppw pcty prec r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hC : κ (ixAddr bC) = C)
    (ho : 1 ≤ o)
    (hsR : Rcty.stripPis (nP + nF) = some (rcbs, Expr.mkAppN (.const T rus) rargs))
    (hsE : Ecty.stripPis (nP + nF) = some (ecbs, Expr.mkAppN (.const T eus) eargs))
    (hall : ∀ i ∈ recIdx, i < nF ∧
      RawRecSpine T (rcbs.getD (nP + i) default).1 (ecbs.getD (nP + i) default).1 ∧
      nP + o + nF + recIdx.length + (Ix.Kernel.structFieldTeleOf Ecty nP nF i).length < 4294967296)
    (hlt_base : nP + o + nF + recIdx.length < 4294967296)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hcprj : Bytes.RepAddressRef addrTy h bC pcprj)
    (hlps : RepKLevelList h clvls plps)
    (hpw : RepKLevel h ℓ ppw)
    (hRaw : RawTm κ 0 Γ₀ h 0 Rcty Ecty pcty)
    (hrec : RepList fieldListEnum (fun _ idx v => v = .field (idx : F)) h recIdx prec)
    (ev : ObsFn W "KernelCheck::nat_minor_ty"
      [pcprj, plps, .field (nP : F), .field (nF : F), .field (o : F), ppw, pcty, prec]
      h r h' cs) :
    ∃ mty,
      cMinorTy C clvls nP nF o ℓ.zeronessOf Ecty recIdx = some mty ∧
      Tm κ 0 Γ₀ h' (nP + o) mty r := by
  rcases Obs.«KernelCheck::nat_minor_ty».obs ev with
    ⟨v1, m2, cs12, m32, cs42, v45, m47, cs55, w77, x_rargs, v88, m89, cs99, v103, m105,
      m134, cs142, v145, v146, m148, cs156, v159, m185, cs193, v211, m212, cs222,
      v225, v226, m229, cs237, v241, m243, v255, x262, m281, cs289, v292, m295, cs303,
      v306, m310, cs318, m359, cs367, cs387, v392, v393, m410, cs418, m445, cs453,
      ev14, ev57, ev44, hm105, op174, ev158, ev195, ev144, ev101, hm243, op277, op269,
      ev320, ev305, ev291, ev239, ev369, ev224, ev420, ev455, ev389, hc⟩
  subst hc
  -- Step 1 & 2: peel `nP` then `nF` Pis on `pcty`
  obtain ⟨hm2, rbsP, ebsP, Rq, Eq, hsRP, hsEP, hRq⟩ :=
    peel_n_foralls_rawTm_spec nP (by omega) hRaw ev14
  rw [hm2] at ev57
  obtain ⟨hm47, rbsF, ebsF, Rr, Er, hsRF, hsEF, hRr⟩ :=
    peel_n_foralls_rawTm_spec nF (by omega) hRq ev57
  rw [hm47] at ev44
  obtain ⟨bsP_R, q2_R, bsF_R, hsRP', hsRF', _, _⟩ := stripPis_split nP nF hsR
  rw [hsRP] at hsRP'; injection hsRP' with hp; injection hp with _ hRq_eq; subst hRq_eq
  rw [hsRF] at hsRF'; injection hsRF' with hp; injection hp with _ hRr_eq; subst hRr_eq
  obtain ⟨bsP_E, q2_E, bsF_E, hsEP', hsEF', _, _⟩ := stripPis_split nP nF hsE
  rw [hsEP] at hsEP'; injection hsEP' with hp; injection hp with _ hEq_eq; subst hEq_eq
  rw [hsEF] at hsEF'; injection hsEF' with hp; injection hp with _ hEr_eq; subst hEr_eq
  -- Step 3: `collect_spine` on `v45` (`nP + nF` depth)
  have hRr' : RawTm κ 0 Γ₀ h (nP + nF)
      (Expr.mkAppN (.const T rus) rargs) (Expr.mkAppN (.const T eus) eargs) v45 := by
    simpa [Nat.zero_add] using hRr
  obtain ⟨hd, sp, Rh, Eh, Ras, Eas, htup, hH, hEas, _, hR_sp, hE_sp, hnot_app⟩ :=
    collect_spine_rawTm_spec hRr' ev44
  injection htup with hl; injection hl with h1 hl; injection hl with h2
  subst h1 h2
  have hRh_fn : Rh = .const T rus := by
    have hfn := congrArg Expr.getAppFn hR_sp
    rw [getAppFn_mkAppN, getAppFn_mkAppN] at hfn
    cases Rh with
    | app f a => exact (hnot_app f a rfl).elim
    | bvar _ | fvar _ _ | sort _ | const _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ _
    | lit _ | proj _ _ _ => exact hfn.symm
  subst hRh_fn
  have hEh := hH.const_left_inv
  subst hEh
  obtain ⟨-, rfl, rfl⟩ := mkAppN_const_inj hE_sp
  -- Step 4 & 5: `v88 = Expr.mkAppN (.const C clvls) (structPsAt (o + nF) nP ++ structPsAt 0 nF)`
  have ext_m105 : Heap.Extends m32 m105 := by rw [hm105]; exact Heap.Extends.snoc _ _
  have ext_h_105 := ev44.heap_extends.trans ext_m105
  have hC_const : Tm κ 0 Γ₀ m105 (nP + o + nF) (.const C clvls)
      (.ptr (.enum kexprEnum) m32.length) := by
    rw [hm105, ← hC]
    exact .const (by simp) (Bytes.repAddressRef_heapMono₂ addrTy ext_h_105 hcprj)
      (hlps.mono ext_h_105) (lvEqList_refl clvls)
  rw [evalBinOp_add_nat o nF op174] at ev158
  have hps1 := nat_ps_at_spec nP (o + nF) (nP + o + nF) (by omega) (by omega) ev158
  have hps2 := nat_ps_at_spec nF 0 (nP + o + nF) (by omega) (by omega) ev195
  have hps12 := kexpr_list_concat_spec ev144 (hps1.mono ev195.heap_extends) hps2
  have hv88 := nat_app_n_spec
    ((hC_const.mono (ev158.heap_extends.trans (ev195.heap_extends.trans ev144.heap_extends))))
    hps12 ev101
  -- Step 6–8: `v225 = Expr.mkAppN (.bvar (nF + o - 1)) (...)`
  rw [evalBinOp_add_nat nF o op277] at op269
  rw [evalBinOp_sub_nat (by omega : 1 ≤ nF + o) op269] at hm243
  have ext_m243 : Heap.Extends m89 m243 := by rw [hm243]; exact Heap.Extends.snoc _ _
  have hbvar_mot : Tm κ 0 Γ₀ m243 (nP + o + nF) (.bvar (nF + o - 1))
      (.ptr (.enum kexprEnum) m89.length) := by
    rw [hm243]; exact tm_bvarLocal_nat (by simp) (by omega) (by omega)
  have ext_32_243 := ext_m105.trans (ev158.heap_extends.trans (ev195.heap_extends.trans
    (ev144.heap_extends.trans (ev101.heap_extends.trans ext_m243))))
  obtain ⟨_, hdrop_rargs, hm310⟩ := kexpr_list_drop_spec (by omega) ev320 (hEas.mono ext_32_243)
  rw [hm310] at ev305
  have hbnd_ml : IxVM.Consistency.Bounded cs303 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hmap_rargs := nat_map_lift_spec (by omega : nF ≤ nP + nF) (by omega) (by omega)
    hbnd_ml hdrop_rargs ev305
  have hmap_rargs' : RepList kexprListEnum (fun h E p => Tm κ 0 Γ₀ h (nP + o + nF) E p)
      m295 ((Eas.drop nP).map (Expr.liftLooseBVars o nF)) v292 := by
    rwa [show nP + o + nF = (nP + nF) + o by omega]
  have hsnoc := SubstAux.ksnoc (R := fun h E p => Tm κ 0 Γ₀ h (nP + o + nF) E p)
    (fun _ _ _ _ ext r => Tm.mono ext r) ev291 hmap_rargs'
    ((hv88.mono ext_m243).mono ev305.heap_extends)
  have hv225 := nat_app_n_spec
    ((hbvar_mot.mono ev305.heap_extends).mono ev291.heap_extends) hsnoc ev239
  -- Step 9 & 10: lift `v225` by `recIdx.length`
  have ext_h_229 := ev44.heap_extends.trans (ext_32_243.trans
    (ev305.heap_extends.trans (ev291.heap_extends.trans ev239.heap_extends)))
  obtain ⟨hv226, hm359⟩ := field_list_length_spec ev369 (hrec.mono ext_h_229)
  rw [hv226, hm359] at ev224
  have hbnd_l1 : IxVM.Consistency.Bounded cs222 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hv211 := expr_lift_local_spec (by omega) (by omega) (by omega) hbnd_l1 hv225 ev224
  -- Step 11: lift `v1` (`Eq`) by `o` at `0`
  have ext_h_212 := ext_h_229.trans ev224.heap_extends
  have hbnd_l2 : IxVM.Consistency.Bounded cs418 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hv1_tm : Tm κ 0 Γ₀ m212 nP Eq v1 := by
    simpa [Nat.zero_add] using hRq.toTm.mono ext_h_212
  have hv392 := expr_lift_local_spec (by omega) (by omega) (by omega) hbnd_l2 hv1_tm ev420
  -- Step 12: `nat_ih_pis`
  have ext_h_410 := ext_h_212.trans ev420.heap_extends
  have hbnd_ih : IxVM.Consistency.Bounded cs453 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hv211' : Tm κ 0 Γ₀ m410 (nP + o + nF + 0 + recIdx.length) _ v211 := by
    simpa using hv211.mono ev420.heap_extends
  have hv393 := nat_ih_pis_spec ho hsR hsE 0
    (fun i hi => by obtain ⟨h1, h2, h3⟩ := hall i hi; exact ⟨h1, h2, by omega⟩)
    (by omega) hbnd_ih
    (repKLevel_heapMono₂ ext_h_410 hpw)
    (hRaw.mono ext_h_410) (hrec.mono ext_h_410) hv211' ev455
  -- Step 13: `nat_replace_pis`
  have ext_h_445 := ext_h_410.trans ev455.heap_extends
  have hv393' : Tm κ 0 Γ₀ m445 ((nP + o) + nF) _ v393 := by
    simpa [Nat.add_assoc] using hv393
  obtain ⟨mty, hmty, hmty_tm⟩ := nat_replace_pis_spec nF (by omega)
    (repKLevel_heapMono₂ ext_h_445 hpw)
    (hv392.mono ev455.heap_extends) hv393' ev389
  simp only [↓reduceIte] at hmty
  refine ⟨mty, ?_, hmty_tm⟩
  unfold cMinorTy
  rw [hsEP, Option.bind_some, hsEF, Option.bind_some, getAppArgs_mkAppN_const]
  exact hmty

end IxVM.Refinement.Decl
