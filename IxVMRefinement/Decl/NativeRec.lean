import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.Levels.Bound
import IxVMRefinement.Subst.Steps
import IxVMRefinement.Obs.KernelCheck7

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
  | proj {s : KKey} {i : Nat} {e e' : KExpr} :
      WrapTSem find? e e' → WrapTSem find? (.proj s i e) (.proj s i e')

theorem ExprSemEq.toWrapTSem (find? : KKey → Option (ConstantInfo .anon)) {e e' : KExpr}
    (h : ExprSemEq e e') (hl : letFree e' = true) : WrapTSem find? e e' := by
  induction h with
  | bvar i => exact .bvar i
  | fvar _ _ => exact .fvar _ _ _
  | sort hu => exact .sort hu
  | const hus => exact .const hus
  | lit l => exact .lit l
  | app _ _ ihf iha =>
    simp only [letFree, Bool.and_eq_true] at hl
    exact .app (ihf hl.1) (iha hl.2)
  | lam hpw _ _ iht ihb =>
    simp only [letFree, Bool.and_eq_true] at hl
    exact .lam hpw (.refl _) (iht hl.1) (ihb hl.2)
  | forallE hpw _ _ iht ihb =>
    simp only [letFree, Bool.and_eq_true] at hl
    exact .forallE hpw (.refl _) (iht hl.1) (ihb hl.2)
  | letE _ _ _ _ _ _ => simp [letFree] at hl
  | proj _ ihe =>
    simp only [letFree] at hl
    exact .proj (ihe hl)

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
    | @forallE _ d' ty body _ _ _ _ _ hit _ hib _ _ =>
      simp only [Expr.sizeB] at hsz
      simp only [defnAritiesOk, Bool.and_eq_true]
      refine ⟨defnAritiesOk_of_infer_go sz (by omega) hit, ?_⟩
      rw [← defnAritiesOk_of_instantiate1_fvar d' ty body 0]
      exact defnAritiesOk_of_infer_go sz
        (by rw [sizeB_instantiate1_fvar]; omega) hib
    | @lam _ d' ty body _ _ _ _ _ _ hit _ hib _ _ _ _ =>
      simp only [Expr.sizeB] at hsz
      simp only [defnAritiesOk, Bool.and_eq_true]
      refine ⟨defnAritiesOk_of_infer_go sz (by omega) (hit rfl), ?_⟩
      rw [← defnAritiesOk_of_instantiate1_fvar d' ty body 0]
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

private theorem wrapTSem_defeq_go {env : Ix.Kernel.Env .anon} :
    ∀ (sz : Nat) {depth : Nat} {g d_e : KExpr},
      d_e.sizeB ≤ sz → WrapTSem env.find? g d_e → defnAritiesOk env.find? g = true →
      g.looseBVarsBounded 0 = true → DefEq env depth g d_e
  | 0, _, _, _, hsz, hw, _, _ => by
    cases hw <;> simp [Expr.sizeB] at hsz
  | sz + 1, depth, g, d_e, hsz, hw, hok, hlbb => by
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
      simp only [defnAritiesOk, Expr.looseBVarsBounded, Bool.and_eq_true] at hok hlbb
      exact .app
        (wrapTSem_defeq_go sz (by omega) hf hok.1 hlbb.1)
        (wrapTSem_defeq_go sz (by omega) ha hok.2 hlbb.2)
    | @lam t a t' b b' m m' hpw hs hw_dom hw_body =>
      simp only [Expr.sizeB] at hsz
      simp only [defnAritiesOk, Expr.looseBVarsBounded, Bool.and_eq_true] at hok hlbb
      have hdom_a : DefEq env depth a t' :=
        wrapTSem_defeq_go sz (by omega) hw_dom
          (hs.of (P := fun e => defnAritiesOk env.find? e = true) hP_ok hok.1)
          (hs.of (P := fun e => e.looseBVarsBounded 0 = true) hP_lbb hlbb.1)
      have hdom : DefEq env depth t t' := .redL (hs.red hok.1 hlbb.1) hdom_a
      have hbody_w : WrapTSem env.find?
          (b.instantiate1 (.fvar depth t')) (b'.instantiate1 (.fvar depth t')) :=
        hw_body.instantiate1 (.fvar depth t' t') 0
      have hbody_ok : defnAritiesOk env.find? (b.instantiate1 (.fvar depth t')) = true := by
        rw [defnAritiesOk_of_instantiate1_fvar]; exact hok.2
      have hbody_lbb : (b.instantiate1 (.fvar depth t')).looseBVarsBounded 0 = true :=
        lbb_instantiate1_fvar depth t' b 0 hlbb.2
      have hbody : DefEq env (depth + 1)
          (b.instantiate1 (.fvar depth t')) (b'.instantiate1 (.fvar depth t')) :=
        wrapTSem_defeq_go sz (by rw [sizeB_instantiate1_fvar]; omega) hbody_w hbody_ok hbody_lbb
      exact .lam hdom hbody hpw
    | @forallE t a t' b b' m m' hpw hs hw_dom hw_body =>
      simp only [Expr.sizeB] at hsz
      simp only [defnAritiesOk, Expr.looseBVarsBounded, Bool.and_eq_true] at hok hlbb
      have hdom_a : DefEq env depth a t' :=
        wrapTSem_defeq_go sz (by omega) hw_dom
          (hs.of (P := fun e => defnAritiesOk env.find? e = true) hP_ok hok.1)
          (hs.of (P := fun e => e.looseBVarsBounded 0 = true) hP_lbb hlbb.1)
      have hdom : DefEq env depth t t' := .redL (hs.red hok.1 hlbb.1) hdom_a
      have hbody_w : WrapTSem env.find?
          (b.instantiate1 (.fvar depth t')) (b'.instantiate1 (.fvar depth t')) :=
        hw_body.instantiate1 (.fvar depth t' t') 0
      have hbody_ok : defnAritiesOk env.find? (b.instantiate1 (.fvar depth t')) = true := by
        rw [defnAritiesOk_of_instantiate1_fvar]; exact hok.2
      have hbody_lbb : (b.instantiate1 (.fvar depth t')).looseBVarsBounded 0 = true :=
        lbb_instantiate1_fvar depth t' b 0 hlbb.2
      have hbody : DefEq env (depth + 1)
          (b.instantiate1 (.fvar depth t')) (b'.instantiate1 (.fvar depth t')) :=
        wrapTSem_defeq_go sz (by rw [sizeB_instantiate1_fvar]; omega) hbody_w hbody_ok hbody_lbb
      exact .forallE hdom hbody hpw
    | proj he =>
      simp only [Expr.sizeB] at hsz
      simp only [defnAritiesOk, Expr.looseBVarsBounded] at hok hlbb
      exact .proj (wrapTSem_defeq_go sz (by omega) he hok hlbb)

/-- `WrapRelSem` on a `let`-free declared term `d_e` and loose-bvar-closed generated term `g`
implies kernel `DefEq env depth d_e g`. -/
theorem WrapRelSem.defeq {env : Ix.Kernel.Env .anon} {depth : Nat} {g d_e : KExpr}
    (h : WrapRelSem env.find? g d_e) (hl : letFree d_e = true)
    (hok : defnAritiesOk env.find? g = true) (hlbb : g.looseBVarsBounded 0 = true) :
    DefEq env depth d_e g :=
  .symm (wrapTSem_defeq_go d_e.sizeB (Nat.le_refl _) (h.toWrapTSem hl) hok hlbb)

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
      simp only [Expr.liftLooseBVars, Expr.abstract1, ite_eq_left rfl,
        ite_eq_left (show k + c ≥ c by omega)]
      congr 1
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
    · subst hij
      simp only [Expr.instantiate1Lift, Expr.abstract1, ite_eq_left rfl]
      simpa using liftLooseBVars_abstract1 j d v k 0
    · by_cases hgt : i > j
      · simp [Expr.instantiate1Lift, Expr.abstract1, hij, hgt]
      · simp [Expr.instantiate1Lift, Expr.abstract1, hij, hgt]
  | .fvar idx ty, j => by
    by_cases hidx : idx = d
    · subst hidx
      simp only [Expr.instantiate1Lift, Expr.abstract1, ite_eq_left rfl,
        ite_eq_right (show k + j + 1 ≠ j by omega),
        ite_eq_left (show k + j + 1 > j by omega)]
      congr 1
      omega
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
      simp only [Expr.liftLooseBVars, Expr.abstract1, ite_eq_left rfl,
        ite_eq_left (show c + m ≥ c by omega)]
      congr 1
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
  | .fvar _ _, _, _, _, _ | .sort _, _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _, _ => rfl
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
    subst hm157
    rw [lamFirstArity_posOf] at hlam_pos
    have hrest_m96 : RepList kexprListEnum (fun h E p => Tm c.κ d Γ h 0 E p) m96 rest xrest :=
      hrest.mono (fun _ _ _ ext r => r.mono ext) e_ci
    have hlen_rest_lt : rest.length < 549755813888 :=
      RomBound.bounded_length_lt hgood.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [xrest], m96⟩)
        (by simp) List.mem_cons_self hrest_m96
    rw [← kexprList_inst] at ev235
    obtain ⟨hx222, rfl⟩ :=
      Lib.Lists.length_spec (t := kexprTy) (R := fun h E p => Tm c.κ d Γ h 0 E p)
        ev235 hrest_m96
    rw [hx222] at op229
    have hy214 : y214 = .field ((rest.length + 1 : Nat) : F) :=
      evalBinOp_add_one rest.length op229
    rw [hxk, hy214] at op220
    simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
      Except.ok.injEq, Value.field.injEq] at op220
    have hk_lt : k_out < 549755813888 := by
      have := hbnd_call_lfa steps_v hdesc_xv
      omega
    have hk_eq : k_out = rest.length + 1 :=
      nat_eq_of_field_eq hk_lt (by omega) (congrArg Value.field (sub_eq_zero.mp op220))
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
              rw [haddr] at op619
              simp [evalBinOp, bind, Except.bind, pure, Except.pure] at op619
          subst hs_eq
          have hv648 : v648 = .field 0 := by
            by_cases h0 : v648 = .field 0
            · exact h0
            · have hf_ne : ∀ x : F, v648 = .field x → x ≠ 0 := by
                intro x hx hx0; subst hx0; exact h0 hx
              simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
                Except.ok.injEq] at op662
              subst op662
              have hne0 : fa - fb ≠ 0 := hf_ne _ rfl
              rw [hiz, ite_eq_right hne0] at op619
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
          exact (kexpr_struct_eq_tm_one hG hD ev715).toWrapTSem c.env.find? hD.letFree
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
    ((Subst.lbrLe_of_idxLt hG (by simpa using Subst.tm_idxLt hG) (Nat.le_refl 0)).2.1)

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
    simp only [Ix.Kernel.openPisAtFvars, Option.map_eq_some_iff] at hop
    obtain ⟨⟨tl, r⟩, htl, hcons, _⟩ := hop
    subst hcons
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
      injection hpair with _ hsp; subst hsp
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
      have hzero := nat_eq_of_field_eq (by omega) (by decide) hsub.symm
      omega
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
      simp only [Ix.Kernel.openPisAtFvars, Option.map_eq_some_iff] at hop
      obtain ⟨⟨xFvs_tl, r_tl⟩, hop_tl, hxpair⟩ := hop
      injection hxpair with hxFvs_eq hr_eq
      subst hr_eq
      have hxFvs_symm : xFvs = .fvar (nP + field_idx) dom :: xFvs_tl := hxFvs_eq.symm
      subst hxFvs_symm
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
          subst hv282 hm283 hcs285
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
                by simpa using hinf₀, by simpa using hred₀, Or.inl hu₀_zero⟩
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
                by simpa using hinf₀, by simpa using hred₀, Or.inr hcur_in_idx⟩
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
          (by simpa using hcur.mono e_nil) (fun _ hm => nomatch hm) hbvars_nil ev20
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
      simp only [Ix.Kernel.openPisAtFvars, Option.map_eq_some_iff] at hopP
      obtain ⟨⟨fvsP_tl, r_tl⟩, hopP_tl, hxpair⟩ := hopP
      injection hxpair with _ hr_eq
      subst hr_eq
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
    have hlen0 : ctors.length = 0 := nat_eq_of_field_eq hnCtors_lt (by decide) hv69
    refine ⟨Or.inr (by omega), [], by omega, by omega, fun j _ _ hcj _ => ?_⟩
    have := (List.getElem?_eq_some_iff.mp hcj).1
    omega
  | .other_other_n1_other_Ctor_n0 (hv77 := hv77) (hv92 := hv92) .. =>
    have hlen1 : ctors.length = 1 := nat_eq_of_field_eq hnCtors_lt (by decide) hv77
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
    have hnF0 : cA₀.2 = 0 := nat_eq_of_field_eq hnF_lt (by decide) hnf0
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
    have hlen1 : ctors.length = 1 := nat_eq_of_field_eq hnCtors_lt (by decide) hv77
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
          (fvar_not_in_fvsP hopP (Nat.le_refl nP)) hopF nP 0 (by omega) hopP hg_prop
          (hrc.mono (e_15.trans e_247)) hty_nil GhostScoped.zero
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

end IxVM.Refinement.Decl
