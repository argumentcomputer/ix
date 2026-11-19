import IxVMRefinement.Decl.ModeledAux
import IxVMRefinement.Core.Det
import IxC.Kernel.Model.IndRenJudge

/-! # A judgement package for model aliases with positionally reindexed valuations

A family member `X` with level parameters `lps` (a permutation of the positions, `n :: range n`
for a large eliminator) is given a model alias: a definition at a derived key whose value is the
advice model applied to `lps`, the advice model being stored at positional parameters
`range lps.length`. In every model of an environment that stores such an alias, the alias's leaf at
`ψ` is the target's leaf at `posVal lps ψ`. A renaming `h` of aliases to their targets is therefore
invisible to the reading (`denoteMeta_renameConsts_pos`), although the level lists differ, which
IxC's `RenameOk` does not allow.

`aliasJ h J` adjoins the renaming to a package: a judgement of `aliasJ h J` on a term is `J`'s
judgement on the term renamed by `h`, at an environment whose `h`-moved keys are stored aliases
(`AliasEnv`). It is sound at every model at which `J` is (`judgeSound_aliasJ_of`). -/

namespace IxVM.Refinement.Decl.FamilyAlias

open Aiur Aiur.Library Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Model
open Ix.Kernel.Term Ix.Kernel.Verify Ix.Kernel.SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal BinderMeta RecRule IndCaps
  LevelParam EnvExt ReducibilityHint Derived openPisAtFvars eqName eqA auxKey nestedRuleShape
  recRuleBits isEqHead hasFvar_renameConsts)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

/-! ## The positional valuation -/

/-- The positional valuation of an instantiated assignment is the positional instantiation. -/
theorem posVal_substFn {ps : List LevelParam} {us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hlen : us.length = ps.length)
    (φ : LevelParam → Nat) :
    posVal ps (Level.substFn φ ps us) = Level.substFn φ (List.range us.length) us := by
  funext p
  have hid : Level.subst (List.range us.length) us (.param p) =
      Level.subst ps us (Level.subst (List.range ps.length) (ps.map .param) (.param p)) := by
    have h := InferAux.posOf_instantiateLevelParams_perm (us := us)
      (T := invPosOf ps (.sort (.param p))) hperm hlen
    rw [posOf_invPosOf hperm] at h
    exact Expr.sort.inj h
  have hev := congrArg (Level.eval φ) hid
  simp only [Level.eval_subst] at hev
  exact hev.symm

/-- The positional valuation reads an assignment only at the parameters. -/
theorem posVal_congr {ps : List LevelParam} {ψ₁ ψ₂ : LevelParam → Nat}
    (h : ∀ p ∈ ps, ψ₁ p = ψ₂ p) :
    ∀ p ∈ List.range ps.length, posVal ps ψ₁ p = posVal ps ψ₂ p := by
  intro p hp
  have hp' : p < ps.length := List.mem_range.mp hp
  have hp_len : p < (ps.map Level.param).length := by rw [List.length_map]; exact hp'
  have hget := InferAux.getElem?_eq_subst_go_range (us := ps.map Level.param) hp_len
  rw [List.length_map, List.getElem?_map, List.getElem?_eq_getElem hp'] at hget
  have hgo : Level.subst.go (List.range ps.length) (ps.map .param) p = .param ps[p] :=
    (Option.some.inj hget).symm
  show Level.substFn ψ₁ (List.range ps.length) (ps.map .param) p =
    Level.substFn ψ₂ (List.range ps.length) (ps.map .param) p
  rw [← Level.eval_subst_go, ← Level.eval_subst_go, hgo]
  exact h _ (List.getElem_mem hp')

/-! ## The renaming condition with a reindexed valuation -/

/-- **The renaming condition, positionally**: a renamed constant resolves with as many level
parameters, the two leaves agree at every instantiation of the two parameter lists by one level
list, and unresolved names stay unresolved. `Ix.Kernel.Model.RenameOk` is the case of equal
parameter lists. -/
def RenameOkPos (acval : KKey → (LevelParam → Nat) → AnnotTerm) (env : Env .anon)
    (h : KKey → KKey) : Prop :=
  (∀ n ci, env.find? n = some ci → ∃ ci', env.find? (h n) = some ci' ∧
    ci'.toConstantVal.levelParams.length = ci.toConstantVal.levelParams.length ∧
    ∀ (φ : LevelParam → Nat) (us : List KLevel),
      us.length = ci.toConstantVal.levelParams.length →
      acval (h n) (Level.substFn φ ci'.toConstantVal.levelParams us) =
        acval n (Level.substFn φ ci.toConstantVal.levelParams us)) ∧
  (∀ n, env.find? n = none → env.find? (h n) = none)

/-- IxC's condition is the positional one at equal parameter lists. -/
theorem RenameOkPos.of_renameOk {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {h : KKey → KKey} (hro : RenameOk acval env h) :
    RenameOkPos acval env h := by
  refine ⟨fun n ci hf => ?_, hro.2.1⟩
  obtain ⟨ci', hf', hlp⟩ := hro.1 n ci hf
  refine ⟨ci', hf', by rw [hlp], fun φ us _ => ?_⟩
  rw [hlp, hro.2.2]

/-- **Renaming is invisible to the reading, positionally** (`denoteMeta_renameConsts` for a
renaming whose targets have reindexed valuations). -/
theorem denoteMeta_renameConsts_pos {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {φ : LevelParam → Nat} {h : KKey → KKey}
    (hro : RenameOkPos acval env h) :
    ∀ (e : KExpr) (d : Nat),
      denoteMeta acval env φ d (e.renameConsts h) = denoteMeta acval env φ d e
  | .bvar _, _ => by simp [Expr.renameConsts]
  | .sort _, _ => by simp [Expr.renameConsts]
  | .fvar _ _, _ => by simp [Expr.renameConsts, denoteMeta_fvar]
  | .lit (.natVal _), _ => by rw [Expr.renameConsts]
  | .lit (.strVal _), _ => by rw [Expr.renameConsts]
  | .const n ws, d => by
    simp only [Expr.renameConsts]
    cases hf : env.find? n with
    | none =>
      rw [denoteMeta, denoteMeta, hf, hro.2 n hf]
    | some ci =>
      obtain ⟨ci', hf', hlen, hac⟩ := hro.1 n ci hf
      rw [denoteMeta, denoteMeta, hf, hf']
      dsimp only
      by_cases hal : ws.length = ci.toConstantVal.levelParams.length
      · rw [ite_eq_left hal, ite_eq_left (hal.trans hlen.symm), hac φ ws hal]
      · rw [ite_eq_right hal, ite_eq_right (fun hh => hal (hh.trans hlen))]
  | .app g a, d => by
    simp only [Expr.renameConsts, denoteMeta_app,
      denoteMeta_renameConsts_pos hro g d, denoteMeta_renameConsts_pos hro a d]
  | .proj s i e, d => by
    simp only [Expr.renameConsts, denoteMeta_proj, denoteMeta_renameConsts_pos hro e d]
  | .forallE ty body m, d => by
    simp only [Expr.renameConsts, denoteMeta_forallE]
    rw [← Expr.renameConsts_instantiate1]
    rw [denoteMeta_renameConsts_pos hro ty d,
      denoteMeta_renameConsts_pos hro (body.instantiate1 (.fvar d ty)) (d + 1)]
  | .lam ty body m, d => by
    simp only [Expr.renameConsts, denoteMeta_lam]
    rw [← Expr.renameConsts_instantiate1]
    rw [denoteMeta_renameConsts_pos hro ty d,
      denoteMeta_renameConsts_pos hro (body.instantiate1 (.fvar d ty)) (d + 1)]
  | .letE ty val body _, d => by
    simp only [Expr.renameConsts]
    rw [denoteMeta, denoteMeta]
  termination_by e => e.sizeB
  decreasing_by
    all_goals
      simp [Expr.sizeB]
      try rw [Expr.sizeB_instantiate1 _ rfl]
      try omega

/-- **A context that suits a term suits its renaming**, positionally. -/
theorem ctxOk_renameConsts_pos {V : Type u} [Ix.Kernel.SetTheory V] {env : Env .anon}
    {m : EnvModel V env} {h : KKey → KKey}
    (hro : RenameOkPos m.acval env h) {φ : LevelParam → Nat} {d : Nat} {Δa : List AnnotTerm}
    {e : KExpr} (hc : CtxOk m φ d Δa e) : CtxOk m φ d Δa (e.renameConsts h) := by
  refine ⟨hc.1, ?_⟩
  intro l hl
  rw [fvarLeaves_renameConstsE] at hl
  obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
  obtain ⟨hlt, hfb, tya, Aa, hden, hAa, hint, hok⟩ := hc.2 l₀ hl₀
  exact ⟨hlt, fvarsBelow_renameConstsM _ hfb, tya, Aa,
    (denoteMeta_renameConsts_pos hro l₀.2 d).trans hden, hAa, hint, hok⟩

/-! ## Permutation valuations and level equivalence -/

/-- `Level.substFn` at a distinct parameter list evaluates at the parameter's position. -/
theorem substFn_getElem {φ : LevelParam → Nat} :
    ∀ {ks : List LevelParam} {vs : List KLevel},
      ks.Nodup → ks.length = vs.length → ∀ (i : Nat) (hi : i < ks.length),
      Level.substFn φ ks vs ks[i] = Level.eval φ (vs[i]'(by omega))
  | [], _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, hlen, _, _ => nomatch hlen
  | k :: ks, v :: vs, hnd, hlen, 0, _ => by
    simp [Level.substFn]
  | k :: ks, v :: vs, hnd, hlen, i + 1, hi => by
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    have hne : ks[i]'(by simp at hi; omega) ≠ k :=
      fun heq => hnot (heq ▸ List.getElem_mem (by simp at hi; omega))
    simp only [List.getElem_cons_succ, Level.substFn, if_neg hne]
    exact substFn_getElem hnd' (Nat.succ.inj hlen) i (by simp at hi; omega)

/-- `Level.substFn` leaves any parameter outside the parameter list unchanged. -/
theorem substFn_not_mem {φ : LevelParam → Nat} :
    ∀ {ks : List LevelParam} {vs : List KLevel} {p : LevelParam},
      p ∉ ks → Level.substFn φ ks vs p = φ p
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | k :: ks, _ :: vs, p, hp => by
    have hne : p ≠ k := fun h => hp (h ▸ List.mem_cons_self)
    simp only [Level.substFn, if_neg hne]
    exact substFn_not_mem (fun hm => hp (List.mem_cons_of_mem _ hm))

/-- `Level.substFn` preserves pointwise level equivalence of its level arguments. -/
theorem substFn_congr_lvEqList (φ : LevelParam → Nat) :
    ∀ (ks : List LevelParam) {us vs : List KLevel},
      LvEqList us vs → Level.substFn φ ks us = Level.substFn φ ks vs
  | [], _, _, _ => rfl
  | _ :: _, [], [], _ => rfl
  | _ :: _, [], _ :: _, h => False.elim (h φ)
  | _ :: _, _ :: _, [], h => False.elim (h φ)
  | k :: ks, u :: us, v :: vs, h => by
    funext p
    simp only [Level.substFn]
    split
    · exact (h φ).1
    · exact congrFun (substFn_congr_lvEqList φ ks (fun ψ => (h ψ).2)) p

/-- Pointwise level equivalence preserves list length. -/
theorem lvEqList_length_eq : ∀ {us vs : List KLevel}, LvEqList us vs → us.length = vs.length
  | [], [], _ => rfl
  | [], _ :: _, h => False.elim (h (fun _ => 0))
  | _ :: _, [], h => False.elim (h (fun _ => 0))
  | _ :: _, _ :: _, h => congrArg Nat.succ (lvEqList_length_eq (fun ψ => (h ψ).2))

/-- Renaming a positional parameter permutation back by `posVal lps ψ` matches instantiating it
at `lps.map .param`. -/
theorem substFn_posVal_of_perm {lps q : List LevelParam}
    (hpermL : lps.Perm (List.range lps.length)) (hpermQ : q.Perm (List.range lps.length))
    (ψ : LevelParam → Nat) :
    Level.substFn (posVal lps ψ) q ((List.range q.length).map .param) =
      Level.substFn ψ q (lps.map .param) := by
  have hlenQ : q.length = lps.length := by
    simpa [List.length_range] using hpermQ.length_eq
  have hndQ : q.Nodup := hpermQ.nodup_iff.mpr List.nodup_range
  funext p
  by_cases hp : p ∈ q
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have h1 := substFn_getElem (φ := posVal lps ψ) hndQ
      (by simp) i hi
    have h2 := substFn_getElem (φ := ψ) hndQ (by simp [hlenQ]) i hi
    rw [h1, h2]
    have hiL : i < lps.length := hlenQ ▸ hi
    simp only [List.getElem_map, List.getElem_range, Level.eval]
    have h3 := substFn_getElem (φ := ψ) (ks := List.range lps.length) (vs := lps.map .param)
      List.nodup_range (by simp) i (by simp [hiL])
    simp only [List.getElem_range, List.getElem_map, Level.eval] at h3
    exact h3
  · have hnr : p ∉ List.range lps.length := fun hm => hp (hpermQ.mem_iff.mpr hm)
    rw [substFn_not_mem hp, substFn_not_mem hp]
    exact substFn_not_mem hnr

/-- Composing two permutation substitutions cancels the intermediate parameter list. -/
theorem substFn_comp_of_perm {lps q : List LevelParam} {us : List KLevel}
    (hpermL : lps.Perm (List.range lps.length)) (hpermQ : q.Perm (List.range lps.length))
    (hlen : us.length = lps.length) (φ : LevelParam → Nat) :
    Level.substFn (Level.substFn φ lps us) q (lps.map .param) = Level.substFn φ q us := by
  have hlenQ : q.length = lps.length := by
    simpa [List.length_range] using hpermQ.length_eq
  have hndQ : q.Nodup := hpermQ.nodup_iff.mpr List.nodup_range
  have hndL : lps.Nodup := hpermL.nodup_iff.mpr List.nodup_range
  funext p
  by_cases hp : p ∈ q
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have h1 := substFn_getElem (φ := Level.substFn φ lps us) hndQ (by simp [hlenQ]) i hi
    have h2 := substFn_getElem (φ := φ) hndQ (by omega) i hi
    rw [h1, h2]
    have hiL : i < lps.length := hlenQ ▸ hi
    simp only [List.getElem_map, Level.eval]
    exact substFn_getElem hndL hlen.symm i hiL
  · have hnr : p ∉ List.range lps.length := fun hm => hp (hpermQ.mem_iff.mpr hm)
    have hnl : p ∉ lps := fun hm => hnr (hpermL.mem_iff.mp hm)
    rw [substFn_not_mem hp, substFn_not_mem hp, substFn_not_mem hnl]

/-- `Level.substFn ψ q (lps.map .param)` depends on `ψ` only at `lps`. -/
theorem substFn_lps_congr {lps q : List LevelParam}
    (hpermQ : q.Perm (List.range lps.length)) {ψ₁ ψ₂ : LevelParam → Nat}
    (h : ∀ p ∈ lps, ψ₁ p = ψ₂ p) :
    ∀ p ∈ q, Level.substFn ψ₁ q (lps.map .param) p = Level.substFn ψ₂ q (lps.map .param) p := by
  have hlenQ : q.length = lps.length := by
    simpa [List.length_range] using hpermQ.length_eq
  have hndQ : q.Nodup := hpermQ.nodup_iff.mpr List.nodup_range
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  rw [substFn_getElem hndQ (by simp [hlenQ]) i hi, substFn_getElem hndQ (by simp [hlenQ]) i hi]
  simp only [List.getElem_map, Level.eval]
  exact h _ (List.getElem_mem (hlenQ ▸ hi))

/-- Level-equivalent expressions have the same `sizeB`. -/
theorem exprLvEq_sizeB {e₁ e₂ : KExpr} (h : ExprLvEq e₁ e₂) : e₁.sizeB = e₂.sizeB := by
  induction h with
  | bvar | fvar | sort | const | lit => rfl
  | app _ _ ihf iha => simp [Expr.sizeB, ihf, iha]
  | lam _ _ iht ihb | forallE _ _ iht ihb => simp [Expr.sizeB, iht, ihb]
  | letE _ _ _ iht ihv ihb => simp [Expr.sizeB, iht, ihv, ihb]
  | proj _ ih => simp [Expr.sizeB, ih]

/-- Level-equivalent expressions have the same `hasFvar`. -/
theorem exprLvEq_hasFvar {e₁ e₂ : KExpr} (h : ExprLvEq e₁ e₂) : e₁.hasFvar = e₂.hasFvar := by
  induction h with
  | bvar | fvar | sort | const | lit => rfl
  | app _ _ ihf iha => simp [Expr.hasFvar, ihf, iha]
  | lam _ _ iht ihb | forallE _ _ iht ihb => simp [Expr.hasFvar, iht, ihb]
  | letE _ _ _ iht ihv ihb => simp [Expr.hasFvar, iht, ihv, ihb]
  | proj _ ih => simp [Expr.hasFvar, ih]

/-- Level-equivalent expressions have the same `looseBVarsBounded`. -/
theorem exprLvEq_looseBVarsBounded {e₁ e₂ : KExpr} (h : ExprLvEq e₁ e₂) :
    ∀ k, e₁.looseBVarsBounded k = e₂.looseBVarsBounded k := by
  induction h with
  | bvar | fvar | sort | const | lit => intro _; rfl
  | app _ _ ihf iha => intro k; simp [Expr.looseBVarsBounded, ihf k, iha k]
  | lam _ _ iht ihb | forallE _ _ iht ihb =>
    intro k; simp [Expr.looseBVarsBounded, iht k, ihb (k + 1)]
  | letE _ _ _ iht ihv ihb =>
    intro k; simp [Expr.looseBVarsBounded, iht k, ihv k, ihb (k + 1)]
  | proj _ ih => intro k; simp [Expr.looseBVarsBounded, ih k]

/-- Level-equivalent expressions have the same `constsResolve`. -/
theorem exprLvEq_constsResolve (env : Env .anon) {e₁ e₂ : KExpr} (h : ExprLvEq e₁ e₂) :
    e₁.constsResolve env = e₂.constsResolve env := by
  induction h with
  | bvar | sort | const | lit => rfl
  | fvar _ ih => exact ih
  | app _ _ ihf iha => simp [Expr.constsResolve, ihf, iha]
  | lam _ _ iht ihb | forallE _ _ iht ihb => simp [Expr.constsResolve, iht, ihb]
  | letE _ _ _ iht ihv ihb => simp [Expr.constsResolve, iht, ihv, ihb]
  | proj _ ih => simp [Expr.constsResolve, ih]

/-- Level-equivalent expressions have the same denotation. -/
theorem denoteMeta_of_exprLvEq {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {φ : LevelParam → Nat} :
    ∀ {e₁ e₂ : KExpr}, ExprLvEq e₁ e₂ → ∀ d : Nat,
      denoteMeta acval env φ d e₁ = denoteMeta acval env φ d e₂
  | .bvar _, .bvar _, .bvar, _ => rfl
  | .fvar _ _, .fvar _ _, .fvar _, _ => rfl
  | .sort u, .sort v, .sort hu, _ => by simp only [denoteMeta, hu φ]
  | .const n us, .const _ vs, .const hus, _ => by
    simp only [denoteMeta]
    cases env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      rw [lvEqList_length_eq hus, substFn_congr_lvEqList φ ci.toConstantVal.levelParams hus]
  | .app f₁ a₁, .app f₂ a₂, .app hf ha, d => by
    simp only [denoteMeta_app, denoteMeta_of_exprLvEq hf d, denoteMeta_of_exprLvEq ha d]
  | .lam t₁ b₁ m, .lam t₂ b₂ _, .lam ht hb, d => by
    simp only [denoteMeta_lam, denoteMeta_of_exprLvEq ht d]
    have hinst : ExprLvEq (b₁.instantiate1 (.fvar d t₁)) (b₂.instantiate1 (.fvar d t₂)) :=
      (ExprLvEq.fvar ht).shift hb 0
    rw [denoteMeta_of_exprLvEq hinst (d + 1)]
  | .forallE t₁ b₁ m, .forallE t₂ b₂ _, .forallE ht hb, d => by
    simp only [denoteMeta_forallE, denoteMeta_of_exprLvEq ht d]
    have hinst : ExprLvEq (b₁.instantiate1 (.fvar d t₁)) (b₂.instantiate1 (.fvar d t₂)) :=
      (ExprLvEq.fvar ht).shift hb 0
    rw [denoteMeta_of_exprLvEq hinst (d + 1)]
  | .letE _ _ _ _, .letE _ _ _ _, .letE _ _ _, _ => rfl
  | .lit _, .lit _, .lit, _ => rfl
  | .proj _ _ e₁, .proj _ _ e₂, .proj he, d => by
    simp only [denoteMeta_proj, denoteMeta_of_exprLvEq he d]
  termination_by e₁ _ _ _ => e₁.sizeB
  decreasing_by
    all_goals
      simp [Expr.sizeB]
      try rw [Expr.sizeB_instantiate1 _ rfl]
      try omega

/-! ## Stored aliases -/

/-- **`h` moves stored aliases only**: a key `h` moves is stored as a definition whose value is
its target at the definition's own level parameters, those parameters are a permutation of the
positions, and the target's parameters are a permutation of the same positions. -/
def AliasEnv (env : Env .anon) (h : KKey → KKey) : Prop :=
  ∀ k, h k ≠ k →
    ∃ (lps : List LevelParam) (ty : KExpr) (hint : ReducibilityHint) (ci : ConstantInfo .anon),
      env.find? k = some (.defnInfo ⟨k, lps, ty⟩ (.const (h k) (lps.map .param)) hint) ∧
      lps.Perm (List.range lps.length) ∧
      env.find? (h k) = some ci ∧
      ci.toConstantVal.levelParams.Perm (List.range lps.length)

/-- **The alias law holds in every model**: an alias's leaf at `ψ` is its target's leaf at the
parameter-reindexed valuation, by the model's reading of the alias's stored value. -/
theorem aliasEnv_acval {V : Type u} [Ix.Kernel.SetTheory V] {μ : CheckMode} {env : Env .anon}
    (m : EnvModelM V μ env) {h : KKey → KKey} (hA : AliasEnv env h) {k : KKey} (hk : h k ≠ k) :
    ∃ (lps : List LevelParam) (ty : KExpr) (hint : ReducibilityHint) (ci : ConstantInfo .anon),
      env.find? k = some (.defnInfo ⟨k, lps, ty⟩ (.const (h k) (lps.map .param)) hint) ∧
      lps.Perm (List.range lps.length) ∧
      env.find? (h k) = some ci ∧
      ci.toConstantVal.levelParams.Perm (List.range lps.length) ∧
      ∀ ψ : LevelParam → Nat,
        m.base2.acval k ψ =
          m.base2.acval (h k) (Level.substFn ψ ci.toConstantVal.levelParams (lps.map .param)) := by
  obtain ⟨lps, ty, hint, ci, hfk, hperm, hft, hlt⟩ := hA k hk
  refine ⟨lps, ty, hint, ci, hfk, hperm, hft, hlt, fun ψ => ?_⟩
  have hmem := Ix.Kernel.Semantics.Env.find?_mem hfk
  have hrd := m.defn_reads ψ ⟨k, lps, ty⟩ (.const (h k) (lps.map .param)) ⟨hint, hmem⟩
  rw [denoteMeta, hft] at hrd
  dsimp only at hrd
  have hlen : (lps.map Level.param).length = ci.toConstantVal.levelParams.length := by
    have hq := hlt.length_eq
    simp only [List.length_range] at hq
    simp [hq]
  rw [ite_eq_left hlen] at hrd
  exact (Option.some.inj hrd).symm

/-- **The renaming of aliases to their targets is invisible in every model** of an environment
that stores them. -/
theorem renameOkPos_of_aliasEnv {V : Type u} [Ix.Kernel.SetTheory V] {μ : CheckMode}
    {env : Env .anon} (m : EnvModelM V μ env) {h : KKey → KKey} (hA : AliasEnv env h) :
    RenameOkPos m.base2.acval env h := by
  refine ⟨fun n ci hf => ?_, fun n hf => ?_⟩
  · by_cases hn : h n = n
    · rw [hn]
      exact ⟨ci, hf, rfl, fun _ _ _ => rfl⟩
    · obtain ⟨lps, ty, hint, ci', hfk, hperm, hft, hlt, hac⟩ := aliasEnv_acval m hA hn
      rw [hfk] at hf
      obtain rfl := Option.some.inj hf
      have hlenQ : ci'.toConstantVal.levelParams.length = lps.length := by
        simpa [List.length_range] using hlt.length_eq
      refine ⟨ci', hft, hlenQ, fun φ us hus => ?_⟩
      have hus' : us.length = lps.length := hus
      rw [hac, substFn_comp_of_perm hperm hlt hus' φ]
  · by_cases hn : h n = n
    · rw [hn]
      exact hf
    · obtain ⟨lps, ty, hint, ci', hfk, -⟩ := hA n hn
      rw [hfk] at hf
      exact nomatch hf

/-! ## The package -/

/-- Every leaf annotation of `e` is fixed by the renaming. -/
def LeavesFixed (h : KKey → KKey) (e : KExpr) : Prop :=
  ∀ l ∈ e.fvarLeaves, l.2.renameConsts h = l.2

theorem LeavesFixed.of_closed {h : KKey → KKey} {e : KExpr} (hc : e.hasFvar = false) :
    LeavesFixed h e := by
  intro l hl
  rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hc] at hl
  exact nomatch hl

theorem fvarLeaves_renameConsts_of_fixed {h : KKey → KKey} {e : KExpr}
    (hfix : LeavesFixed h e) : (e.renameConsts h).fvarLeaves = e.fvarLeaves := by
  have hmap : e.fvarLeaves.map (fun l => (l.1, l.2.renameConsts h)) =
      e.fvarLeaves.map (fun l => l) :=
    List.map_congr_left (fun l hl => Prod.ext rfl (hfix l hl))
  rw [fvarLeaves_renameConstsE, hmap]
  simp

/-- **A package with stored aliases renamed to their targets**: a typing or a conversion of
`aliasJ h J` is `J`'s on the renamed terms, at an environment that stores the aliases `h` moves.
A conversion may leave its left term as it is: a type the package inferred is compared with a
renamed term, and an inferred type is over the targets already.
A typing is adjoined only for a subject whose leaf annotations `h` fixes (every closed subject),
so that the inferred type keeps the subject's frame. -/
def aliasJ (h : KKey → KKey) (J : Judgements .anon) : Judgements .anon where
  annot := J.annot
  infer env d e t := AliasEnv env h ∧ LeavesFixed h e ∧ J.infer env d (e.renameConsts h) t
  defeq env d a b := AliasEnv env h ∧
    (J.defeq env d (a.renameConsts h) (b.renameConsts h) ∨
      J.defeq env d a (b.renameConsts h))
  sort := J.sort
  isZero := J.isZero
  thmValue := J.thmValue

theorem judgeFrames_aliasJ {J : Judgements .anon} {env : Env .anon} {h : KKey → KKey}
    (hf : JudgeFrames J env) : JudgeFrames (aliasJ h J) env :=
  ⟨hf.annot_syntax, hf.annot_wscoped, hf.annot_bounded, hf.annot_leaves⟩

/-- **The package is sound where the renaming is invisible.** -/
theorem judgeSound_aliasJ {V : Type u} [Ix.Kernel.SetTheory V] {J : Judgements .anon}
    {env : Env .anon} {m : EnvModel V env} {h : KKey → KKey}
    (hro : AliasEnv env h → RenameOkPos m.acval env h) (hJ : JudgeSound J m) :
    JudgeSound (aliasJ h J) m where
  annot_syntax := hJ.annot_syntax
  annot_wscoped := hJ.annot_wscoped
  annot_bounded := hJ.annot_bounded
  annot_leaves := hJ.annot_leaves
  accepted := by
    intro φ d e t hj hws hb hL
    obtain ⟨hA, -, hj⟩ := hj
    obtain ⟨ea, hea⟩ := hJ.accepted φ hj (wscoped_renameConsts e hws)
      ((Expr.looseBVarsBounded_renameConsts h e 0).trans hb)
      (leavesBounded_renameConsts e hL)
    exact ⟨ea, (denoteMeta_renameConsts_pos (hro hA) e d).symm.trans hea⟩
  infer := by
    intro φ d e t Δa hj hws hb hL ea ta hctx hea hta
    obtain ⟨hA, -, hj⟩ := hj
    exact hJ.infer φ hj (wscoped_renameConsts e hws)
      ((Expr.looseBVarsBounded_renameConsts h e 0).trans hb)
      (leavesBounded_renameConsts e hL) (ctxOk_renameConsts_pos (hro hA) hctx)
      ((denoteMeta_renameConsts_pos (hro hA) e d).trans hea) hta
  defeq := by
    intro φ d a b Δa hj hwsa hba hLa hwsb hbb hLb aa ba hca hcb hda hdb hga hgb
    obtain ⟨hA, hj | hj⟩ := hj
    · exact hJ.defeq φ hj (wscoped_renameConsts a hwsa)
        ((Expr.looseBVarsBounded_renameConsts h a 0).trans hba)
        (leavesBounded_renameConsts a hLa) (wscoped_renameConsts b hwsb)
        ((Expr.looseBVarsBounded_renameConsts h b 0).trans hbb)
        (leavesBounded_renameConsts b hLb)
        (ctxOk_renameConsts_pos (hro hA) hca) (ctxOk_renameConsts_pos (hro hA) hcb)
        ((denoteMeta_renameConsts_pos (hro hA) a d).trans hda)
        ((denoteMeta_renameConsts_pos (hro hA) b d).trans hdb) hga hgb
    · exact hJ.defeq φ hj hwsa hba hLa (wscoped_renameConsts b hwsb)
        ((Expr.looseBVarsBounded_renameConsts h b 0).trans hbb)
        (leavesBounded_renameConsts b hLb)
        hca (ctxOk_renameConsts_pos (hro hA) hcb) hda
        ((denoteMeta_renameConsts_pos (hro hA) b d).trans hdb) hga hgb
  reads := by
    intro φ d e t Δa ea hj hws hb hL hctx hea
    obtain ⟨hA, -, hj⟩ := hj
    exact hJ.reads φ hj (wscoped_renameConsts e hws)
      ((Expr.looseBVarsBounded_renameConsts h e 0).trans hb)
      (leavesBounded_renameConsts e hL) (ctxOk_renameConsts_pos (hro hA) hctx)
      ((denoteMeta_renameConsts_pos (hro hA) e d).trans hea)
  frame := by
    intro φ d e t Δa ea hj hws hb hL hctx hea
    obtain ⟨hA, hfix, hj⟩ := hj
    obtain ⟨hwst, hbt, hsub⟩ := hJ.frame φ hj (wscoped_renameConsts e hws)
      ((Expr.looseBVarsBounded_renameConsts h e 0).trans hb)
      (leavesBounded_renameConsts e hL) (ctxOk_renameConsts_pos (hro hA) hctx)
      ((denoteMeta_renameConsts_pos (hro hA) e d).trans hea)
    refine ⟨hwst, hbt, fun l hl => ?_⟩
    have hl' := hsub l hl
    rw [fvarLeaves_renameConsts_of_fixed hfix] at hl'
    exact hl'

/-- **The package is sound at every model at which `J` is**: the alias law is read off the
model, so nothing is assumed of it. -/
theorem judgeSound_aliasJ_of {V : Type u} [Ix.Kernel.SetTheory V] {μ : CheckMode}
    {J : Judgements .anon} {env : Env .anon} (mp : EnvModelM V μ env) {h : KKey → KKey}
    (hJ : JudgeSound J mp.base2) : JudgeSound (aliasJ h J) mp.base2 :=
  judgeSound_aliasJ (fun hA => renameOkPos_of_aliasEnv mp hA) hJ

/-- **The family package**: positional derivations on the terms with the aliases renamed to
their targets. -/
abbrev famJ (h : KKey → KKey) : Judgements .anon := aliasJ h posRulesJ

theorem judgeFrames_famJ (h : KKey → KKey) (env : Env .anon) : JudgeFrames (famJ h) env :=
  judgeFrames_aliasJ (judgeFrames_posRulesJ env)

/-- **The family package is sound at every model of every environment.** -/
theorem judgeSound_famJ_of {V : Type u} [Ix.Kernel.SetTheory V] {μ : CheckMode}
    {env : Env .anon} (mp : EnvModelM V μ env) (h : KKey → KKey) :
    JudgeSound (famJ h) mp.base2 :=
  judgeSound_aliasJ_of mp (judgeSound_posRulesJ_of mp)

end IxVM.Refinement.Decl.FamilyAlias
