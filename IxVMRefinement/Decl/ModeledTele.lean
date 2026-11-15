import IxVMRefinement.Decl.ModeledLevels
import IxVMRefinement.Subst.Steps
import IxVMRefinement.Obs.KernelModeled0
import IxVMRefinement.Obs.KernelModeled1
import IxVMRefinement.Obs.KernelModeled4
import IxVMRefinement.Obs.KernelCheck0
import IxVMRefinement.Obs.KernelCheck2
import IxVMRefinement.Obs.KernelCheck11
import IxVMRefinement.Obs.KernelWhnf0
import IxC.Kernel.Verify.InstLevels

/-! # Telescope, spine, renaming, and major-pin helpers for modeled declarations

This module proves the VM refinement specifications for all helper functions shared across
`KernelModeled` (`rename_addr`, `rename`, `rename_list`, `peel_n_foralls`,
`build_param_lvls_range`, `peel_n_lams_collect`, `apply_spine`, `defeq_list_ok`,
`assert_index_vars`, `lower_pins`, `rec_major_pins`, `peel_collect`, `bvars_desc`, `lift_list`,
`inst_params`, `inst_params_typed`, `defeq_tele`, `defeq_lam_tele`), together with the positional
level-parameter (`posOf`) commutation lemmas and `CoreCallCtx` abstraction used by both the public
and advice keyings. -/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Core.Specs.Subst (IdxAll IdxLt NoIdx NoIdxF BVarIm idxBound)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo Declaration RecRule IndCaps EnvExt)
open Ix.Kernel.Rules (Annot Red DefEq Infer)
open Ix.Kernel.Semantics (Judgements DefEqListJ TypedListJ)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

local macro "tele_lt_calls" : term =>
  `(by simp only [List.length_cons, List.length_append, List.length_nil] <;> omega)

local macro "tele_sub_calls" : term =>
  `(fun _ hx => by simp [hx])

/-! ## Kernel expression algebra: `renameAll`, `NoProjIn`, `noLooseIn`, `lowerBVars`, and `posOf` -/

/-- Variant of `Expr.renameConsts` that also renames structure keys inside `.proj` nodes
(matching `KernelModeled::rename` on arbitrary heap expressions before discharging `NoProjIn`). -/
def renameAll (f : KKey → KKey) : KExpr → KExpr
  | .bvar i => .bvar i
  | .fvar i ty => .fvar i (renameAll f ty)
  | .sort u => .sort u
  | .const n us => .const (f n) us
  | .app a b => .app (renameAll f a) (renameAll f b)
  | .lam ty body m => .lam (renameAll f ty) (renameAll f body) m
  | .forallE ty body m => .forallE (renameAll f ty) (renameAll f body) m
  | .letE ty v body m => .letE (renameAll f ty) (renameAll f v) (renameAll f body) m
  | .lit l => .lit l
  | .proj s i e => .proj (f s) i (renameAll f e)

/-- No `.proj sn i e` subterm of the expression names a structure `sn ∈ bad`. -/
def NoProjIn (bad : List KKey) : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar _ ty => NoProjIn bad ty
  | .app f a => NoProjIn bad f && NoProjIn bad a
  | .lam ty b _ | .forallE ty b _ => NoProjIn bad ty && NoProjIn bad b
  | .letE ty v b _ => NoProjIn bad ty && NoProjIn bad v && NoProjIn bad b
  | .proj sn _ e => !bad.contains sn && NoProjIn bad e

theorem renameAll_eq_renameConsts_of_noProjIn {bad : List KKey} {f : KKey → KKey}
    (hf : ∀ k, bad.contains k = false → f k = k) :
    ∀ {e : KExpr}, NoProjIn bad e = true → renameAll f e = e.renameConsts f := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _; rfl
  | fvar i ty ih =>
    intro h; simp only [NoProjIn] at h
    simp only [renameAll, Expr.renameConsts, ih h]
  | app a b iha ihb =>
    intro h; simp only [NoProjIn, Bool.and_eq_true] at h
    simp only [renameAll, Expr.renameConsts, iha h.1, ihb h.2]
  | lam ty bo m iht ihb =>
    intro h; simp only [NoProjIn, Bool.and_eq_true] at h
    simp only [renameAll, Expr.renameConsts, iht h.1, ihb h.2]
  | forallE ty bo m iht ihb =>
    intro h; simp only [NoProjIn, Bool.and_eq_true] at h
    simp only [renameAll, Expr.renameConsts, iht h.1, ihb h.2]
  | letE ty v bo m iht ihv ihb =>
    intro h; simp only [NoProjIn, Bool.and_eq_true] at h
    simp only [renameAll, Expr.renameConsts, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj sn i e ih =>
    intro h; simp only [NoProjIn, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [renameAll, Expr.renameConsts, hf sn h.1, ih h.2]

theorem noProjIn_instantiateLevelParams (bad : List KKey) (ks : List LevelParam)
    (us : List KLevel) :
    ∀ e : KExpr, NoProjIn bad (e.instantiateLevelParams ks us) = NoProjIn bad e := by
  intro e
  induction e <;> simp_all [Expr.instantiateLevelParams, NoProjIn]

theorem noProjIn_of_instantiate1 {bad : List KKey} {v : KExpr} :
    ∀ {e : KExpr} (k : Nat), NoProjIn bad (e.instantiate1 v k) = true → NoProjIn bad e = true := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | fvar _ _ _ => intro _ h; exact h
  | app f a ihf iha =>
    intro k h; simp only [Expr.instantiate1, NoProjIn, Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty b _ iht ihb =>
    intro k h; simp only [Expr.instantiate1, NoProjIn, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b _ iht ihb =>
    intro k h; simp only [Expr.instantiate1, NoProjIn, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty va b _ iht ihv ihb =>
    intro k h; simp only [Expr.instantiate1, NoProjIn, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj sn i e ih =>
    intro k h; simp only [Expr.instantiate1, NoProjIn, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih k h.2⟩

theorem noProjIn_of_instSpine {bad : List KKey} :
    ∀ (args : List KExpr) (t : Nat) {e : KExpr},
      NoProjIn bad (Expr.instSpine args t e) = true → NoProjIn bad e = true
  | [], _, _, h => h
  | a :: as, t, e, h =>
    noProjIn_of_instantiate1 t (noProjIn_of_instSpine as (t - 1) h)

private def FvarNoProjIn (bad : List KKey) : KExpr → Prop
  | .bvar _ | .sort _ | .const _ _ | .lit _ => True
  | .fvar _ ty => NoProjIn bad ty = true ∧ FvarNoProjIn bad ty
  | .app f a => FvarNoProjIn bad f ∧ FvarNoProjIn bad a
  | .lam ty b _ | .forallE ty b _ => FvarNoProjIn bad ty ∧ FvarNoProjIn bad b
  | .letE ty v b _ => FvarNoProjIn bad ty ∧ FvarNoProjIn bad v ∧ FvarNoProjIn bad b
  | .proj _ _ e => FvarNoProjIn bad e

private theorem fvarNoProjIn_of_hasFvar_false {bad : List KKey} :
    ∀ {e : KExpr}, e.hasFvar = false → FvarNoProjIn bad e := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _; trivial
  | fvar _ _ _ => intro h; simp [Expr.hasFvar] at h
  | app _ _ ihf iha =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h; exact ⟨ihf h.1, iha h.2⟩
  | lam _ _ _ iht ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h; exact ⟨iht h.1, ihb h.2⟩
  | forallE _ _ _ iht ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h; exact ⟨iht h.1, ihb h.2⟩
  | letE _ _ _ _ iht ihv ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | proj _ _ _ ih =>
    intro h; simp only [Expr.hasFvar] at h; exact ih h

private theorem fvarNoProjIn_instantiate1 {bad : List KKey} {v : KExpr}
    (hv : FvarNoProjIn bad v) :
    ∀ {e : KExpr} (k : Nat), FvarNoProjIn bad e → FvarNoProjIn bad (e.instantiate1 v k) := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> trivial
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ h; exact h
  | app _ _ ihf iha => intro k h; exact ⟨ihf k h.1, iha k h.2⟩
  | lam _ _ _ iht ihb => intro k h; exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE _ _ _ iht ihb => intro k h; exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE _ _ _ _ iht ihv ihb => intro k h; exact ⟨iht k h.1, ihv k h.2.1, ihb (k + 1) h.2.2⟩
  | proj _ _ _ ih => intro k h; exact ih k h

private def teleExprDepth : KExpr → Nat
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lit _ => 0
  | .app f a => 1 + max (teleExprDepth f) (teleExprDepth a)
  | .lam ty b _ | .forallE ty b _ => 1 + max (teleExprDepth ty) (teleExprDepth b)
  | .letE ty v b _ => 1 + max (max (teleExprDepth ty) (teleExprDepth v)) (teleExprDepth b)
  | .proj _ _ e => 1 + teleExprDepth e

private theorem teleExprDepth_instantiate1_fvar (d : Nat) (ty : KExpr) :
    ∀ (e : KExpr) (k : Nat), teleExprDepth (e.instantiate1 (.fvar d ty) k) = teleExprDepth e := by
  intro e
  induction e with
  | bvar i =>
    intro k; simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _; rfl
  | app f a ihf iha => intro k; simp only [Expr.instantiate1, teleExprDepth, ihf k, iha k]
  | lam t b _ iht ihb => intro k; simp only [Expr.instantiate1, teleExprDepth, iht k, ihb (k + 1)]
  | forallE t b _ iht ihb =>
    intro k; simp only [Expr.instantiate1, teleExprDepth, iht k, ihb (k + 1)]
  | letE t v b _ iht ihv ihb =>
    intro k; simp only [Expr.instantiate1, teleExprDepth, iht k, ihv k, ihb (k + 1)]
  | proj _ _ e ih => intro k; simp only [Expr.instantiate1, teleExprDepth, ih k]

private theorem infer_noProjIn_aux {bad : List KKey} :
    ∀ (n : Nat) {env : Ix.Kernel.Env .anon} {g : Ix.Kernel.Rules.Grade}
      {d : Nat} {e t : KExpr},
      teleExprDepth e ≤ n → Infer env g d e t → g = .full →
      (∀ sn i entry, env.findProj? sn i = some entry → bad.contains sn = false) →
      FvarNoProjIn bad e →
      NoProjIn bad e = true := by
  intro n
  induction n with
  | zero =>
    intro env g d e t hdep hinf hg _ hfv
    cases hinf with
    | sort | const _ _ _ | natLit _ | strLit _ => rfl
    | fvar _ => exact hfv.1
    | forallE | lam | app | proj => simp only [teleExprDepth] at hdep; omega
    | appSkip => nomatch hg
  | succ n ih =>
    intro env g d e t hdep hinf hg hproj hfv
    cases hinf with
    | sort | const _ _ _ | natLit _ | strLit _ => rfl
    | fvar _ => exact hfv.1
    | forallE hty _ hbo _ _ =>
      simp only [teleExprDepth] at hdep
      have hty_np := ih (by omega) hty hg hproj hfv.1
      have hbo_np := ih (by rw [teleExprDepth_instantiate1_fvar]; omega) hbo hg hproj
        (fvarNoProjIn_instantiate1 (v := .fvar _ _) ⟨hty_np, hfv.1⟩ 0 hfv.2)
      simp only [NoProjIn, Bool.and_eq_true]
      exact ⟨hty_np, noProjIn_of_instantiate1 0 hbo_np⟩
    | lam hty _ hbo _ _ _ _ =>
      simp only [teleExprDepth] at hdep
      have hty_np := ih (by omega) (hty hg) rfl hproj hfv.1
      have hbo_np := ih (by rw [teleExprDepth_instantiate1_fvar]; omega) hbo hg hproj
        (fvarNoProjIn_instantiate1 (v := .fvar _ _) ⟨hty_np, hfv.1⟩ 0 hfv.2)
      simp only [NoProjIn, Bool.and_eq_true]
      exact ⟨hty_np, noProjIn_of_instantiate1 0 hbo_np⟩
    | app hfn _ harg _ =>
      simp only [teleExprDepth] at hdep
      simp only [NoProjIn, Bool.and_eq_true]
      exact ⟨ih (by omega) hfn hg hproj hfv.1, ih (by omega) harg hg hproj hfv.2⟩
    | appSkip => nomatch hg
    | @proj _ _ sn i pe _ _ _ entry hpe _ _ hent _ _ _ =>
      simp only [teleExprDepth] at hdep
      simp only [NoProjIn, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨hproj sn i entry hent, ih (by omega) hpe hg hproj hfv⟩

/-- Full-grade `Rules.Infer` guarantees `NoProjIn bad e = true` whenever every projection table in
`env` avoids `bad` and opened variables in `e` already satisfy `FvarNoProjIn bad`. -/
theorem infer_noProjIn_open {bad : List KKey} {env : Ix.Kernel.Env .anon}
    {d : Nat} {e t : KExpr} (hinf : Infer env .full d e t)
    (hproj : ∀ sn i entry, env.findProj? sn i = some entry → bad.contains sn = false)
    (hfv : FvarNoProjIn bad e) :
    NoProjIn bad e = true :=
  infer_noProjIn_aux (teleExprDepth e) (Nat.le_refl _) hinf rfl hproj hfv

/-- Closed specialization: full-grade `Rules.Infer` on an fvar-free expression guarantees
`NoProjIn bad e = true`. -/
theorem infer_noProjIn {bad : List KKey} {env : Ix.Kernel.Env .anon}
    {d : Nat} {e t : KExpr} (hinf : Infer env .full d e t)
    (hproj : ∀ sn i entry, env.findProj? sn i = some entry → bad.contains sn = false)
    (hfv : e.hasFvar = false) :
    NoProjIn bad e = true :=
  infer_noProjIn_open hinf hproj (fvarNoProjIn_of_hasFvar_false hfv)

/-- Any intermediate environment `envX` extending `env₀` without adding projection tables preserves
the fact that no structure with a projection table belongs to a list of fresh block names. -/
theorem findProj_not_in_fresh_block {env₀ envX : Ix.Kernel.Env .anon} {blockNames : List KKey}
    (hstore : Ix.Kernel.Open.StoreInv env₀)
    (hfresh : ∀ n ∈ blockNames, env₀.find? n = none)
    (hproj_eq : ∀ sn, envX.find? (Ix.Kernel.projTableName sn) =
      env₀.find? (Ix.Kernel.projTableName sn)) :
    ∀ sn i entry, envX.findProj? sn i = some entry → blockNames.contains sn = false := by
  intro sn i entry hent
  obtain ⟨tbl, hfX, hi, _⟩ := Ix.Kernel.Env.findProj?_some hent
  have hf₀ : env₀.find? (Ix.Kernel.projTableName sn) = some (.projInfo tbl) := by
    rw [← hproj_eq sn]; exact hfX
  obtain ⟨_, _, _, ⟨cvT, caps, hT, _, _⟩, _⟩ := hstore.proj_ok _ tbl hf₀ i hi
  have hsn : tbl.structName = sn := by
    have hf' : env₀.consts.find? (fun x => x.name == Ix.Kernel.projTableName sn) =
        some (.projInfo tbl) := hf₀
    have hbeq : (ConstantInfo.projInfo tbl : ConstantInfo .anon).name ==
        Ix.Kernel.projTableName sn :=
      List.find?_some (p := fun x : ConstantInfo .anon => x.name == Ix.Kernel.projTableName sn) hf'
    exact Ix.Kernel.projTableName_inj (beq_iff_eq.mp hbeq)
  simp only [Ix.Kernel.ProjTable.entry, hsn] at hT
  by_cases hm : blockNames.contains sn = true
  · have hmem : sn ∈ blockNames := List.contains_iff_mem.mp hm
    rw [hfresh sn hmem] at hT
    exact nomatch hT
  · exact Bool.eq_false_iff.mpr hm

theorem renameAll_liftLooseBVars (f : KKey → KKey) :
  ∀ (e : KExpr) (n c : Nat),
    renameAll f (e.liftLooseBVars n c) = (renameAll f e).liftLooseBVars n c := by
  intro e
  induction e with
  | bvar i =>
    intro n c; simp only [renameAll, Expr.liftLooseBVars]; split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app a b iha ihb => intro n c; simp only [Expr.liftLooseBVars, renameAll, iha n c, ihb n c]
  | lam t b m iht ihb =>
    intro n c; simp only [Expr.liftLooseBVars, renameAll, iht n c, ihb n (c + 1)]
  | forallE t b m iht ihb =>
    intro n c; simp only [Expr.liftLooseBVars, renameAll, iht n c, ihb n (c + 1)]
  | letE t v b m iht ihv ihb =>
    intro n c; simp only [Expr.liftLooseBVars, renameAll, iht n c, ihv n c, ihb n (c + 1)]
  | proj s i e ih => intro n c; simp only [Expr.liftLooseBVars, renameAll, ih n c]

theorem renameAll_instantiate1Lift (f : KKey → KKey) {v : KExpr} :
    ∀ (e : KExpr) (d : Nat),
      renameAll f (e.instantiate1Lift v d) =
        (renameAll f e).instantiate1Lift (renameAll f v) d := by
  intro e
  induction e with
  | bvar i =>
    intro d
    simp only [renameAll, Expr.instantiate1Lift]
    split
    · exact renameAll_liftLooseBVars f v d 0
    · split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _; rfl
  | app a b iha ihb => intro d; simp only [Expr.instantiate1Lift, renameAll, iha d, ihb d]
  | lam t b m iht ihb =>
    intro d; simp only [Expr.instantiate1Lift, renameAll, iht d, ihb (d + 1)]
  | forallE t b m iht ihb =>
    intro d; simp only [Expr.instantiate1Lift, renameAll, iht d, ihb (d + 1)]
  | letE t va b m iht ihv ihb =>
    intro d; simp only [Expr.instantiate1Lift, renameAll, iht d, ihv d, ihb (d + 1)]
  | proj s i e ih => intro d; simp only [Expr.instantiate1Lift, renameAll, ih d]

theorem renameAll_instShift (f : KKey → KKey) (V : KExpr) (j : Nat) (B : KExpr) :
    renameAll f (instShift V j B) = instShift (renameAll f V) j (renameAll f B) :=
  renameAll_instantiate1Lift f B j

/-- Syntactic check that `e` has no loose de Bruijn variable in `[lo, lo + n)`. -/
def noLooseIn (lo n : Nat) : KExpr → Bool
  | .bvar i => decide (i < lo ∨ lo + n ≤ i)
  | .fvar _ _ | .sort _ | .const _ _ | .lit _ => true
  | .app f a => noLooseIn lo n f && noLooseIn lo n a
  | .lam ty b _ | .forallE ty b _ => noLooseIn lo n ty && noLooseIn (lo + 1) n b
  | .letE ty v b _ => noLooseIn lo n ty && noLooseIn lo n v && noLooseIn (lo + 1) n b
  | .proj _ _ e => noLooseIn lo n e

theorem liftLooseBVars_lowerBVars_of_noLooseIn {n : Nat} :
    ∀ {e : KExpr} {c : Nat}, noLooseIn c n e = true →
      (e.lowerBVars n c).liftLooseBVars n c = e := by
  intro e
  induction e with
  | bvar i =>
    intro c h
    simp only [noLooseIn, decide_eq_true_eq] at h
    rcases h with hlt | hge
    · have h1 : ¬ (i ≥ c + n) := by omega
      have h2 : ¬ (i ≥ c) := by omega
      show Expr.liftLooseBVars n c (if i ≥ c + n then Expr.bvar (i - n) else Expr.bvar i) = _
      rw [ite_eq_right h1]
      show (if i ≥ c then Expr.bvar (i + n) else Expr.bvar i) = Expr.bvar i
      exact ite_eq_right h2
    · show Expr.liftLooseBVars n c (if i ≥ c + n then Expr.bvar (i - n) else Expr.bvar i) = _
      rw [ite_eq_left (by omega)]
      show (if i - n ≥ c then Expr.bvar (i - n + n) else Expr.bvar (i - n)) = Expr.bvar i
      rw [ite_eq_left (by omega)]
      congr 1; omega
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro c h; simp only [noLooseIn, Bool.and_eq_true] at h
    simp only [Expr.lowerBVars, Expr.liftLooseBVars, ihf h.1, iha h.2]
  | lam t b m iht ihb =>
    intro c h; simp only [noLooseIn, Bool.and_eq_true] at h
    simp only [Expr.lowerBVars, Expr.liftLooseBVars, iht h.1, ihb h.2]
  | forallE t b m iht ihb =>
    intro c h; simp only [noLooseIn, Bool.and_eq_true] at h
    simp only [Expr.lowerBVars, Expr.liftLooseBVars, iht h.1, ihb h.2]
  | letE t v b m iht ihv ihb =>
    intro c h; simp only [noLooseIn, Bool.and_eq_true] at h
    simp only [Expr.lowerBVars, Expr.liftLooseBVars, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj s i e ih =>
    intro c h; simp only [noLooseIn] at h
    simp only [Expr.lowerBVars, Expr.liftLooseBVars, ih h]

theorem lowerBVars_eq_self_of_bounded {n : Nat} :
    ∀ {e : KExpr} {c : Nat}, e.looseBVarsBounded (c + n) = true → noLooseIn c n e = true →
      e.lowerBVars n c = e := by
  intro e
  induction e with
  | bvar i =>
    intro c hb hn
    simp only [Expr.looseBVarsBounded, noLooseIn, decide_eq_true_eq] at hb hn
    show (if i ≥ c + n then Expr.bvar (i - n) else Expr.bvar i) = Expr.bvar i
    exact ite_eq_right (by omega)
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _ _; rfl
  | app f a ihf iha =>
    intro c hb hn
    simp only [Expr.looseBVarsBounded, noLooseIn, Bool.and_eq_true] at hb hn
    simp only [Expr.lowerBVars, ihf hb.1 hn.1, iha hb.2 hn.2]
  | lam t b m iht ihb =>
    intro c hb hn
    simp only [Expr.looseBVarsBounded, noLooseIn, Bool.and_eq_true] at hb hn
    have hb' : b.looseBVarsBounded (c + 1 + n) = true := by
      rw [show c + 1 + n = c + n + 1 by omega]; exact hb.2
    simp only [Expr.lowerBVars, iht hb.1 hn.1, ihb hb' hn.2]
  | forallE t b m iht ihb =>
    intro c hb hn
    simp only [Expr.looseBVarsBounded, noLooseIn, Bool.and_eq_true] at hb hn
    have hb' : b.looseBVarsBounded (c + 1 + n) = true := by
      rw [show c + 1 + n = c + n + 1 by omega]; exact hb.2
    simp only [Expr.lowerBVars, iht hb.1 hn.1, ihb hb' hn.2]
  | letE t v b m iht ihv ihb =>
    intro c hb hn
    simp only [Expr.looseBVarsBounded, noLooseIn, Bool.and_eq_true] at hb hn
    have hb' : b.looseBVarsBounded (c + 1 + n) = true := by
      rw [show c + 1 + n = c + n + 1 by omega]; exact hb.2
    simp only [Expr.lowerBVars, iht hb.1.1 hn.1.1, ihv hb.1.2 hn.1.2, ihb hb' hn.2]
  | proj s i e ih =>
    intro c hb hn
    simp only [Expr.looseBVarsBounded, noLooseIn] at hb hn
    simp only [Expr.lowerBVars, ih hb hn]

private theorem noLooseIn_liftLooseBVars_zero {n : Nat} :
    ∀ {v : KExpr} {c : Nat} (d k : Nat), noLooseIn (c + k) n v = true →
      noLooseIn (c + d + k) n (v.liftLooseBVars d k) = true := by
  intro v
  induction v with
  | bvar i =>
    intro c d k h
    simp only [noLooseIn, decide_eq_true_eq] at h
    by_cases hik : i ≥ k
    · show noLooseIn (c + d + k) n (if i ≥ k then Expr.bvar (i + d) else Expr.bvar i) = true
      rw [ite_eq_left hik]
      simp only [noLooseIn, decide_eq_true_eq]; omega
    · show noLooseIn (c + d + k) n (if i ≥ k then Expr.bvar (i + d) else Expr.bvar i) = true
      rw [ite_eq_right hik]
      simp only [noLooseIn, decide_eq_true_eq]; omega
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _ _ _; rfl
  | app f a ihf iha =>
    intro c d k h; simp only [noLooseIn, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, noLooseIn, Bool.and_eq_true]
    exact ⟨ihf d k h.1, iha d k h.2⟩
  | lam t b m iht ihb =>
    intro c d k h; simp only [noLooseIn, Bool.and_eq_true] at h
    have hb := ihb (c := c) d (k + 1) (by rw [show c + (k + 1) = c + k + 1 by omega]; exact h.2)
    rw [show c + d + (k + 1) = c + d + k + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, noLooseIn, Bool.and_eq_true]
    exact ⟨iht d k h.1, hb⟩
  | forallE t b m iht ihb =>
    intro c d k h; simp only [noLooseIn, Bool.and_eq_true] at h
    have hb := ihb (c := c) d (k + 1) (by rw [show c + (k + 1) = c + k + 1 by omega]; exact h.2)
    rw [show c + d + (k + 1) = c + d + k + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, noLooseIn, Bool.and_eq_true]
    exact ⟨iht d k h.1, hb⟩
  | letE t v b m iht ihv ihb =>
    intro c d k h; simp only [noLooseIn, Bool.and_eq_true] at h
    have hb := ihb (c := c) d (k + 1) (by rw [show c + (k + 1) = c + k + 1 by omega]; exact h.2)
    rw [show c + d + (k + 1) = c + d + k + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, noLooseIn, Bool.and_eq_true]
    exact ⟨⟨iht d k h.1.1, ihv d k h.1.2⟩, hb⟩
  | proj s i e ih =>
    intro c d k h; simp only [noLooseIn] at h
    simp only [Expr.liftLooseBVars, noLooseIn]; exact ih d k h

private theorem lowerBVars_liftLooseBVars_comm {n : Nat} :
    ∀ {v : KExpr} {c : Nat} (d k : Nat), noLooseIn (c + k) n v = true →
      (v.liftLooseBVars d k).lowerBVars n (c + d + k) =
        (v.lowerBVars n (c + k)).liftLooseBVars d k := by
  intro v
  induction v with
  | bvar i =>
    intro c d k h
    simp only [noLooseIn, decide_eq_true_eq] at h
    by_cases hik : i ≥ k
    · show Expr.lowerBVars n (c + d + k) (if i ≥ k then Expr.bvar (i + d) else Expr.bvar i) =
        Expr.liftLooseBVars d k (if i ≥ c + k + n then Expr.bvar (i - n) else Expr.bvar i)
      rw [ite_eq_left hik]
      rcases h with hlt | hge
      · rw [ite_eq_right (by omega)]
        show (if i + d ≥ c + d + k + n then Expr.bvar (i + d - n) else Expr.bvar (i + d)) =
          (if i ≥ k then Expr.bvar (i + d) else Expr.bvar i)
        rw [ite_eq_right (by omega), ite_eq_left hik]
      · rw [ite_eq_left (by omega)]
        show (if i + d ≥ c + d + k + n then Expr.bvar (i + d - n) else Expr.bvar (i + d)) =
          (if i - n ≥ k then Expr.bvar (i - n + d) else Expr.bvar (i - n))
        rw [ite_eq_left (by omega), ite_eq_left (by omega)]
        congr 1; omega
    · show Expr.lowerBVars n (c + d + k) (if i ≥ k then Expr.bvar (i + d) else Expr.bvar i) =
        Expr.liftLooseBVars d k (if i ≥ c + k + n then Expr.bvar (i - n) else Expr.bvar i)
      rw [ite_eq_right hik, ite_eq_right (by omega)]
      show (if i ≥ c + d + k + n then Expr.bvar (i - n) else Expr.bvar i) =
        (if i ≥ k then Expr.bvar (i + d) else Expr.bvar i)
      rw [ite_eq_right (by omega), ite_eq_right hik]
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _ _ _; rfl
  | app f a ihf iha =>
    intro c d k h; simp only [noLooseIn, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.lowerBVars, ihf d k h.1, iha d k h.2]
  | lam t b m iht ihb =>
    intro c d k h; simp only [noLooseIn, Bool.and_eq_true] at h
    have hb := ihb (c := c) d (k + 1) (by rw [show c + (k + 1) = c + k + 1 by omega]; exact h.2)
    rw [show c + d + (k + 1) = c + d + k + 1 by omega,
        show c + (k + 1) = c + k + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, Expr.lowerBVars, iht d k h.1, hb]
  | forallE t b m iht ihb =>
    intro c d k h; simp only [noLooseIn, Bool.and_eq_true] at h
    have hb := ihb (c := c) d (k + 1) (by rw [show c + (k + 1) = c + k + 1 by omega]; exact h.2)
    rw [show c + d + (k + 1) = c + d + k + 1 by omega,
        show c + (k + 1) = c + k + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, Expr.lowerBVars, iht d k h.1, hb]
  | letE t v b m iht ihv ihb =>
    intro c d k h; simp only [noLooseIn, Bool.and_eq_true] at h
    have hb := ihb (c := c) d (k + 1) (by rw [show c + (k + 1) = c + k + 1 by omega]; exact h.2)
    rw [show c + d + (k + 1) = c + d + k + 1 by omega,
        show c + (k + 1) = c + k + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, Expr.lowerBVars, iht d k h.1.1, ihv d k h.1.2, hb]
  | proj s i e ih =>
    intro c d k h; simp only [noLooseIn] at h
    simp only [Expr.liftLooseBVars, Expr.lowerBVars, ih d k h]

private theorem noLooseIn_instantiate1Lift {n c : Nat} {v : KExpr} (hv : noLooseIn c n v = true) :
    ∀ {b : KExpr} (d : Nat), noLooseIn (c + d + 1) n b = true →
      noLooseIn (c + d) n (b.instantiate1Lift v d) = true := by
  intro b
  induction b with
  | bvar i =>
    intro d hb
    simp only [noLooseIn, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1Lift]
    by_cases hid : i = d
    · subst hid
      rw [ite_eq_left rfl]
      simpa using noLooseIn_liftLooseBVars_zero (c := c) i 0 (by simpa using hv)
    · rw [ite_eq_right hid]
      by_cases hgt : i > d
      · rw [ite_eq_left hgt]; simp only [noLooseIn, decide_eq_true_eq]; omega
      · rw [ite_eq_right hgt]; simp only [noLooseIn, decide_eq_true_eq]; omega
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro d hb; simp only [noLooseIn, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, noLooseIn, Bool.and_eq_true]
    exact ⟨ihf d hb.1, iha d hb.2⟩
  | lam t b m iht ihb =>
    intro d hb; simp only [noLooseIn, Bool.and_eq_true] at hb
    have hb' := ihb (d + 1) (by rw [show c + (d + 1) + 1 = c + d + 1 + 1 by omega]; exact hb.2)
    rw [show c + (d + 1) = c + d + 1 by omega] at hb'
    simp only [Expr.instantiate1Lift, noLooseIn, Bool.and_eq_true]
    exact ⟨iht d hb.1, hb'⟩
  | forallE t b m iht ihb =>
    intro d hb; simp only [noLooseIn, Bool.and_eq_true] at hb
    have hb' := ihb (d + 1) (by rw [show c + (d + 1) + 1 = c + d + 1 + 1 by omega]; exact hb.2)
    rw [show c + (d + 1) = c + d + 1 by omega] at hb'
    simp only [Expr.instantiate1Lift, noLooseIn, Bool.and_eq_true]
    exact ⟨iht d hb.1, hb'⟩
  | letE t va b m iht ihv ihb =>
    intro d hb; simp only [noLooseIn, Bool.and_eq_true] at hb
    have hb' := ihb (d + 1) (by rw [show c + (d + 1) + 1 = c + d + 1 + 1 by omega]; exact hb.2)
    rw [show c + (d + 1) = c + d + 1 by omega] at hb'
    simp only [Expr.instantiate1Lift, noLooseIn, Bool.and_eq_true]
    exact ⟨⟨iht d hb.1.1, ihv d hb.1.2⟩, hb'⟩
  | proj s i e ih =>
    intro d hb; simp only [noLooseIn] at hb
    simp only [Expr.instantiate1Lift, noLooseIn]; exact ih d hb

private theorem lowerBVars_instantiate1Lift {n c : Nat} {v : KExpr} (hv : noLooseIn c n v = true) :
    ∀ {b : KExpr} (d : Nat), noLooseIn (c + d + 1) n b = true →
      (b.instantiate1Lift v d).lowerBVars n (c + d) =
        (b.lowerBVars n (c + d + 1)).instantiate1Lift (v.lowerBVars n c) d := by
  intro b
  induction b with
  | bvar i =>
    intro d hb
    simp only [noLooseIn, decide_eq_true_eq] at hb
    by_cases hid : i = d
    · subst hid
      have h1 : (Expr.bvar i : KExpr).instantiate1Lift v i = v.liftLooseBVars i 0 := by
        simp [Expr.instantiate1Lift]
      have h2 : (Expr.bvar i : KExpr).lowerBVars n (c + i + 1) = Expr.bvar i := by
        show (if i ≥ c + i + 1 + n then _ else _) = _; exact ite_eq_right (by omega)
      rw [h1, h2]
      simp only [Expr.instantiate1Lift, ite_eq_left rfl]
      simpa using lowerBVars_liftLooseBVars_comm (c := c) i 0 (by simpa using hv)
    · by_cases hgt : i > d
      · have h1 : (Expr.bvar i : KExpr).instantiate1Lift v d = Expr.bvar (i - 1) := by
          show (if i = d then _ else if i > d then _ else _) = _
          rw [ite_eq_right hid, ite_eq_left hgt]
        rw [h1]
        rcases hb with hlt | hge
        · have hl1 : (Expr.bvar (i - 1) : KExpr).lowerBVars n (c + d) = Expr.bvar (i - 1) := by
            show (if i - 1 ≥ c + d + n then _ else _) = _; exact ite_eq_right (by omega)
          have hl2 : (Expr.bvar i : KExpr).lowerBVars n (c + d + 1) = Expr.bvar i := by
            show (if i ≥ c + d + 1 + n then _ else _) = _; exact ite_eq_right (by omega)
          rw [hl1, hl2]
          show Expr.bvar (i - 1) = (if i = d then _ else if i > d then _ else _)
          rw [ite_eq_right hid, ite_eq_left hgt]
        · have hl1 : (Expr.bvar (i - 1) : KExpr).lowerBVars n (c + d) = Expr.bvar (i - 1 - n) := by
            show (if i - 1 ≥ c + d + n then _ else _) = _; exact ite_eq_left (by omega)
          have hl2 : (Expr.bvar i : KExpr).lowerBVars n (c + d + 1) = Expr.bvar (i - n) := by
            show (if i ≥ c + d + 1 + n then _ else _) = _; exact ite_eq_left (by omega)
          rw [hl1, hl2]
          show Expr.bvar (i - 1 - n) = (if i - n = d then _ else if i - n > d then _ else _)
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
          congr 1; omega
      · have h1 : (Expr.bvar i : KExpr).instantiate1Lift v d = Expr.bvar i := by
          show (if i = d then _ else if i > d then _ else _) = _
          rw [ite_eq_right hid, ite_eq_right hgt]
        have hl1 : (Expr.bvar i : KExpr).lowerBVars n (c + d) = Expr.bvar i := by
          show (if i ≥ c + d + n then _ else _) = _; exact ite_eq_right (by omega)
        have hl2 : (Expr.bvar i : KExpr).lowerBVars n (c + d + 1) = Expr.bvar i := by
          show (if i ≥ c + d + 1 + n then _ else _) = _; exact ite_eq_right (by omega)
        have h3 : (Expr.bvar i : KExpr).instantiate1Lift (v.lowerBVars n c) d = Expr.bvar i := by
          show (if i = d then _ else if i > d then _ else _) = _
          rw [ite_eq_right hid, ite_eq_right hgt]
        rw [h1, hl1, hl2, h3]
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro d hb; simp only [noLooseIn, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, Expr.lowerBVars, ihf d hb.1, iha d hb.2]
  | lam t b m iht ihb =>
    intro d hb; simp only [noLooseIn, Bool.and_eq_true] at hb
    have hb' := ihb (d + 1) (by rw [show c + (d + 1) + 1 = c + d + 1 + 1 by omega]; exact hb.2)
    rw [show c + (d + 1) = c + d + 1 by omega] at hb'
    simp only [Expr.instantiate1Lift, Expr.lowerBVars, iht d hb.1, hb']
  | forallE t b m iht ihb =>
    intro d hb; simp only [noLooseIn, Bool.and_eq_true] at hb
    have hb' := ihb (d + 1) (by rw [show c + (d + 1) + 1 = c + d + 1 + 1 by omega]; exact hb.2)
    rw [show c + (d + 1) = c + d + 1 by omega] at hb'
    simp only [Expr.instantiate1Lift, Expr.lowerBVars, iht d hb.1, hb']
  | letE t va b m iht ihv ihb =>
    intro d hb; simp only [noLooseIn, Bool.and_eq_true] at hb
    have hb' := ihb (d + 1) (by rw [show c + (d + 1) + 1 = c + d + 1 + 1 by omega]; exact hb.2)
    rw [show c + (d + 1) = c + d + 1 by omega] at hb'
    simp only [Expr.instantiate1Lift, Expr.lowerBVars, iht d hb.1.1, ihv d hb.1.2, hb']
  | proj s i e ih =>
    intro d hb; simp only [noLooseIn] at hb
    simp only [Expr.instantiate1Lift, Expr.lowerBVars, ih d hb]

theorem liftLooseBVars_zero (e : KExpr) : ∀ c : Nat, e.liftLooseBVars 0 c = e := by
  intro c
  induction e generalizing c with
  | bvar i =>
    show (if i ≥ c then Expr.bvar (i + 0) else Expr.bvar i) = Expr.bvar i
    split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => rfl
  | app f a ihf iha => simp only [Expr.liftLooseBVars, ihf c, iha c]
  | lam t b m iht ihb => simp only [Expr.liftLooseBVars, iht c, ihb (c + 1)]
  | forallE t b m iht ihb => simp only [Expr.liftLooseBVars, iht c, ihb (c + 1)]
  | letE t v b m iht ihv ihb => simp only [Expr.liftLooseBVars, iht c, ihv c, ihb (c + 1)]
  | proj s i e ih => simp only [Expr.liftLooseBVars, ih c]

theorem noLooseIn_instShift_zero {n c : Nat} {v b : KExpr}
    (hv : noLooseIn c n v = true) (hb : noLooseIn (c + 1) n b = true) :
    noLooseIn c n (instShift v 0 b) = true := by
  simpa using noLooseIn_instantiate1Lift hv 0 (by simpa using hb)

theorem lowerBVars_instShift_zero {n c : Nat} {v b : KExpr}
    (hv : noLooseIn c n v = true) (hb : noLooseIn (c + 1) n b = true) :
    (instShift v 0 b).lowerBVars n c =
      instShift (v.lowerBVars n c) 0 (b.lowerBVars n (c + 1)) := by
  simpa using lowerBVars_instantiate1Lift hv 0 (by simpa using hb)

theorem hasFvar_lowerBVars (n : Nat) :
    ∀ (e : KExpr) (c : Nat), (e.lowerBVars n c).hasFvar = e.hasFvar := by
  intro e
  induction e with
  | bvar i => intro c; simp only [Expr.lowerBVars]; split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _; rfl
  | app f a ihf iha => intro c; simp only [Expr.lowerBVars, Expr.hasFvar, ihf c, iha c]
  | lam t b _ iht ihb => intro c; simp only [Expr.lowerBVars, Expr.hasFvar, iht c, ihb (c + 1)]
  | forallE t b _ iht ihb => intro c; simp only [Expr.lowerBVars, Expr.hasFvar, iht c, ihb (c + 1)]
  | letE t v b _ iht ihv ihb =>
    intro c; simp only [Expr.lowerBVars, Expr.hasFvar, iht c, ihv c, ihb (c + 1)]
  | proj _ _ e ih => intro c; simp only [Expr.lowerBVars, Expr.hasFvar, ih c]

theorem looseBVarsBounded_lowerBVars {n : Nat} :
    ∀ {e : KExpr} {c rp : Nat}, noLooseIn c n e = true →
      e.looseBVarsBounded (rp + c + n) = true →
      (e.lowerBVars n c).looseBVarsBounded (rp + c) = true := by
  intro e
  induction e with
  | bvar i =>
    intro c rp hn hb
    simp only [noLooseIn, Expr.looseBVarsBounded, decide_eq_true_eq] at hn hb
    by_cases hge : i ≥ c + n
    · show Expr.looseBVarsBounded (rp + c) (if i ≥ c + n then Expr.bvar (i - n) else Expr.bvar i) = true
      rw [ite_eq_left hge]
      simp only [Expr.looseBVarsBounded, decide_eq_true_eq]; omega
    · show Expr.looseBVarsBounded (rp + c) (if i ≥ c + n then Expr.bvar (i - n) else Expr.bvar i) = true
      rw [ite_eq_right hge]
      simp only [Expr.looseBVarsBounded, decide_eq_true_eq]; omega
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _ _ _; rfl
  | app f a ihf iha =>
    intro c rp hn hb
    simp only [noLooseIn, Expr.looseBVarsBounded, Bool.and_eq_true] at hn hb
    simp only [Expr.lowerBVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihf hn.1 hb.1, iha hn.2 hb.2⟩
  | lam t b _ iht ihb =>
    intro c rp hn hb
    simp only [noLooseIn, Expr.looseBVarsBounded, Bool.and_eq_true] at hn hb
    have hb' : b.looseBVarsBounded (rp + (c + 1) + n) = true := by
      rw [show rp + (c + 1) + n = rp + c + n + 1 by omega]; exact hb.2
    have ih' := ihb (rp := rp) hn.2 hb'
    rw [show rp + (c + 1) = rp + c + 1 by omega] at ih'
    simp only [Expr.lowerBVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht hn.1 hb.1, ih'⟩
  | forallE t b _ iht ihb =>
    intro c rp hn hb
    simp only [noLooseIn, Expr.looseBVarsBounded, Bool.and_eq_true] at hn hb
    have hb' : b.looseBVarsBounded (rp + (c + 1) + n) = true := by
      rw [show rp + (c + 1) + n = rp + c + n + 1 by omega]; exact hb.2
    have ih' := ihb (rp := rp) hn.2 hb'
    rw [show rp + (c + 1) = rp + c + 1 by omega] at ih'
    simp only [Expr.lowerBVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht hn.1 hb.1, ih'⟩
  | letE t v b _ iht ihv ihb =>
    intro c rp hn hb
    simp only [noLooseIn, Expr.looseBVarsBounded, Bool.and_eq_true] at hn hb
    have hb' : b.looseBVarsBounded (rp + (c + 1) + n) = true := by
      rw [show rp + (c + 1) + n = rp + c + n + 1 by omega]; exact hb.2
    have ih' := ihb (rp := rp) hn.2 hb'
    rw [show rp + (c + 1) = rp + c + 1 by omega] at ih'
    simp only [Expr.lowerBVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨iht hn.1.1 hb.1.1, ihv hn.1.2 hb.1.2⟩, ih'⟩
  | proj _ _ e ih =>
    intro c rp hn hb
    simp only [noLooseIn, Expr.looseBVarsBounded] at hn hb
    simp only [Expr.lowerBVars, Expr.looseBVarsBounded]; exact ih hn hb

theorem allLevelParamsDefined_lowerBVars (n : Nat) (ps : List LevelParam) :
    ∀ (e : KExpr) (c : Nat),
      (e.lowerBVars n c).allLevelParamsDefined ps = e.allLevelParamsDefined ps := by
  intro e
  induction e with
  | bvar i => intro c; simp only [Expr.lowerBVars]; split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _; rfl
  | app f a ihf iha =>
    intro c; simp only [Expr.lowerBVars, Expr.allLevelParamsDefined, ihf c, iha c]
  | lam t b m iht ihb =>
    intro c; simp only [Expr.lowerBVars, Expr.allLevelParamsDefined, iht c, ihb (c + 1)]
  | forallE t b m iht ihb =>
    intro c; simp only [Expr.lowerBVars, Expr.allLevelParamsDefined, iht c, ihb (c + 1)]
  | letE t v b m iht ihv ihb =>
    intro c; simp only [Expr.lowerBVars, Expr.allLevelParamsDefined, iht c, ihv c, ihb (c + 1)]
  | proj _ _ e ih =>
    intro c; simp only [Expr.lowerBVars, Expr.allLevelParamsDefined, ih c]

/-! ## Level-parameter instantiation (`instantiateLevelParams` / `posOf`) commutation -/

theorem instantiateLevelParams_instantiate1_gen (ks : List LevelParam) (us : List KLevel)
    (v : KExpr) :
    ∀ (e : KExpr) (k : Nat),
      (e.instantiate1 v k).instantiateLevelParams ks us =
        (e.instantiateLevelParams ks us).instantiate1 (v.instantiateLevelParams ks us) k := by
  intro e
  induction e with
  | bvar i =>
    intro k; simp only [Expr.instantiate1, Expr.instantiateLevelParams]
    split
    · rfl
    · split <;> rfl
  | _ => intro k; simp_all [Expr.instantiate1, Expr.instantiateLevelParams]

theorem instantiateLevelParams_liftLooseBVars (ks : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr) (n c : Nat),
      (e.liftLooseBVars n c).instantiateLevelParams ks us =
        (e.instantiateLevelParams ks us).liftLooseBVars n c := by
  intro e
  induction e with
  | bvar i =>
    intro n c; simp only [Expr.liftLooseBVars, Expr.instantiateLevelParams]; split <;> rfl
  | _ => intro n c; simp_all [Expr.liftLooseBVars, Expr.instantiateLevelParams]

theorem instantiateLevelParams_lowerBVars (ks : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr) (n c : Nat),
      (e.lowerBVars n c).instantiateLevelParams ks us =
        (e.instantiateLevelParams ks us).lowerBVars n c := by
  intro e
  induction e with
  | bvar i =>
    intro n c; simp only [Expr.lowerBVars, Expr.instantiateLevelParams]; split <;> rfl
  | _ => intro n c; simp_all [Expr.lowerBVars, Expr.instantiateLevelParams]

theorem instantiateLevelParams_renameConsts (ks : List LevelParam) (us : List KLevel)
    (f : KKey → KKey) :
    ∀ e : KExpr,
      (e.renameConsts f).instantiateLevelParams ks us =
        (e.instantiateLevelParams ks us).renameConsts f := by
  intro e
  induction e <;> simp_all [Expr.renameConsts, Expr.instantiateLevelParams]

theorem instantiateLevelParams_fvarTypeD (ks : List LevelParam) (us : List KLevel) :
    ∀ e : KExpr,
      e.fvarTypeD.instantiateLevelParams ks us =
        (e.instantiateLevelParams ks us).fvarTypeD := by
  intro e
  cases e <;> rfl

theorem instantiateLevelParams_instSpine (ks : List LevelParam) (us : List KLevel) :
    ∀ (args : List KExpr) (t : Nat) (e : KExpr),
      (Expr.instSpine args t e).instantiateLevelParams ks us =
        Expr.instSpine (args.map (·.instantiateLevelParams ks us)) t
          (e.instantiateLevelParams ks us)
  | [], _, _ => rfl
  | a :: as, t, e => by
    simp only [Expr.instSpine, List.map_cons,
      instantiateLevelParams_instSpine ks us as (t - 1),
      instantiateLevelParams_instantiate1_gen]

theorem openPisAtFvars_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (n : Nat) (e : KExpr) (i : Nat),
      Ix.Kernel.openPisAtFvars n (e.instantiateLevelParams ks us) i =
        (Ix.Kernel.openPisAtFvars n e i).map (fun p =>
          (p.1.map (·.instantiateLevelParams ks us), p.2.instantiateLevelParams ks us))
  | 0, _, _ => rfl
  | n + 1, .forallE dom body m, i => by
    simp only [Expr.instantiateLevelParams, Ix.Kernel.openPisAtFvars,
      ← Expr.instantiateLevelParams_instantiate1 ks us body 0,
      openPisAtFvars_instantiateLevelParams ks us n (body.instantiate1 (.fvar i dom)) (i + 1)]
    cases Ix.Kernel.openPisAtFvars n (body.instantiate1 (.fvar i dom)) (i + 1) <;> rfl
  | _ + 1, .bvar _, _ | _ + 1, .fvar _ _, _ | _ + 1, .sort _, _ | _ + 1, .const _ _, _
  | _ + 1, .app _ _, _ | _ + 1, .lam _ _ _, _ | _ + 1, .letE _ _ _ _, _ | _ + 1, .lit _, _
  | _ + 1, .proj _ _ _, _ => rfl

theorem instPisAt_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (args : List KExpr) (e : KExpr),
      Expr.instPisAt (args.map (·.instantiateLevelParams ks us))
          (e.instantiateLevelParams ks us) =
        (Expr.instPisAt args e).map (fun p =>
          (p.1.map (·.instantiateLevelParams ks us), p.2.instantiateLevelParams ks us))
  | [], _ => rfl
  | a :: as, .forallE dom body m => by
    simp only [List.map_cons, Expr.instantiateLevelParams, Expr.instPisAt,
      ← instantiateLevelParams_instantiate1_gen ks us a body 0,
      instPisAt_instantiateLevelParams ks us as (body.instantiate1 a)]
    cases Expr.instPisAt as (body.instantiate1 a) <;> rfl
  | _ :: _, .bvar _ | _ :: _, .fvar _ _ | _ :: _, .sort _ | _ :: _, .const _ _
  | _ :: _, .app _ _ | _ :: _, .lam _ _ _ | _ :: _, .letE _ _ _ _ | _ :: _, .lit _
  | _ :: _, .proj _ _ _ => rfl

theorem instLamsAt_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (args : List KExpr) (e : KExpr),
      Expr.instLamsAt (args.map (·.instantiateLevelParams ks us))
          (e.instantiateLevelParams ks us) =
        (Expr.instLamsAt args e).map (fun p =>
          (p.1.map (·.instantiateLevelParams ks us), p.2.instantiateLevelParams ks us))
  | [], _ => rfl
  | a :: as, .lam dom body m => by
    simp only [List.map_cons, Expr.instantiateLevelParams, Expr.instLamsAt,
      ← instantiateLevelParams_instantiate1_gen ks us a body 0,
      instLamsAt_instantiateLevelParams ks us as (body.instantiate1 a)]
    cases Expr.instLamsAt as (body.instantiate1 a) <;> rfl
  | _ :: _, .bvar _ | _ :: _, .fvar _ _ | _ :: _, .sort _ | _ :: _, .const _ _
  | _ :: _, .app _ _ | _ :: _, .forallE _ _ _ | _ :: _, .letE _ _ _ _ | _ :: _, .lit _
  | _ :: _, .proj _ _ _ => rfl

theorem stripLams_instantiateLevelParams_isSome (ks : List LevelParam) (us : List KLevel) :
    ∀ (k : Nat) (e : KExpr),
      ((e.instantiateLevelParams ks us).stripLams k).isSome = (e.stripLams k).isSome
  | 0, _ => rfl
  | k + 1, .lam _ body _ => by
    simp only [Expr.instantiateLevelParams, Expr.stripLams, Option.isSome_map]
    exact stripLams_instantiateLevelParams_isSome ks us k body
  | _ + 1, .bvar _ | _ + 1, .fvar _ _ | _ + 1, .sort _ | _ + 1, .const _ _
  | _ + 1, .app _ _ | _ + 1, .forallE _ _ _ | _ + 1, .letE _ _ _ _ | _ + 1, .lit _
  | _ + 1, .proj _ _ _ => rfl

theorem stripPis_instantiateLevelParams_full (ks : List LevelParam) (us : List KLevel) :
    ∀ (k : Nat) (e : KExpr),
      (e.instantiateLevelParams ks us).stripPis k =
        (e.stripPis k).map (fun p =>
          (p.1.map (fun bm =>
            (bm.1.instantiateLevelParams ks us, { bm.2 with pw := Level.substPW ks us bm.2.pw })),
           p.2.instantiateLevelParams ks us))
  | 0, _ => rfl
  | k + 1, .forallE ty b m => by
    simp only [Expr.instantiateLevelParams, Expr.stripPis,
      stripPis_instantiateLevelParams_full ks us k b]
    cases b.stripPis k <;> rfl
  | _ + 1, .bvar _ | _ + 1, .fvar _ _ | _ + 1, .sort _ | _ + 1, .const _ _
  | _ + 1, .app _ _ | _ + 1, .lam _ _ _ | _ + 1, .letE _ _ _ _ | _ + 1, .lit _
  | _ + 1, .proj _ _ _ => rfl

theorem ctorTeleOk_instantiateLevelParams (ks : List LevelParam) (us : List KLevel)
    (e : KExpr) (k : Nat) :
    Expr.ctorTeleOk (e.instantiateLevelParams ks us) k = Expr.ctorTeleOk e k := by
  unfold Expr.ctorTeleOk
  rw [stripPis_instantiateLevelParams_full]
  cases e.stripPis k with
  | none => rfl
  | some p =>
    simp only [Option.map_some, Expr.getAppFn_instantiateLevelParams]
    cases p.2.getAppFn <;> rfl

theorem isEqHead_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) (e : KExpr) :
    Ix.Kernel.isEqHead (e.instantiateLevelParams ks us) = Ix.Kernel.isEqHead e := by
  cases e with
  | const c ls =>
    cases ls with
    | nil => rfl
    | cons l rest =>
      cases rest <;> rfl
  | _ => rfl

theorem instantiateLevelParams_comp {ks ps : List LevelParam} {us vs : List KLevel}
    (hlen : vs.length = ps.length) :
    ∀ {e : KExpr}, e.allLevelParamsDefined ps = true →
      (e.instantiateLevelParams ps vs).instantiateLevelParams ks us =
        e.instantiateLevelParams ps (vs.map (Level.subst ks us)) := by
  intro e
  induction e with
  | bvar _ | lit _ => intro _; rfl
  | fvar i ty ih =>
    intro h; simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams, ih h]
  | sort u =>
    intro h; simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams, Level.subst_subst hlen h]
  | const n ls =>
    intro h; simp only [Expr.allLevelParamsDefined, List.all_eq_true] at h
    simp only [Expr.instantiateLevelParams, List.map_map]
    congr 1
    exact List.map_congr_left fun l hl => Level.subst_subst hlen (h l hl)
  | app f a ihf iha =>
    intro h; simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, ihf h.1, iha h.2]
  | lam ty bo m iht ihb =>
    intro h; simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, iht h.1.1, ihb h.1.2,
      Level.substPW_comp hlen h.2]
  | forallE ty bo m iht ihb =>
    intro h; simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, iht h.1.1, ihb h.1.2,
      Level.substPW_comp hlen h.2]
  | letE ty v bo m iht ihv ihb =>
    intro h; simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj s i e ih =>
    intro h; simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams, ih h]

theorem map_subst_range_posLevels {ps : List LevelParam} {us : List KLevel}
    (hlen : us.length = ps.length) :
    (posLevels ps).map (Level.subst (List.range us.length) us) = us := by
  unfold posLevels
  rw [← hlen, List.map_map]
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  simp only [List.length_map, List.length_range] at hi₁
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
  have hget := InferAux.getElem?_eq_subst_go_range (us := us) hi₁
  rw [List.getElem?_eq_getElem hi₁] at hget
  exact (Option.some.inj hget).symm

/-- Instantiating positional level parameters on `posOf cjps e` equals `posOf lps` applied to
`e.instantiateLevelParams cjps lvls` whenever `e.allLevelParamsDefined cjps = true` and
`lvls.length = cjps.length`. -/
theorem posOf_instantiateLevelParams_eq {cjps lps : List LevelParam} {lvls : List KLevel}
    {e : KExpr} (hlen : lvls.length = cjps.length) (hdef : e.allLevelParamsDefined cjps = true) :
    let lvls_pos := lvls.map (Level.subst lps (posLevels lps))
    (posOf cjps e).instantiateLevelParams (List.range lvls_pos.length) lvls_pos =
      posOf lps (e.instantiateLevelParams cjps lvls) := by
  dsimp only
  unfold posOf
  have hpos_len : (posLevels cjps).length = cjps.length := by simp [posLevels]
  have hmap_len : (lvls.map (Level.subst lps (posLevels lps))).length = cjps.length := by
    simp [hlen]
  rw [instantiateLevelParams_comp hpos_len hdef,
    map_subst_range_posLevels hmap_len,
    instantiateLevelParams_comp hlen hdef]

theorem erasedEq_of_posOf_eq {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {a b : KExpr} (h : posOf ps a = posOf ps b) : Expr.ErasedEq a b :=
  Expr.ErasedEq.of_eq (posOf_inj hperm h)

/-! ## `TmExact` opening, ghost congruence, store constructors, and exact `Subst` helpers -/

theorem TmExact.congr_ghost {κ : _root_.Address → KKey} {d : Nat} {Γ₁ Γ₂ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F} (hΓ : ∀ j < d, Γ₁ j = Γ₂ j)
    (rep : TmExact κ d Γ₁ h k E p) : TmExact κ d Γ₂ h k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
  | @bvarFree k' addr i cell hs hk hd =>
    have hlt : fvIdx d k' (ZMod.val i) < d := by unfold fvIdx; omega
    rw [hΓ _ hlt]
    exact .bvarFree cell hs hk hd
  | sort cell rl => exact .sort cell rl
  | const cell ra rls => exact .const cell ra rls
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

theorem TmExact.open {κ : _root_.Address → KKey} {d : Nat} {Γ Γ' : Nat → KExpr} {h : Heap F}
    {T : KExpr} (hT : Γ' d = T) (hΓ : ∀ j, j < d → Γ' j = Γ j) {k' : Nat} {E : KExpr}
    {p : SourceValue F} (rep : TmExact κ d Γ h k' E p) :
    ∀ k, k' = k + 1 → TmExact κ (d + 1) Γ' h k (E.instantiate1 (.fvar d T) k) p := by
  induction rep with
  | @bvarLocal k₁ addr i cell hs hi =>
    intro k hk
    subst hk
    simp only [Expr.instantiate1]
    by_cases hik : ZMod.val i = k
    · rw [ite_eq_left hik]
      have hf := TmExact.bvarFree (κ := κ) (d := d + 1) (Γ := Γ') (k := k) cell hs (by omega)
        (by omega)
      have e : fvIdx (d + 1) k (ZMod.val i) = d := by unfold fvIdx; omega
      rw [e, hT] at hf
      exact hf
    · rw [ite_eq_right hik, ite_eq_right (by omega)]
      exact .bvarLocal cell hs (by omega)
  | @bvarFree k₁ addr i cell hs hk hd =>
    intro k hk'
    subst hk'
    simp only [Expr.instantiate1]
    have hf := TmExact.bvarFree (κ := κ) (d := d + 1) (Γ := Γ') (k := k) cell hs (by omega)
      (by omega)
    have e : fvIdx (d + 1) k (ZMod.val i) = fvIdx d (k + 1) (ZMod.val i) := by
      unfold fvIdx; omega
    rw [e, hΓ _ (by unfold fvIdx; omega)] at hf
    exact hf
  | sort cell rl => intro k _; exact .sort cell rl
  | const cell ra rls => intro k _; exact .const cell ra rls
  | app cell _ _ ihf iha =>
    intro k hk
    simp only [Expr.instantiate1]
    exact .app cell (ihf k hk) (iha k hk)
  | lam cell _ _ rl iht ihb =>
    intro k hk
    simp only [Expr.instantiate1]
    exact .lam cell (iht k hk) (ihb (k + 1) (by omega)) rl
  | forallE cell _ _ rl iht ihb =>
    intro k hk
    simp only [Expr.instantiate1]
    exact .forallE cell (iht k hk) (ihb (k + 1) (by omega)) rl
  | @letE k₁ addr tp vp bp T₀ V B cell _ _ _ iht ihv ihb =>
    intro k hk
    have hcomm := Expr.instantiate1Lift_instantiate1 (a := V) (s := (.fvar d T : KExpr))
      (by simp [Expr.looseBVarsBounded]) B 0 k
    simp only [Nat.zero_add] at hcomm
    rw [show (instShift V 0 B).instantiate1 (.fvar d T) k =
        (B.instantiate1Lift V 0).instantiate1 (.fvar d T) k from rfl, hcomm,
      Nat.add_comm 1 k]
    exact .letE cell (iht k hk) (ihv k hk) (ihb (k + 1) (by omega))
  | litNat cell rl hc => intro k _; exact .litNat cell rl hc
  | litStr cell rb hs => intro k _; exact .litStr cell rb hs
  | proj cell ra _ ihe =>
    intro k hk
    simp only [Expr.instantiate1]
    exact .proj cell ra (ihe k hk)

theorem TmExact.open_body {κ : _root_.Address → KKey} {d : Nat} {Γ Γ' : Nat → KExpr} {h : Heap F}
    {T B : KExpr} {p : SourceValue F} (hT : Γ' d = T) (hΓ : ∀ j, j < d → Γ' j = Γ j)
    (rep : TmExact κ d Γ h 1 B p) : TmExact κ (d + 1) Γ' h 0 (B.instantiate1 (.fvar d T)) p :=
  rep.open hT hΓ 0 rfl

/-- Opening a closed local-context expression (`d = 0, k = n`) step-by-step at the ambient opened
variables `0, …, n - 1` produces `Expr.instSpine` with ZERO heap allocation. -/
private theorem tmExact_open_prefix {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} :
    ∀ (n : Nat) {k : Nat} {E : KExpr} {p : SourceValue F},
      TmExact κ 0 (fun _ => .sort .zero) h (k + n) E p →
      TmExact κ n Γ h k
        (Expr.instSpine ((List.range n).map fun j => .fvar j (Γ j)) (k + n - 1) E) p
  | 0, k, E, p, rep => by
    simp only [List.range_zero, List.map_nil, Expr.instSpine]
    exact rep.congr_ghost (fun _ hj => nomatch hj)
  | n + 1, k, E, p, rep => by
    have hrep1 : TmExact κ n Γ h (k + 1)
        (Expr.instSpine ((List.range n).map fun j => .fvar j (Γ j)) (k + 1 + n - 1) E) p :=
      tmExact_open_prefix n (by rw [show k + 1 + n = k + (n + 1) by omega]; exact rep)
    have hcongr : TmExact κ (n + 1) Γ h k
        ((Expr.instSpine ((List.range n).map fun j => .fvar j (Γ j)) (k + 1 + n - 1) E).instantiate1
          (.fvar n (Γ n)) k) p :=
      hrep1.open (Γ' := Γ) rfl (fun _ _ => rfl) k rfl
    rw [List.range_succ, List.map_append, List.map_singleton]
    have hspine : ∀ (xs : List KExpr) (m : Nat) (X v : KExpr),
        xs.length ≤ m →
        Expr.instSpine (xs ++ [v]) m X =
          (Expr.instSpine xs m X).instantiate1 v (m - xs.length) := by
      intro xs
      induction xs with
      | nil => intro m X v _; simp [Expr.instSpine]
      | cons a as ih =>
        intro m X v hle
        simp only [List.length_cons] at hle ⊢
        simp only [List.cons_append, Expr.instSpine]
        rw [ih (m - 1) (X.instantiate1 a m) v (by omega)]
        congr 1; omega
    rw [hspine _ (k + (n + 1) - 1) E (.fvar n (Γ n))
      (by simp only [List.length_map, List.length_range]; omega)]
    simp only [List.length_map, List.length_range]
    have h1 : k + 1 + n - 1 = k + (n + 1) - 1 := by omega
    have h2 : k + (n + 1) - 1 - n = k := by omega
    rw [h2, ← h1]
    exact hcongr

/-- Exact `d = rP` prefix opening: `TmExact κ 0 _ h rP P p` IS `TmExact κ rP Γ h 0 (instSpine ...) p`. -/
theorem TmExact.open_prefix_eq {κ : _root_.Address → KKey} {rP : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {P : KExpr} {p : SourceValue F}
    (rep : TmExact κ 0 (fun _ => .sort .zero) h rP P p) :
    TmExact κ rP Γ h 0
      (Expr.instSpine ((List.range rP).map fun j => .fvar j (Γ j)) (rP - 1) P) p := by
  simpa using tmExact_open_prefix (Γ := Γ) rP (k := 0) (by simpa using rep)

private theorem tmExact_store_bvarLocal {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {i : F}
    (hs : ZMod.val i < 9223372036854775808) (hi : ZMod.val i < k) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "BVar" [.field i]]) k (.bvar (ZMod.val i))
      (.ptr (.enum kexprEnum) h.length) :=
  .bvarLocal (by simp) hs hi

private theorem tmExact_store_bvarFree_eq {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {i : F} {j : Nat}
    (hs : ZMod.val i < 9223372036854775808) (hk : k ≤ ZMod.val i) (hd : ZMod.val i - k < d)
    (hj : fvIdx d k (ZMod.val i) = j) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "BVar" [.field i]]) k (.fvar j (Γ j))
      (.ptr (.enum kexprEnum) h.length) := by
  subst hj; exact .bvarFree (by simp) hs hk hd

private theorem tmExact_store_app {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {Ef Ea : KExpr} {fp ap : SourceValue F}
    (rf : TmExact κ d Γ h k Ef fp) (ra : TmExact κ d Γ h k Ea ap) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "App" [fp, ap]]) k (.app Ef Ea)
      (.ptr (.enum kexprEnum) h.length) :=
  let ext : Heap.Extends h (h ++ [.construct kexprEnum "App" [fp, ap]]) := Heap.Extends.snoc _ _
  .app (by simp) (rf.mono ext) (ra.mono ext)

private theorem tmExact_store_lam {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {T B : KExpr} {ℓ : KLevel} {tp bp lp : SourceValue F}
    (rt : TmExact κ d Γ h k T tp) (rb : TmExact κ d Γ h (k + 1) B bp) (rl : RepKLevel h ℓ lp) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "Lam" [tp, bp, lp]]) k (.lam T B (bmeta ℓ))
      (.ptr (.enum kexprEnum) h.length) :=
  let ext : Heap.Extends h (h ++ [.construct kexprEnum "Lam" [tp, bp, lp]]) := Heap.Extends.snoc _ _
  .lam (by simp) (rt.mono ext) (rb.mono ext) (rl.mono ext)

private theorem tmExact_store_forallE {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {T B : KExpr} {ℓ : KLevel} {tp bp lp : SourceValue F}
    (rt : TmExact κ d Γ h k T tp) (rb : TmExact κ d Γ h (k + 1) B bp) (rl : RepKLevel h ℓ lp) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "Forall" [tp, bp, lp]]) k (.forallE T B (bmeta ℓ))
      (.ptr (.enum kexprEnum) h.length) :=
  let ext : Heap.Extends h (h ++ [.construct kexprEnum "Forall" [tp, bp, lp]]) :=
    Heap.Extends.snoc _ _
  .forallE (by simp) (rt.mono ext) (rb.mono ext) (rl.mono ext)

private theorem tmExact_store_letE {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {T V B : KExpr} {tp vp bp : SourceValue F}
    (rt : TmExact κ d Γ h k T tp) (rv : TmExact κ d Γ h k V vp)
    (rb : TmExact κ d Γ h (k + 1) B bp) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "Let" [tp, vp, bp]]) k (instShift V 0 B)
      (.ptr (.enum kexprEnum) h.length) :=
  let ext : Heap.Extends h (h ++ [.construct kexprEnum "Let" [tp, vp, bp]]) := Heap.Extends.snoc _ _
  .letE (by simp) (rt.mono ext) (rv.mono ext) (rb.mono ext)

private theorem tmExact_store_proj {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {a : Bytes.Address} {i : F} {E : KExpr} {ap ep : SourceValue F}
    (ra : Bytes.RepAddressRef addrTy h a ap) (re : TmExact κ d Γ h k E ep) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "Proj" [ap, .field i, ep]]) k
      (.proj (κ (ixAddr a)) (ZMod.val i) E) (.ptr (.enum kexprEnum) h.length) :=
  let ext : Heap.Extends h (h ++ [.construct kexprEnum "Proj" [ap, .field i, ep]]) :=
    Heap.Extends.snoc _ _
  .proj (by simp) (Bytes.repAddressRef_heapMono₂ addrTy ext ra) (re.mono ext)

private theorem tmExact_copy_sort {κ : _root_.Address → KKey} {d d' : Nat} {Γ Γ' : Nat → KExpr}
    {h : Heap F} {k k' : Nat} {E : KExpr} {e lp : SourceValue F}
    (hE : TmExact κ d Γ h k E e) (ld : loadValue h e = .ok (.construct kexprEnum "Srt" [lp])) :
    TmExact κ d' Γ' (h ++ [.construct kexprEnum "Srt" [lp]]) k' E
      (.ptr (.enum kexprEnum) h.length) := by
  obtain ⟨l, rfl, rl⟩ := hE.sort_of_load ld
  exact .sort (by simp) (rl.mono (Heap.Extends.snoc _ _))

private theorem tmExact_copy_const {κ : _root_.Address → KKey} {d d' : Nat} {Γ Γ' : Nat → KExpr}
    {h : Heap F} {k k' : Nat} {E : KExpr} {e ap lsp : SourceValue F}
    (hE : TmExact κ d Γ h k E e)
    (ld : loadValue h e = .ok (.construct kexprEnum "Const" [ap, lsp])) :
    TmExact κ d' Γ' (h ++ [.construct kexprEnum "Const" [ap, lsp]]) k' E
      (.ptr (.enum kexprEnum) h.length) := by
  obtain ⟨a, ls, rfl, ra, rls⟩ := hE.const_of_load ld
  have ext : Heap.Extends h (h ++ [.construct kexprEnum "Const" [ap, lsp]]) := Heap.Extends.snoc _ _
  exact .const (by simp) (Bytes.repAddressRef_heapMono₂ addrTy ext ra) (rls.mono ext)

private theorem tmExact_copy_lit {κ : _root_.Address → KKey} {d d' : Nat} {Γ Γ' : Nat → KExpr}
    {h : Heap F} {k k' : Nat} {E : KExpr} {e lp : SourceValue F}
    (hE : TmExact κ d Γ h k E e) (ld : loadValue h e = .ok (.construct kexprEnum "Lit" [lp])) :
    TmExact κ d' Γ' (h ++ [.construct kexprEnum "Lit" [lp]]) k' E
      (.ptr (.enum kexprEnum) h.length) := by
  have ext : Heap.Extends h (h ++ [.construct kexprEnum "Lit" [lp]]) := Heap.Extends.snoc _ _
  rcases hE.toTm.lit_of_load ld with ⟨_, limbs, rfl, rl, hc, rfl⟩ |
    ⟨_, bs, s, rfl, rb, hs, rfl⟩
  · exact .litNat (by simp) (repList_heapMono₂ _ repU64_heapMono₂ ext rl) hc
  · exact .litStr (by simp) (Bytes.repByteStream_heapMono₂ _ ext rb) hs

/-- If every `BVar` index in `e` lies strictly below the local depth `k`, `TmExact` holds at any
target opening depth `(d', Γ')` and any `k' ≥ k`. -/
private theorem tmExact_of_idxLt {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} :
    ∀ {k₀ m : Nat} {E : KExpr} {e : SourceValue F},
      TmExact κ d Γ h k₀ E e →
      k₀ = k + m →
      IdxAll h (fun n i => ZMod.val i < k + n) m e →
      ∀ d' Γ' k', k ≤ k' → TmExact κ d' Γ' h (k' + m) E e := by
  intro k₀ m E e rep
  induction rep generalizing m with
  | @bvarLocal _ addr i cell hs hi =>
    intro _ hidx d' Γ' k' hk'
    obtain ⟨i', hx, hlt⟩ := SubstAux.idxAll_bvar_inv hidx (loadValue_enum_cell cell)
    injection hx with hx; subst hx
    exact .bvarLocal cell hs (by omega)
  | @bvarFree _ addr i cell hs hk hd =>
    intro hk₀ hidx
    exfalso
    obtain ⟨i', hx, hlt⟩ := SubstAux.idxAll_bvar_inv hidx (loadValue_enum_cell cell)
    injection hx with hx; subst hx
    omega
  | sort cell rl => intro _ _ _ _ _ _; exact .sort cell rl
  | const cell ra rls => intro _ _ _ _ _ _; exact .const cell ra rls
  | app cell _ _ ihf iha =>
    intro hk₀ hidx d' Γ' k' hk'
    obtain ⟨nf, na⟩ := SubstAux.idxAll_app_inv hidx (loadValue_enum_cell cell)
    exact .app cell (ihf hk₀ nf d' Γ' k' hk') (iha hk₀ na d' Γ' k' hk')
  | lam cell _ _ rl iht ihb =>
    intro hk₀ hidx d' Γ' k' hk'
    obtain ⟨nt, nb⟩ := SubstAux.idxAll_lam_inv hidx (loadValue_enum_cell cell)
    have hb' := ihb (m := m + 1) (by omega) nb d' Γ' k' hk'
    rw [show k' + (m + 1) = k' + m + 1 by omega] at hb'
    exact .lam cell (iht hk₀ nt d' Γ' k' hk') hb' rl
  | forallE cell _ _ rl iht ihb =>
    intro hk₀ hidx d' Γ' k' hk'
    obtain ⟨nt, nb⟩ := SubstAux.idxAll_forallE_inv hidx (loadValue_enum_cell cell)
    have hb' := ihb (m := m + 1) (by omega) nb d' Γ' k' hk'
    rw [show k' + (m + 1) = k' + m + 1 by omega] at hb'
    exact .forallE cell (iht hk₀ nt d' Γ' k' hk') hb' rl
  | letE cell _ _ _ iht ihv ihb =>
    intro hk₀ hidx d' Γ' k' hk'
    obtain ⟨nt, nv, nb⟩ := SubstAux.idxAll_letE_inv hidx (loadValue_enum_cell cell)
    have hb' := ihb (m := m + 1) (by omega) nb d' Γ' k' hk'
    rw [show k' + (m + 1) = k' + m + 1 by omega] at hb'
    exact .letE cell (iht hk₀ nt d' Γ' k' hk') (ihv hk₀ nv d' Γ' k' hk') hb'
  | litNat cell rl hc => intro _ _ _ _ _ _; exact .litNat cell rl hc
  | litStr cell rb hs => intro _ _ _ _ _ _; exact .litStr cell rb hs
  | proj cell ra _ ihe =>
    intro hk₀ hidx d' Γ' k' hk'
    exact .proj cell ra
      (ihe hk₀ (SubstAux.idxAll_proj_inv hidx (loadValue_enum_cell cell)) d' Γ' k' hk')

/-- Exact `collect_spine`: splits an application into head and spine while preserving `TmExact`. -/
theorem collect_spine_exact {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ {e r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr},
      ObsFn W "KernelTypes::collect_spine" [e] h r h' cs →
      TmExact κ d Γ h k E e →
      ∃ hd sp H As, r = .tuple [hd, sp] ∧ TmExact κ d Γ h' k H hd ∧
        RepList kexprListEnum (fun h E p => TmExact κ d Γ h k E p) h' As sp ∧
        E = Expr.mkAppN H As := by
  have hmain : ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelTypes::collect_spine" →
      ∀ (e : SourceValue F) (k : Nat) (E : KExpr), args = [e] → TmExact κ d Γ h k E e →
        ∃ hd sp H As, r = .tuple [hd, sp] ∧ TmExact κ d Γ h' k H hd ∧
          RepList kexprListEnum (fun h E p => TmExact κ d Γ h k E p) h' As sp ∧
          E = Expr.mkAppN H As :=
    ObsFn.strong_induction (world := W)
      (fun fname args h r h' cs => fname = "KernelTypes::collect_spine" →
        ∀ (e : SourceValue F) (k : Nat) (E : KExpr), args = [e] → TmExact κ d Γ h k E e →
          ∃ hd sp H As, r = .tuple [hd, sp] ∧ TmExact κ d Γ h' k H hd ∧
            RepList kexprListEnum (fun h E p => TmExact κ d Γ h k E p) h' As sp ∧
            E = Expr.mkAppN H As)
      (fun fname args h r h' cs ev ih hfn e k E hargs hE => by
        subst hfn hargs
        match Obs.«KernelTypes::collect_spine».obs ev with
        | .App (ld12 := ld) (ev43 := e1) (he69 := hr) (ev88 := e2) (he105 := he) (hc106 := hc) .. =>
          subst hc hr he
          obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
          obtain ⟨hd, sp, H, As, htup, hH, hAs, rfl⟩ :=
            ih _ _ _ _ _ _ tele_lt_calls e1 rfl _ k Ef rfl hf
          injection htup with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
          exact ⟨_, _, H, As ++ [Ea], rfl, hH.mono e2.heap_extends,
            SubstAux.ksnoc (R := fun h E p => TmExact κ d Γ h k E p)
              (fun _ _ _ _ ext r => r.mono ext) e2 hAs (ha.mono e1.heap_extends),
            (SubstAux.mkAppN_snoc As H Ea).symm⟩
        | .other (he115 := hr) (hm132 := hm) (he136 := he) .. =>
          subst hr hm he
          exact ⟨e, _, E, [], rfl, hE.mono (Heap.Extends.snoc _ _), .nil (by simp), rfl⟩)
  intro e r h h' cs k E ev hE
  exact hmain _ _ _ _ _ _ ev rfl e k E rfl hE

/-- Exact opening-depth lift (`s₁ = 0`, `s₂ = ZMod.val s`, `k = ZMod.val c`): `KernelSubst::expr_lift`
lifts `TmExact κ d Γ h (ZMod.val c) E e` to `TmExact κ (d + ZMod.val s) Γ h' (ZMod.val c) E r`. -/
private theorem expr_lift_open_exact_aux (κ : _root_.Address → KKey) :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → IxVM.Consistency.Bounded cs →
      ((fname = "KernelSubst::expr_lift" →
        ∀ (e : SourceValue F) (s c : F) (d : Nat) (Γ : Nat → KExpr) (E : KExpr),
          args = [e, .field s, .field c] → ZMod.val s < 4611686018427387904 →
          TmExact κ d Γ h (ZMod.val c) E e →
          TmExact κ (d + ZMod.val s) Γ h' (ZMod.val c) E r) ∧
       (fname = "KernelSubst::expr_lift_walk" →
        ∀ (e : SourceValue F) (s c : F) (d : Nat) (Γ : Nat → KExpr) (E : KExpr),
          args = [e, .field s, .field c] → ZMod.val s < 4611686018427387904 →
          ZMod.val c < 4294967296 →
          TmExact κ d Γ h (ZMod.val c) E e →
          TmExact κ (d + ZMod.val s) Γ h' (ZMod.val c) E r) ∧
       (fname = "KernelSubst::expr_lift_let" →
        ∀ (ty val body : SourceValue F) (s c : F) (d : Nat) (Γ : Nat → KExpr) (T V B : KExpr),
          args = [ty, val, body, .field s, .field c] → ZMod.val s < 4611686018427387904 →
          ZMod.val c < 4294967296 →
          TmExact κ d Γ h (ZMod.val c) T ty →
          TmExact κ d Γ h (ZMod.val c) V val →
          TmExact κ d Γ h (ZMod.val c + 1) B body →
          TmExact κ (d + ZMod.val s) Γ h' (ZMod.val c) (instShift V 0 B) r) ∧
       (fname = "KernelSubst::expr_lift_bvar" →
        ∀ (i s c : F) (d : Nat) (Γ : Nat → KExpr) (E : KExpr),
          args = [.field i, .field s, .field c] → ZMod.val s < 4611686018427387904 →
          BVarIm d Γ (ZMod.val c) (ZMod.val i) E →
          TmExact κ (d + ZMod.val s) Γ h' (ZMod.val c) E r)) :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => IxVM.Consistency.Bounded cs →
      ((fname = "KernelSubst::expr_lift" →
        ∀ (e : SourceValue F) (s c : F) (d : Nat) (Γ : Nat → KExpr) (E : KExpr),
          args = [e, .field s, .field c] → ZMod.val s < 4611686018427387904 →
          TmExact κ d Γ h (ZMod.val c) E e →
          TmExact κ (d + ZMod.val s) Γ h' (ZMod.val c) E r) ∧
       (fname = "KernelSubst::expr_lift_walk" →
        ∀ (e : SourceValue F) (s c : F) (d : Nat) (Γ : Nat → KExpr) (E : KExpr),
          args = [e, .field s, .field c] → ZMod.val s < 4611686018427387904 →
          ZMod.val c < 4294967296 →
          TmExact κ d Γ h (ZMod.val c) E e →
          TmExact κ (d + ZMod.val s) Γ h' (ZMod.val c) E r) ∧
       (fname = "KernelSubst::expr_lift_let" →
        ∀ (ty val body : SourceValue F) (s c : F) (d : Nat) (Γ : Nat → KExpr) (T V B : KExpr),
          args = [ty, val, body, .field s, .field c] → ZMod.val s < 4611686018427387904 →
          ZMod.val c < 4294967296 →
          TmExact κ d Γ h (ZMod.val c) T ty →
          TmExact κ d Γ h (ZMod.val c) V val →
          TmExact κ d Γ h (ZMod.val c + 1) B body →
          TmExact κ (d + ZMod.val s) Γ h' (ZMod.val c) (instShift V 0 B) r) ∧
       (fname = "KernelSubst::expr_lift_bvar" →
        ∀ (i s c : F) (d : Nat) (Γ : Nat → KExpr) (E : KExpr),
          args = [.field i, .field s, .field c] → ZMod.val s < 4611686018427387904 →
          BVarIm d Γ (ZMod.val c) (ZMod.val i) E →
          TmExact κ (d + ZMod.val s) Γ h' (ZMod.val c) E r)))
    (fun fname args h r h' cs ev ih bd => by
      refine ⟨fun hfn e s c d Γ E hargs hs hE => ?_,
        fun hfn e s c d Γ E hargs hs hc0 hE => ?_,
        fun hfn ty val body s c d Γ T V B hargs hs hc0 ht hv hb => ?_,
        fun hfn i s c d Γ E hargs hs hcase => ?_⟩
      · subst hfn hargs
        match Obs.«KernelSubst::expr_lift».obs ev with
        | .n0 (hv14 := hv) (he16 := hr) (he17 := he) .. =>
          subst hr he; injection hv with hv; subst hv
          rw [ZMod.val_zero, Nat.add_zero]; exact hE
        | .other_n0 (ev36 := e1) (ev59 := e2) (he81 := hr) (he82 := he) (hc83 := hc) .. =>
          subst hc hr he
          obtain ⟨rfl, sl⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ e1 _ rfl
            (bounded_sub tele_sub_calls bd)
          obtain ⟨c', y, hc', hy, -, -, hltf, rfl⟩ := SubstAux.ltf e2
          injection hc' with hc'; subst hc'
          have hge := SubstAux.ltf_zero hltf.symm
          obtain ⟨b, hb, b1, -, b3, -, -⟩ := sl d Γ (ZMod.val c) E hE.toTm
          rw [hb] at hy; injection hy with hy; subst hy
          rw [SubstAux.val_natCast (SubstAux.lt_mod_of_le_idx b1)] at hge
          have hidx := SubstAux.idxAll_mono b3
            (Q := fun n i => ZMod.val i < ZMod.val c + n) fun n i hi => by omega
          simpa using tmExact_of_idxLt (k := ZMod.val c) (m := 0) hE (Nat.add_zero _).symm
            hidx (d + ZMod.val s) Γ (ZMod.val c) (Nat.le_refl _)
        | .other_n1 (ev36 := e1) (ev59 := e2) (ev94 := e3) (hc119 := hc) .. =>
          subst hc
          obtain ⟨rfl, -⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ e1 _ rfl
            (bounded_sub tele_sub_calls bd)
          obtain ⟨c', _, hc', _, hc32, -, -, rfl⟩ := SubstAux.ltf e2
          injection hc' with hc'; subst hc'
          exact (ih _ _ _ _ _ _ tele_lt_calls e3 (bounded_sub tele_sub_calls bd)).2.1
            rfl e s c d Γ E rfl hs hc32 hE
      · subst hfn hargs
        match Obs.«KernelSubst::expr_lift_walk».obs ev with
        | .BVar (ld12 := ld) (ev30 := e1) (hc55 := hc) .. =>
          subst hc
          obtain ⟨i, rfl, hsm, hbc⟩ := hE.bvar_of_load ld
          exact (ih _ _ _ _ _ _ tele_lt_calls e1 (bounded_sub tele_sub_calls bd)).2.2.2
            rfl i s c d Γ E rfl hs ⟨hsm, hbc⟩
        | .Srt (ld12 := ld) (he72 := hr) (hm71 := hm) .. =>
          subst hr hm; exact tmExact_copy_sort hE ld
        | .Const (ld12 := ld) (he106 := hr) (hm105 := hm) .. =>
          subst hr hm; exact tmExact_copy_const hE ld
        | .Lit (ld12 := ld) (he554 := hr) (hm553 := hm) .. =>
          subst hr hm; exact tmExact_copy_lit hE ld
        | .App (ld12 := ld) (he148 := hr) (hm147 := hm) (ev165 := e1) (ev201 := e2)
            (hc226 := hc) .. =>
          subst hc hr hm
          obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
          have sf := (ih _ _ _ _ _ _ tele_lt_calls e1 (bounded_sub tele_sub_calls bd)).1
            rfl _ s c d Γ Ef rfl hs hf
          have sa := (ih _ _ _ _ _ _ tele_lt_calls e2 (bounded_sub tele_sub_calls bd)).1
            rfl _ s c d Γ Ea rfl hs (ha.mono e1.heap_extends)
          exact tmExact_store_app (sf.mono e2.heap_extends) sa
        | .Lam (ld12 := ld) (he253 := hr) (hm252 := hm) (ev271 := e1) (op338 := op) (ev307 := e2)
            (hc347 := hc) .. =>
          subst hc hr hm; rw [SubstAux.add_ok op] at e2
          obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.lam_of_load ld
          have st := (ih _ _ _ _ _ _ tele_lt_calls e1 (bounded_sub tele_sub_calls bd)).1
            rfl _ s c d Γ T rfl hs ht
          have sb := (ih _ _ _ _ _ _ tele_lt_calls e2 (bounded_sub tele_sub_calls bd)).1
            rfl _ s (c + 1) d Γ B rfl hs (by rw [SubstAux.val_succ32 hc0]; exact hb.mono e1.heap_extends)
          rw [SubstAux.val_succ32 hc0] at sb
          exact tmExact_store_lam (st.mono e2.heap_extends) sb
            (hl.mono (e1.heap_extends.trans e2.heap_extends))
        | .Forall (ld12 := ld) (he374 := hr) (hm373 := hm) (ev392 := e1) (op459 := op) (ev428 := e2)
            (hc468 := hc) .. =>
          subst hc hr hm; rw [SubstAux.add_ok op] at e2
          obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.forallE_of_load ld
          have st := (ih _ _ _ _ _ _ tele_lt_calls e1 (bounded_sub tele_sub_calls bd)).1
            rfl _ s c d Γ T rfl hs ht
          have sb := (ih _ _ _ _ _ _ tele_lt_calls e2 (bounded_sub tele_sub_calls bd)).1
            rfl _ s (c + 1) d Γ B rfl hs (by rw [SubstAux.val_succ32 hc0]; exact hb.mono e1.heap_extends)
          rw [SubstAux.val_succ32 hc0] at sb
          exact tmExact_store_forallE (st.mono e2.heap_extends) sb
            (hl.mono (e1.heap_extends.trans e2.heap_extends))
        | .Let (ld12 := ld) (ev496 := e1) (hc537 := hc) .. =>
          subst hc
          obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := hE.letE_of_load ld
          exact (ih _ _ _ _ _ _ tele_lt_calls e1 (bounded_sub tele_sub_calls bd)).2.2.1
            rfl _ _ _ s c d Γ T V B rfl hs hc0 ht hv hb
        | .Proj (ld12 := ld) (he593 := hr) (hm592 := hm) (ev625 := e1) (hc650 := hc) .. =>
          subst hc hr hm
          obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := hE.proj_of_load ld
          exact tmExact_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e1.heap_extends ra)
            ((ih _ _ _ _ _ _ tele_lt_calls e1 (bounded_sub tele_sub_calls bd)).1
              rfl _ s c d Γ Es rfl hs hes)
      · subst hfn hargs
        match Obs.«KernelSubst::expr_lift_let».obs ev with
        | .run (he5 := hr) (hm4 := hm) (ev23 := e1) (ev59 := e2) (op126 := op) (ev95 := e3)
            (hc128 := hc) .. =>
          subst hc hr hm; rw [SubstAux.add_ok op] at e3
          have x1 := (ih _ _ _ _ _ _ tele_lt_calls e1 (bounded_sub tele_sub_calls bd)).1
            rfl _ s c d Γ T rfl hs ht
          have x2 := (ih _ _ _ _ _ _ tele_lt_calls e2 (bounded_sub tele_sub_calls bd)).1
            rfl _ s c d Γ V rfl hs (hv.mono e1.heap_extends)
          have x3 := (ih _ _ _ _ _ _ tele_lt_calls e3 (bounded_sub tele_sub_calls bd)).1
            rfl _ s (c + 1) d Γ B rfl hs
            (by rw [SubstAux.val_succ32 hc0]; exact hb.mono (e1.heap_extends.trans e2.heap_extends))
          rw [SubstAux.val_succ32 hc0] at x3
          exact tmExact_store_letE ((x1.mono e2.heap_extends).mono e3.heap_extends)
            (x2.mono e3.heap_extends) x3
      · subst hfn hargs
        obtain ⟨hsm, hbc⟩ := hcase
        cases Obs.«KernelSubst::expr_lift_bvar».obs ev with
        | n1 m2 cs13 ev15 he40 hm39 hc52 =>
          obtain ⟨i', c', hi', hc', -, -, hltf, rfl⟩ := SubstAux.ltf ev15
          injection hi' with hi'; injection hc' with hc'; subst hi' hc' he40 hm39
          have hlt := SubstAux.ltf_one hltf.symm
          rcases hbc with ⟨_, rfl⟩ | ⟨hk, _, _⟩
          · exact tmExact_store_bvarLocal hsm (by omega)
          · omega
        | n0 m2 cs13 v66 ev15 he62 hm61 op80 hc83 =>
          obtain ⟨i', c', hi', hc', hi32, -, hltf, rfl⟩ := SubstAux.ltf ev15
          injection hi' with hi'; injection hc' with hc'; subst hi' hc' he62 hm61
          have hge := SubstAux.ltf_zero hltf.symm
          rw [SubstAux.add_ok op80]
          have hv : ZMod.val (i + s) = ZMod.val i + ZMod.val s :=
            SubstAux.val_add (by
              have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl; omega)
          rcases hbc with ⟨hlt, _⟩ | ⟨hk, hd, rfl⟩
          · omega
          · exact tmExact_store_bvarFree_eq (by omega) (by omega) (by omega)
              (by rw [hv]; unfold fvIdx; omega))

theorem expr_lift_open_exact {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {e r : SourceValue F} {s : F} {h h' : Heap F} {cs : List (Call F)} {E : KExpr}
    (bd : IxVM.Consistency.Bounded cs) (hs : ZMod.val s < 4611686018427387904)
    (ev : ObsFn W "KernelSubst::expr_lift" [e, .field s, .field 0] h r h' cs)
    (hE : TmExact κ d Γ h 0 E e) :
    TmExact κ (d + ZMod.val s) Γ h' 0 E r := by
  have hz : ZMod.val (0 : F) = 0 := ZMod.val_zero
  exact hz ▸ (expr_lift_open_exact_aux κ _ _ _ _ _ _ ev bd).1 rfl e s 0 d Γ E rfl hs (hz ▸ hE)

/-- `NoIdx h c (c + ni) e` on a closed-depth `TmExact κ 0 Γ h k E e` certifies `noLooseIn c ni E`. -/
theorem noLooseIn_of_noIdx_tmExact {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F} :
    ∀ {k c m ni : Nat} {E : KExpr} {e : SourceValue F},
      TmExact κ 0 Γ h k E e →
      IdxAll h (fun n i => ZMod.val i < c + n ∨ c + ni + n ≤ ZMod.val i) m e →
      noLooseIn (c + m) ni E = true := by
  intro k c m ni E e rep
  induction rep generalizing m with
  | @bvarLocal _ addr i cell hs hi =>
    intro hn
    obtain ⟨i', hx, hw⟩ := SubstAux.idxAll_bvar_inv hn (loadValue_enum_cell cell)
    injection hx with hx; subst hx
    simp only [noLooseIn, decide_eq_true_eq]
    omega
  | bvarFree _ _ _ hd => exact nomatch hd
  | sort _ _ | const _ _ _ | litNat _ _ _ | litStr _ _ _ => intro _; rfl
  | app cell _ _ ihf iha =>
    intro hn
    obtain ⟨nf, na⟩ := SubstAux.idxAll_app_inv hn (loadValue_enum_cell cell)
    simp only [noLooseIn, Bool.and_eq_true]
    exact ⟨ihf nf, iha na⟩
  | lam cell _ _ _ iht ihb =>
    intro hn
    obtain ⟨nt, nb⟩ := SubstAux.idxAll_lam_inv hn (loadValue_enum_cell cell)
    have hb := ihb (m := m + 1) nb
    rw [show c + (m + 1) = c + m + 1 by omega] at hb
    simp only [noLooseIn, Bool.and_eq_true]
    exact ⟨iht nt, hb⟩
  | forallE cell _ _ _ iht ihb =>
    intro hn
    obtain ⟨nt, nb⟩ := SubstAux.idxAll_forallE_inv hn (loadValue_enum_cell cell)
    have hb := ihb (m := m + 1) nb
    rw [show c + (m + 1) = c + m + 1 by omega] at hb
    simp only [noLooseIn, Bool.and_eq_true]
    exact ⟨iht nt, hb⟩
  | letE cell _ _ _ _ ihv ihb =>
    intro hn
    obtain ⟨_, nv, nb⟩ := SubstAux.idxAll_letE_inv hn (loadValue_enum_cell cell)
    have hb := ihb (m := m + 1) nb
    rw [show c + (m + 1) = c + m + 1 by omega] at hb
    exact noLooseIn_instShift_zero (ihv nv) hb
  | proj cell _ _ ihe =>
    intro hn
    exact ihe (SubstAux.idxAll_proj_inv hn (loadValue_enum_cell cell))

private theorem tmExact_lower_of_idxLt {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {c k₀ ni : Nat} (hck : c ≤ k₀) :
    ∀ {k' m : Nat} {E : KExpr} {e : SourceValue F},
      TmExact κ 0 Γ h k' E e →
      IdxAll h (fun n i => ZMod.val i < c + n) m e →
      E.lowerBVars ni (c + m) = E ∧ TmExact κ 0 Γ h (k₀ + m) E e := by
  intro k' m E e rep
  induction rep generalizing m with
  | @bvarLocal _ addr i cell hs _ =>
    intro hidx
    obtain ⟨i', hx, hlt⟩ := SubstAux.idxAll_bvar_inv hidx (loadValue_enum_cell cell)
    injection hx with hx; subst hx
    refine ⟨?_, .bvarLocal cell hs (by omega)⟩
    show (if ZMod.val i ≥ c + m + ni then _ else _) = _
    exact ite_eq_right (by omega)
  | @bvarFree _ _ _ _ _ _ hd => exact nomatch hd
  | sort cell rl => intro _; exact ⟨rfl, .sort cell rl⟩
  | const cell ra rls => intro _; exact ⟨rfl, .const cell ra rls⟩
  | app cell _ _ ihf iha =>
    intro hidx
    obtain ⟨nf, na⟩ := SubstAux.idxAll_app_inv hidx (loadValue_enum_cell cell)
    obtain ⟨ef, rf⟩ := ihf nf
    obtain ⟨ea, ra⟩ := iha na
    exact ⟨by simp only [Expr.lowerBVars, ef, ea], .app cell rf ra⟩
  | lam cell _ _ rl iht ihb =>
    intro hidx
    obtain ⟨nt, nb⟩ := SubstAux.idxAll_lam_inv hidx (loadValue_enum_cell cell)
    obtain ⟨et, rt⟩ := iht nt
    obtain ⟨eb, rb⟩ := ihb (m := m + 1) nb
    rw [show c + (m + 1) = c + m + 1 by omega] at eb
    rw [show k₀ + (m + 1) = k₀ + m + 1 by omega] at rb
    exact ⟨by simp only [Expr.lowerBVars, et, eb], .lam cell rt rb rl⟩
  | forallE cell _ _ rl iht ihb =>
    intro hidx
    obtain ⟨nt, nb⟩ := SubstAux.idxAll_forallE_inv hidx (loadValue_enum_cell cell)
    obtain ⟨et, rt⟩ := iht nt
    obtain ⟨eb, rb⟩ := ihb (m := m + 1) nb
    rw [show c + (m + 1) = c + m + 1 by omega] at eb
    rw [show k₀ + (m + 1) = k₀ + m + 1 by omega] at rb
    exact ⟨by simp only [Expr.lowerBVars, et, eb], .forallE cell rt rb rl⟩
  | @letE _ _ _ _ _ T V B cell _ rv rb iht ihv ihb =>
    intro hidx
    obtain ⟨nt, nv, nb⟩ := SubstAux.idxAll_letE_inv hidx (loadValue_enum_cell cell)
    have hnoV : noLooseIn (c + m) ni V = true :=
      noLooseIn_of_noIdx_tmExact (c := c) (m := m) (ni := ni) rv
        (SubstAux.idxAll_mono nv fun n i h1 => Or.inl h1)
    have hnoB : noLooseIn (c + m + 1) ni B = true := by
      have hb0 := noLooseIn_of_noIdx_tmExact (c := c) (m := m + 1) (ni := ni) rb
        (SubstAux.idxAll_mono nb fun n i h1 => Or.inl h1)
      rwa [show c + (m + 1) = c + m + 1 by omega] at hb0
    obtain ⟨_, rt⟩ := iht nt
    obtain ⟨ev, rv'⟩ := ihv nv
    obtain ⟨eb, rb'⟩ := ihb (m := m + 1) nb
    rw [show c + (m + 1) = c + m + 1 by omega] at eb
    rw [show k₀ + (m + 1) = k₀ + m + 1 by omega] at rb'
    refine ⟨?_, .letE cell rt rv' rb'⟩
    rw [lowerBVars_instShift_zero hnoV hnoB, ev, eb]
  | litNat cell rl hc => intro _; exact ⟨rfl, .litNat cell rl hc⟩
  | litStr cell rb hs => intro _; exact ⟨rfl, .litStr cell rb hs⟩
  | proj cell ra _ ihe =>
    intro hidx
    obtain ⟨ee, re⟩ := ihe (SubstAux.idxAll_proj_inv hidx (loadValue_enum_cell cell))
    exact ⟨by simp only [Expr.lowerBVars, ee], .proj cell ra re⟩

/-- Exact local-depth lowering (`d = 0`, `k = rp + ZMod.val c + ZMod.val s` → `rp + ZMod.val c`):
`KernelSubst::expr_lower` on `TmExact κ 0 Γ h (rp + ZMod.val c + ZMod.val s) E e` with
`NoIdx h (ZMod.val c) (ZMod.val c + ZMod.val s) e` produces `E.lowerBVars (ZMod.val s) (ZMod.val c)`. -/
private theorem expr_lower_local_exact_aux (κ : _root_.Address → KKey) (rp : Nat)
    (Γ : Nat → KExpr) :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → IxVM.Consistency.Bounded cs →
      ((fname = "KernelSubst::expr_lower" →
        ∀ (e : SourceValue F) (s c : F) (E : KExpr),
          args = [e, .field s, .field c] →
          TmExact κ 0 Γ h (rp + ZMod.val c + ZMod.val s) E e →
          NoIdx h (ZMod.val c) (ZMod.val c + ZMod.val s) e →
          TmExact κ 0 Γ h' (rp + ZMod.val c) (E.lowerBVars (ZMod.val s) (ZMod.val c)) r) ∧
       (fname = "KernelSubst::expr_lower_walk" →
        ∀ (e : SourceValue F) (s c : F) (E : KExpr),
          args = [e, .field s, .field c] → ZMod.val c < 4294967296 →
          ¬ IdxLt h (ZMod.val c) e →
          TmExact κ 0 Γ h (rp + ZMod.val c + ZMod.val s) E e →
          NoIdx h (ZMod.val c) (ZMod.val c + ZMod.val s) e →
          TmExact κ 0 Γ h' (rp + ZMod.val c) (E.lowerBVars (ZMod.val s) (ZMod.val c)) r) ∧
       (fname = "KernelSubst::expr_lower_let" →
        ∀ (ty val body : SourceValue F) (s c : F) (T V B : KExpr),
          args = [ty, val, body, .field s, .field c] → ZMod.val c < 4294967296 →
          TmExact κ 0 Γ h (rp + ZMod.val c + ZMod.val s) T ty →
          TmExact κ 0 Γ h (rp + ZMod.val c + ZMod.val s) V val →
          TmExact κ 0 Γ h (rp + (ZMod.val c + 1) + ZMod.val s) B body →
          NoIdx h (ZMod.val c) (ZMod.val c + ZMod.val s) ty →
          NoIdx h (ZMod.val c) (ZMod.val c + ZMod.val s) val →
          NoIdx h (ZMod.val c + 1) (ZMod.val c + 1 + ZMod.val s) body →
          TmExact κ 0 Γ h' (rp + ZMod.val c)
            ((instShift V 0 B).lowerBVars (ZMod.val s) (ZMod.val c)) r)) :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => IxVM.Consistency.Bounded cs →
      ((fname = "KernelSubst::expr_lower" →
        ∀ (e : SourceValue F) (s c : F) (E : KExpr),
          args = [e, .field s, .field c] →
          TmExact κ 0 Γ h (rp + ZMod.val c + ZMod.val s) E e →
          NoIdx h (ZMod.val c) (ZMod.val c + ZMod.val s) e →
          TmExact κ 0 Γ h' (rp + ZMod.val c) (E.lowerBVars (ZMod.val s) (ZMod.val c)) r) ∧
       (fname = "KernelSubst::expr_lower_walk" →
        ∀ (e : SourceValue F) (s c : F) (E : KExpr),
          args = [e, .field s, .field c] → ZMod.val c < 4294967296 →
          ¬ IdxLt h (ZMod.val c) e →
          TmExact κ 0 Γ h (rp + ZMod.val c + ZMod.val s) E e →
          NoIdx h (ZMod.val c) (ZMod.val c + ZMod.val s) e →
          TmExact κ 0 Γ h' (rp + ZMod.val c) (E.lowerBVars (ZMod.val s) (ZMod.val c)) r) ∧
       (fname = "KernelSubst::expr_lower_let" →
        ∀ (ty val body : SourceValue F) (s c : F) (T V B : KExpr),
          args = [ty, val, body, .field s, .field c] → ZMod.val c < 4294967296 →
          TmExact κ 0 Γ h (rp + ZMod.val c + ZMod.val s) T ty →
          TmExact κ 0 Γ h (rp + ZMod.val c + ZMod.val s) V val →
          TmExact κ 0 Γ h (rp + (ZMod.val c + 1) + ZMod.val s) B body →
          NoIdx h (ZMod.val c) (ZMod.val c + ZMod.val s) ty →
          NoIdx h (ZMod.val c) (ZMod.val c + ZMod.val s) val →
          NoIdx h (ZMod.val c + 1) (ZMod.val c + 1 + ZMod.val s) body →
          TmExact κ 0 Γ h' (rp + ZMod.val c)
            ((instShift V 0 B).lowerBVars (ZMod.val s) (ZMod.val c)) r)))
    (fun fname args h r h' cs ev ih bd => by
      refine ⟨fun hfn e s c E hargs hE hn => ?_,
        fun hfn e s c E hargs hc0 hnlt hE hn => ?_,
        fun hfn ty val body s c T V B hargs hc0 ht hv hb nt nv nb => ?_⟩
      · subst hfn hargs
        match Obs.«KernelSubst::expr_lower».obs ev with
        | .n0 (hv14 := hv) (he16 := hr) (he17 := he) .. =>
          subst hr he; injection hv with hv; subst hv
          simp only [ZMod.val_zero, Nat.add_zero] at hE ⊢
          have hlow0 : ∀ (X : KExpr) (m : Nat), X.lowerBVars 0 m = X := by
            intro X
            induction X with
            | bvar i => intro m; simp only [Expr.lowerBVars, Nat.sub_zero]; split <;> rfl
            | _ => intro m; simp_all [Expr.lowerBVars]
          rw [hlow0]
          exact hE
        | .other_n0 (ev36 := e1) (ev59 := e2) (he81 := hr) (he82 := he) (hc83 := hc) .. =>
          subst hc hr he
          obtain ⟨rfl, sl⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ e1 _ rfl
            (bounded_sub tele_sub_calls bd)
          obtain ⟨c', y, hc', hy, -, -, hltf, rfl⟩ := SubstAux.ltf e2
          injection hc' with hc'; subst hc'
          have hge := SubstAux.ltf_zero hltf.symm
          obtain ⟨b, hb, b1, -, b3, -, -⟩ := sl 0 Γ (rp + ZMod.val c + ZMod.val s) E hE.toTm
          rw [hb] at hy; injection hy with hy; subst hy
          rw [SubstAux.val_natCast (SubstAux.lt_mod_of_le_idx b1)] at hge
          have hidx_c := SubstAux.idxAll_mono b3
            (Q := fun n i => ZMod.val i < ZMod.val c + n) fun n i hi => by omega
          obtain ⟨heq_low, hrep_c⟩ :=
            tmExact_lower_of_idxLt (c := ZMod.val c) (k₀ := rp + ZMod.val c) (ni := ZMod.val s)
              (by omega) (m := 0) hE hidx_c
          rw [Nat.add_zero] at heq_low hrep_c
          rw [heq_low]
          exact hrep_c
        | .other_n1 (ev36 := e1) (ev59 := e2) (ev94 := e3) (hc119 := hc) .. =>
          subst hc
          obtain ⟨rfl, sl⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ e1 _ rfl
            (bounded_sub tele_sub_calls bd)
          obtain ⟨c', y, hc', hy, hc32, -, hltf, rfl⟩ := SubstAux.ltf e2
          injection hc' with hc'; subst hc'
          have hlt := SubstAux.ltf_one hltf.symm
          obtain ⟨b, hb, b1, -, -, bmin, -⟩ := sl 0 Γ (rp + ZMod.val c + ZMod.val s) E hE.toTm
          rw [hb] at hy; injection hy with hy; subst hy
          rw [SubstAux.val_natCast (SubstAux.lt_mod_of_le_idx b1)] at hlt
          exact (ih _ _ _ _ _ _ tele_lt_calls e3 (bounded_sub tele_sub_calls bd)).2.1
            rfl e s c E rfl hc32 (bmin _ hlt) hE hn
      · subst hfn hargs
        match Obs.«KernelSubst::expr_lower_walk».obs ev with
        | .BVar (ld12 := ld) (he29 := hr) (hm28 := hm) (op47 := op) (hc50 := hc) .. =>
          subst hc hr hm
          obtain ⟨i, rfl, hsm, hbc⟩ := hE.bvar_of_load ld
          have hge_c : ZMod.val c ≤ ZMod.val i := by
            apply Nat.le_of_not_lt; intro hlt
            exact hnlt (SubstAux.idxAll_bvar_of_load ld (by show ZMod.val i < ZMod.val c + 0; omega))
          obtain ⟨i', hx, hw⟩ := SubstAux.idxAll_bvar_inv hn ld
          injection hx with hx; subst hx
          have hw' : ZMod.val c + ZMod.val s ≤ ZMod.val i := by
            have : ZMod.val i < ZMod.val c + 0 ∨ ZMod.val c + ZMod.val s + 0 ≤ ZMod.val i := hw
            omega
          rcases hbc with ⟨hlt_k, rfl⟩ | ⟨_, hd, _⟩
          · rw [SubstAux.sub_ok op]
            have hv : ZMod.val (i - s) = ZMod.val i - ZMod.val s := SubstAux.val_sub (by omega)
            have hl : (Expr.bvar (ZMod.val i) : KExpr).lowerBVars (ZMod.val s) (ZMod.val c) =
                .bvar (ZMod.val (i - s)) := by
              show (if ZMod.val i ≥ ZMod.val c + ZMod.val s then _ else _) = _
              rw [ite_eq_left hw', hv]
            rw [hl]
            exact tmExact_store_bvarLocal (by omega) (by omega)
          · exact nomatch hd
        | .Srt (ld12 := ld) (he67 := hr) (hm66 := hm) .. =>
          subst hr hm
          obtain ⟨l, rfl, rl⟩ := hE.sort_of_load ld
          exact .sort (by simp) (rl.mono (Heap.Extends.snoc _ _))
        | .Const (ld12 := ld) (he101 := hr) (hm100 := hm) .. =>
          subst hr hm
          obtain ⟨a, ls, rfl, ra, rls⟩ := hE.const_of_load ld
          exact .const (by simp) (Bytes.repAddressRef_heapMono₂ addrTy (Heap.Extends.snoc _ _) ra)
            (rls.mono (Heap.Extends.snoc _ _))
        | .Lit (ld12 := ld) (he549 := hr) (hm548 := hm) .. =>
          subst hr hm
          rcases hE.toTm.lit_of_load ld with ⟨_, _, rfl, rl, hc, rfl⟩ |
            ⟨_, _, _, rfl, rb, hs, rfl⟩
          · exact .litNat (by simp) (repList_heapMono₂ _ repU64_heapMono₂
              (Heap.Extends.snoc _ _) rl) hc
          · exact .litStr (by simp)
              (Bytes.repByteStream_heapMono₂ _ (Heap.Extends.snoc _ _) rb) hs
        | .App (ld12 := ld) (he143 := hr) (hm142 := hm) (ev160 := e1) (ev196 := e2)
            (hc221 := hc) .. =>
          subst hc hr hm
          obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
          obtain ⟨nf, na⟩ := SubstAux.idxAll_app_inv hn ld
          have sf := (ih _ _ _ _ _ _ tele_lt_calls e1 (bounded_sub tele_sub_calls bd)).1
            rfl _ s c Ef rfl hf nf
          have sa := (ih _ _ _ _ _ _ tele_lt_calls e2 (bounded_sub tele_sub_calls bd)).1
            rfl _ s c Ea rfl (ha.mono e1.heap_extends) (SubstAux.idxAll_heap e1.heap_extends na)
          exact tmExact_store_app (sf.mono e2.heap_extends) sa
        | .Lam (ld12 := ld) (he248 := hr) (hm247 := hm) (ev266 := e1) (op333 := op) (ev302 := e2)
            (hc342 := hc) .. =>
          subst hc hr hm; rw [SubstAux.add_ok op] at e2
          obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.lam_of_load ld
          obtain ⟨nt, nb⟩ := SubstAux.idxAll_lam_inv hn ld
          have st := (ih _ _ _ _ _ _ tele_lt_calls e1 (bounded_sub tele_sub_calls bd)).1
            rfl _ s c T rfl ht nt
          have sb := (ih _ _ _ _ _ _ tele_lt_calls e2 (bounded_sub tele_sub_calls bd)).1
            rfl _ s (c + 1) B rfl
            (by rw [SubstAux.val_succ32 hc0, show rp + (ZMod.val c + 1) + ZMod.val s =
                  rp + ZMod.val c + ZMod.val s + 1 by omega]
                exact hb.mono e1.heap_extends)
            (by rw [SubstAux.val_succ32 hc0]
                exact SubstAux.noIdx_unbody (SubstAux.idxAll_heap e1.heap_extends nb)
                  (by omega) (by omega))
          rw [SubstAux.val_succ32 hc0, show rp + (ZMod.val c + 1) = rp + ZMod.val c + 1 by omega]
            at sb
          exact tmExact_store_lam (st.mono e2.heap_extends) sb
            (hl.mono (e1.heap_extends.trans e2.heap_extends))
        | .Forall (ld12 := ld) (he369 := hr) (hm368 := hm) (ev387 := e1) (op454 := op) (ev423 := e2)
            (hc463 := hc) .. =>
          subst hc hr hm; rw [SubstAux.add_ok op] at e2
          obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.forallE_of_load ld
          obtain ⟨nt, nb⟩ := SubstAux.idxAll_forallE_inv hn ld
          have st := (ih _ _ _ _ _ _ tele_lt_calls e1 (bounded_sub tele_sub_calls bd)).1
            rfl _ s c T rfl ht nt
          have sb := (ih _ _ _ _ _ _ tele_lt_calls e2 (bounded_sub tele_sub_calls bd)).1
            rfl _ s (c + 1) B rfl
            (by rw [SubstAux.val_succ32 hc0, show rp + (ZMod.val c + 1) + ZMod.val s =
                  rp + ZMod.val c + ZMod.val s + 1 by omega]
                exact hb.mono e1.heap_extends)
            (by rw [SubstAux.val_succ32 hc0]
                exact SubstAux.noIdx_unbody (SubstAux.idxAll_heap e1.heap_extends nb)
                  (by omega) (by omega))
          rw [SubstAux.val_succ32 hc0, show rp + (ZMod.val c + 1) = rp + ZMod.val c + 1 by omega]
            at sb
          exact tmExact_store_forallE (st.mono e2.heap_extends) sb
            (hl.mono (e1.heap_extends.trans e2.heap_extends))
        | .Let (ld12 := ld) (ev491 := e1) (hc532 := hc) .. =>
          subst hc
          obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := hE.letE_of_load ld
          obtain ⟨nt, nv, nb⟩ := SubstAux.idxAll_letE_inv hn ld
          exact (ih _ _ _ _ _ _ tele_lt_calls e1 (bounded_sub tele_sub_calls bd)).2.2
            rfl _ _ _ s c T V B rfl hc0 ht hv
            (by rw [show rp + (ZMod.val c + 1) + ZMod.val s =
              rp + ZMod.val c + ZMod.val s + 1 by omega]; exact hb)
            nt nv (SubstAux.noIdx_unbody nb (by omega) (by omega))
        | .Proj (ld12 := ld) (he588 := hr) (hm587 := hm) (ev620 := e1) (hc645 := hc) .. =>
          subst hc hr hm
          obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := hE.proj_of_load ld
          exact tmExact_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e1.heap_extends ra)
            ((ih _ _ _ _ _ _ tele_lt_calls e1 (bounded_sub tele_sub_calls bd)).1
              rfl _ s c Es rfl hes (SubstAux.idxAll_proj_inv hn ld))
      · subst hfn hargs
        match Obs.«KernelSubst::expr_lower_let».obs ev with
        | .run (he5 := hr) (hm4 := hm) (ev23 := e1) (ev59 := e2) (op126 := op) (ev95 := e3)
            (hc128 := hc) .. =>
          subst hc hr hm; rw [SubstAux.add_ok op] at e3
          have hnoV : noLooseIn (ZMod.val c) (ZMod.val s) V = true := by
            simpa using noLooseIn_of_noIdx_tmExact (c := ZMod.val c) (m := 0) (ni := ZMod.val s) hv nv
          have hnoB : noLooseIn (ZMod.val c + 1) (ZMod.val s) B = true := by
            simpa using noLooseIn_of_noIdx_tmExact (c := ZMod.val c + 1) (m := 0) (ni := ZMod.val s) hb nb
          rw [lowerBVars_instShift_zero hnoV hnoB]
          have x1 := (ih _ _ _ _ _ _ tele_lt_calls e1 (bounded_sub tele_sub_calls bd)).1
            rfl _ s c T rfl ht nt
          have x2 := (ih _ _ _ _ _ _ tele_lt_calls e2 (bounded_sub tele_sub_calls bd)).1
            rfl _ s c V rfl (hv.mono e1.heap_extends) (SubstAux.idxAll_heap e1.heap_extends nv)
          have x3 := (ih _ _ _ _ _ _ tele_lt_calls e3 (bounded_sub tele_sub_calls bd)).1
            rfl _ s (c + 1) B rfl
            (by rw [SubstAux.val_succ32 hc0]; exact hb.mono (e1.heap_extends.trans e2.heap_extends))
            (by rw [SubstAux.val_succ32 hc0]
                exact SubstAux.idxAll_heap (e1.heap_extends.trans e2.heap_extends) nb)
          rw [SubstAux.val_succ32 hc0, show rp + (ZMod.val c + 1) = rp + ZMod.val c + 1 by omega]
            at x3
          exact tmExact_store_letE ((x1.mono e2.heap_extends).mono e3.heap_extends)
            (x2.mono e3.heap_extends) x3)

theorem expr_lower_local_exact {κ : _root_.Address → KKey} {rp : Nat} {Γ : Nat → KExpr}
    {e r : SourceValue F} {s : F} {h h' : Heap F} {cs : List (Call F)} {E : KExpr}
    (bd : IxVM.Consistency.Bounded cs)
    (ev : ObsFn W "KernelSubst::expr_lower" [e, .field s, .field 0] h r h' cs)
    (hE : TmExact κ 0 Γ h (rp + ZMod.val s) E e)
    (hn : NoIdx h 0 (ZMod.val s) e) :
    TmExact κ 0 Γ h' rp (E.lowerBVars (ZMod.val s) 0) r := by
  have hz : ZMod.val (0 : F) = 0 := ZMod.val_zero
  simpa [hz] using (expr_lower_local_exact_aux κ rp Γ _ _ _ _ _ _ ev bd).1 rfl e s 0 E rfl
    (by simpa [hz] using hE) (by simpa [hz] using hn)

/-! ## `Lists` wrappers, `TypesRep` / `GhostScoped` helpers, and `Rules` depth lifting -/

theorem tele_klength {α : Type} {R : Heap F → α → SourceValue F → Prop} {xs : List α}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) : r = .field (xs.length : F) ∧ h' = h :=
  SubstAux.klength ev hl

theorem tele_klookup {α : Type} {R : Heap F → α → SourceValue F → Prop} {xs : List α}
    {l r : SourceValue F} {i : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [l, .field i] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    (∃ x, xs[ZMod.val i]? = some x ∧ R h x r) ∧ h' = h :=
  SubstAux.klookup ev hl

theorem tele_ktake {α : Type} {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R)
    {xs : List α} {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::take<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    ZMod.val n ≤ xs.length ∧ RepList kexprListEnum R h' (xs.take (ZMod.val n)) r := by
  have hspec := Lib.Lists.take_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) hR
    (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hspec

theorem tele_kdrop {α : Type} {R : Heap F → α → SourceValue F → Prop}
    {xs : List α} {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    ZMod.val n ≤ xs.length ∧ RepList kexprListEnum R h (xs.drop (ZMod.val n)) r ∧ h' = h := by
  have hspec := Lib.Lists.drop_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (ZMod.val n) rfl
    (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hspec

theorem tele_kconcat {α : Type} {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R)
    {xs ys : List α} {a b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::concat<&KernelTypes::KExprNode>» [a, b] h r h' cs)
    (ha : RepList kexprListEnum R h xs a) (hb : RepList kexprListEnum R h ys b) :
    RepList kexprListEnum R h' (xs ++ ys) r := by
  have hspec := Lib.Lists.concat_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) hR
    (by rw [Obs.Names.«Lists::concat<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact ha)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hb)
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hspec

theorem getAppFn_mkAppN : ∀ (As : List KExpr) (f : KExpr),
    (Expr.mkAppN f As).getAppFn = f.getAppFn
  | [], _ => rfl
  | a :: As, f => by
    show (Expr.mkAppN (.app f a) As).getAppFn = f.getAppFn
    rw [getAppFn_mkAppN As (.app f a)]; rfl

theorem getAppArgs_mkAppN : ∀ (As : List KExpr) (f : KExpr),
    (Expr.mkAppN f As).getAppArgs = f.getAppArgs ++ As
  | [], _ => (List.append_nil _).symm
  | a :: As, f => by
    show (Expr.mkAppN (.app f a) As).getAppArgs = f.getAppArgs ++ (a :: As)
    rw [getAppArgs_mkAppN As (.app f a)]
    show (f.getAppArgs ++ [a]) ++ As = f.getAppArgs ++ (a :: As)
    rw [List.append_assoc]; rfl

theorem typesRep_congr_ghost {κ : _root_.Address → KKey} {Γ Γ' : Nat → KExpr} {h : Heap F}
    {d : Nat} {p : SourceValue F} (hΓ : ∀ j < d, Γ' j = Γ j)
    (ht : TypesRep κ Γ h d p) : TypesRep κ Γ' h d p := by
  induction ht with
  | nil cell => exact .nil cell
  | @cons d₀ addr tp rest cell rt rr ih =>
    have rt' : Tm κ d₀ Γ' h 0 (Γ d₀) tp :=
      Tm.congr_ghost (fun j hj => hΓ j (by omega)) rt
    rw [← hΓ d₀ (by omega)] at rt'
    exact .cons cell rt' (ih (fun j hj => hΓ j (by omega)))

theorem typesRep_drop (k : Nat) :
    ∀ {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {d : Nat}
      {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = k →
      ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [l, .field n] h r h' cs →
      TypesRep κ Γ h d l →
      ZMod.val n ≤ d ∧ TypesRep κ Γ h (d - ZMod.val n) r ∧ h' = h := by
  induction k with
  | zero =>
    intro κ Γ d l r n h h' cs hk ev hl
    have ev' : ObsFn W (Instance.mk "Lists::drop"
        [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol [l, .field n] h r h' cs := by
      rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev
    rcases Obs.«Lists::drop».obs ev' with ⟨hv, rfl, rfl, -⟩ |
      ⟨_, _, _, _, _, _, hne, op, _, _, _, _, -⟩
    · injection hv with hn; subst hn
      exact ⟨by simp, by simpa using hl, rfl⟩
    · have hn : n ≠ 0 := fun e => hne (by rw [e])
      have := Lib.val_sub_one hn; omega
  | succ k ih =>
    intro κ Γ d l r n h h' cs hk ev hl
    have ev' : ObsFn W (Instance.mk "Lists::drop"
        [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol [l, .field n] h r h' cs := by
      rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev
    rcases Obs.«Lists::drop».obs ev' with ⟨hv, _, _, -⟩ |
      ⟨m, p, cs', v, w, rest, hne, op, ev_rec, ld, rfl, rfl, -⟩
    · injection hv with hn; subst hn; simp at hk
    · have hn : n ≠ 0 := fun e => hne (by rw [e])
      obtain rfl := Lib.sub_one_inv op
      have hpred := Lib.val_sub_one hn
      rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol] at ev_rec
      rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at ld
      obtain ⟨hle, hdrop, rfl⟩ := ih (n := n - 1) (by omega) ev_rec hl
      generalize hdm : d - ZMod.val (n - 1) = dm at hdrop
      cases hdrop with
      | nil cell =>
        rw [Lib.load_enum_cell cell] at ld
        injection ld with hv; injection hv with _ hc _
        exact absurd hc (by decide)
      | @cons d' _ _ _ cell _ rr =>
        rw [Lib.load_enum_cell cell] at ld
        injection ld with hv; injection hv with _ _ hargs
        injection hargs with _ hrest; injection hrest with hrest _
        subst hrest
        have hd_ge : ZMod.val n ≤ d := by omega
        have hd_eq : d' = d - ZMod.val n := by omega
        subst hd_eq
        exact ⟨hd_ge, rr, rfl⟩

theorem ghostScoped_mono {Γ : Nat → KExpr} {d₁ d₂ : Nat} (hle : d₁ ≤ d₂)
    (hs : GhostScoped Γ d₂) : GhostScoped Γ d₁ :=
  fun j hj => hs j (Nat.lt_of_lt_of_le hj hle)

theorem ghostScoped_congr_ghost {Γ₁ Γ₂ : Nat → KExpr} {d : Nat}
    (hΓ : ∀ j < d, Γ₂ j = Γ₁ j) (hs : GhostScoped Γ₁ d) : GhostScoped Γ₂ d :=
  fun j hj => hΓ j hj ▸ hs j hj

theorem defEq_lift_to {κ : _root_.Address → KKey} {env : Ix.Kernel.Env .anon}
    (hsc_env : Ix.Kernel.StoreClosed env)
    {Γ : Nat → KExpr} {d depth : Nat} {h : Heap F} {a b : SourceValue F} {A B : KExpr}
    (hle : d ≤ depth) (hs : GhostScoped Γ d)
    (hA : Tm κ d Γ h 0 A a) (hB : Tm κ d Γ h 0 B b)
    (hde : DefEq env d A B) : DefEq env depth A B := by
  have hl := Ix.Kernel.Rules.DefEq.lift (Ix.Kernel.EnvExt.refl env) hsc_env (g := depth - d) hde
  rw [Ix.Kernel.Rules.renFV_lift_of_wscoped (Nat.le_refl _) (Tm.wscopedB hs hA),
    Ix.Kernel.Rules.renFV_lift_of_wscoped (Nat.le_refl _) (Tm.wscopedB hs hB),
    Nat.add_sub_of_le hle] at hl
  exact hl

theorem infer_lift_to {κ : _root_.Address → KKey} {env : Ix.Kernel.Env .anon}
    (hsc_env : Ix.Kernel.StoreClosed env)
    {Γ : Nat → KExpr} {d depth : Nat} {h h' : Heap F} {e r : SourceValue F} {E T : KExpr}
    (hle : d ≤ depth) (hs : GhostScoped Γ d)
    (hE : Tm κ d Γ h 0 E e) (hT : Tm κ d Γ h' 0 T r)
    (hinf : Infer env .full d E T) : Infer env .full depth E T := by
  have hl := Ix.Kernel.Rules.Infer.lift (Ix.Kernel.EnvExt.refl env) hsc_env (g := depth - d) hinf
  rw [Ix.Kernel.Rules.renFV_lift_of_wscoped (Nat.le_refl _) (Tm.wscopedB hs hE),
    Ix.Kernel.Rules.renFV_lift_of_wscoped (Nat.le_refl _) (Tm.wscopedB hs hT),
    Nat.add_sub_of_le hle] at hl
  exact hl

/-! ## `rename_addr`, `rename`, and `rename_list` -/

/-- Pure address lookup along parallel `(src, dst)` lists matching `KernelModeled::rename_addr`. -/
def renameBytesAddr (a : Bytes.Address) : List Bytes.Address → List Bytes.Address → Bytes.Address
  | s :: ss, t :: ts => if a = s then t else renameBytesAddr a ss ts
  | _, _ => a

/-- Representation invariant relating parallel heap address lists `(src, dst)` to a kernel
constant-key renaming `f : KKey → KKey` from keying `κ₁` to keying `κ₂`. -/
def RenameMap (κ₁ κ₂ : _root_.Address → KKey) (f : KKey → KKey)
    (h : Heap F) (src dst : SourceValue F) : Prop :=
  ∃ srcAs dstAs,
    RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src ∧
    RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst ∧
    srcAs.length = dstAs.length ∧
    ∀ a : Bytes.Address, κ₂ (ixAddr (renameBytesAddr a srcAs dstAs)) = f (κ₁ (ixAddr a))

theorem RenameMap.mono {κ₁ κ₂ : _root_.Address → KKey} {f : KKey → KKey}
    {h₁ h₂ : Heap F} {src dst : SourceValue F} (ext : Heap.Extends h₁ h₂)
    (rm : RenameMap κ₁ κ₂ f h₁ src dst) : RenameMap κ₁ κ₂ f h₂ src dst := by
  obtain ⟨srcAs, dstAs, hsrc, hdst, hlen, hmap⟩ := rm
  exact ⟨srcAs, dstAs,
    RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext hsrc,
    RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext hdst,
    hlen, hmap⟩

theorem renameAll_instantiateLevelParams (ks : List LevelParam) (us : List KLevel)
    (f : KKey → KKey) :
    ∀ e : KExpr,
      (renameAll f e).instantiateLevelParams ks us =
        renameAll f (e.instantiateLevelParams ks us) := by
  intro e
  induction e <;> simp_all [renameAll, Expr.instantiateLevelParams]

private theorem rename_addr_go {srcAs : List Bytes.Address} :
    ∀ {dstAs : List Bytes.Address} {a : Bytes.Address}
      {ap src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      srcAs.length = dstAs.length →
      ObsFn W "KernelModeled::rename_addr" [ap, src, dst] h r h' cs →
      Bytes.RepAddressRef addrTy h a ap →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst →
      Bytes.RepAddressRef addrTy h (renameBytesAddr a srcAs dstAs) r ∧ h' = h := by
  induction srcAs with
  | nil =>
    intro dstAs a ap src dst r h h' cs hlen ev ha hsrc hdst
    cases dstAs with
    | nil =>
      rcases Obs.«KernelModeled::rename_addr».obs ev with ⟨_, rfl, rfl, _⟩ |
        ⟨_, _, _, _, _, _, ld, _, _, _, _⟩ | ⟨_, _, _, _, _, _, _, _, ld, _, _, _, _, _⟩
      · exact ⟨ha, rfl⟩
      · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hsrc ld; cases he
      · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hsrc ld; cases he
    | cons _ _ => cases hlen
  | cons s ss ih =>
    intro dstAs a ap src dst r h h' cs hlen ev ha hsrc hdst
    cases dstAs with
    | nil => cases hlen
    | cons t ts =>
      have hlen' : ss.length = ts.length := Nat.succ.inj hlen
      rcases Obs.«KernelModeled::rename_addr».obs ev with ⟨ld, _, _, _⟩ |
        ⟨_, _, _, _, _, _, ld_s, ld_d, ev_eq, rfl, rfl, _⟩ |
        ⟨_, _, _, _, _, _, _, _, ld_s, ld_d, ev_eq, hne, ev_rec, _⟩
      · cases Lib.rep_nil_of_load hsrc ld
      · obtain ⟨s', ss', hs_eq, hs_rep, _⟩ := Lib.rep_cons_of_load hsrc ld_s
        obtain ⟨t', ts', ht_eq, ht_rep, _⟩ := Lib.rep_cons_of_load hdst ld_d
        injection hs_eq with h1 h2; subst h1 h2
        injection ht_eq with h1 h2; subst h1 h2
        obtain ⟨heq_f, rfl⟩ := Lib.address_eq_spec ev_eq ha hs_rep
        have has : a = s := by
          by_cases h' : a = s
          · exact h'
          · rw [ite_eq_right h'] at heq_f; injection heq_f with hf; exact absurd hf one_ne_zero
        simp only [renameBytesAddr, ite_eq_left has]
        exact ⟨ht_rep, trivial⟩
      · obtain ⟨s', ss', hs_eq, hs_rep, hss_rep⟩ := Lib.rep_cons_of_load hsrc ld_s
        obtain ⟨t', ts', ht_eq, _, hts_rep⟩ := Lib.rep_cons_of_load hdst ld_d
        injection hs_eq with h1 h2; subst h1 h2
        injection ht_eq with h1 h2; subst h1 h2
        obtain ⟨heq_f, rfl⟩ := Lib.address_eq_spec ev_eq ha hs_rep
        have has : a ≠ s := by
          intro h'; subst h'; simp at heq_f; exact hne heq_f
        simp only [renameBytesAddr, ite_eq_right has]
        exact ih hlen' ev_rec ha hss_rep hts_rep

theorem rename_addr_spec {κ₁ κ₂ : _root_.Address → KKey} {f : KKey → KKey}
    {a : Bytes.Address} {ap src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelModeled::rename_addr" [ap, src, dst] h r h' cs)
    (ha : Bytes.RepAddressRef addrTy h a ap)
    (rm : RenameMap κ₁ κ₂ f h src dst) :
    (∃ a', Bytes.RepAddressRef addrTy h a' r ∧ κ₂ (ixAddr a') = f (κ₁ (ixAddr a))) ∧ h' = h := by
  obtain ⟨srcAs, dstAs, hsrc, hdst, hlen, hmap⟩ := rm
  obtain ⟨hr, rfl⟩ := rename_addr_go hlen ev ha hsrc hdst
  exact ⟨⟨renameBytesAddr a srcAs dstAs, hr, hmap a⟩, rfl⟩

/-- Exact VM refinement of `KernelModeled::rename`: renames constants and structure keys by `f`. -/
theorem rename_exact {κ₁ κ₂ : _root_.Address → KKey} {f : KKey → KKey}
    {Γ₁ Γ₂ : Nat → KExpr} :
    ∀ {e src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr},
      ObsFn W "KernelModeled::rename" [e, src, dst] h r h' cs →
      TmExact κ₁ 0 Γ₁ h k E e →
      RenameMap κ₁ κ₂ f h src dst →
      TmExact κ₂ 0 Γ₂ h' k (renameAll f E) r := by
  have hmain : ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelModeled::rename" →
      ∀ (e src dst : SourceValue F) (k : Nat) (E : KExpr),
        args = [e, src, dst] →
        TmExact κ₁ 0 Γ₁ h k E e → RenameMap κ₁ κ₂ f h src dst →
        TmExact κ₂ 0 Γ₂ h' k (renameAll f E) r :=
    ObsFn.strong_induction (world := W)
      (fun fname args h r h' cs => fname = "KernelModeled::rename" →
        ∀ (e src dst : SourceValue F) (k : Nat) (E : KExpr),
          args = [e, src, dst] →
          TmExact κ₁ 0 Γ₁ h k E e → RenameMap κ₁ κ₂ f h src dst →
          TmExact κ₂ 0 Γ₂ h' k (renameAll f E) r)
      (fun fname args h r h' cs ev ih hfn e src dst k E hargs hE rm => by
        subst hfn hargs
        match Obs.«KernelModeled::rename».obs ev with
        | .Const (ld12 := ld) (he34 := hr) (hm33 := hm) (ev51 := e1) .. =>
          subst hr hm
          obtain ⟨a, ls, rfl, ra, rls⟩ := hE.const_of_load ld
          obtain ⟨⟨a', ra', hka⟩, rfl⟩ := rename_addr_spec e1 ra rm
          simp only [renameAll, ← hka]
          exact .const (by simp) (Bytes.repAddressRef_heapMono₂ addrTy (Heap.Extends.snoc _ _) ra')
            (rls.mono (Heap.Extends.snoc _ _))
        | .App (ld12 := ld) (he105 := hr) (hm104 := hm) (ev122 := e1) (ev158 := e2)
            (hc183 := hc) .. =>
          subst hc hr hm
          obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
          have sf := ih _ _ _ _ _ _ tele_lt_calls e1 rfl _ src dst k Ef rfl hf rm
          have sa := ih _ _ _ _ _ _ tele_lt_calls e2 rfl _ src dst k Ea rfl
            (ha.mono e1.heap_extends) (rm.mono e1.heap_extends)
          exact tmExact_store_app (sf.mono e2.heap_extends) sa
        | .Lam (ld12 := ld) (he210 := hr) (hm209 := hm) (ev228 := e1) (ev264 := e2)
            (hc296 := hc) .. =>
          subst hc hr hm
          obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.lam_of_load ld
          have st := ih _ _ _ _ _ _ tele_lt_calls e1 rfl _ src dst k T rfl ht rm
          have sb := ih _ _ _ _ _ _ tele_lt_calls e2 rfl _ src dst (k + 1) B rfl
            (hb.mono e1.heap_extends) (rm.mono e1.heap_extends)
          exact tmExact_store_lam (st.mono e2.heap_extends) sb
            (hl.mono (e1.heap_extends.trans e2.heap_extends))
        | .Forall (ld12 := ld) (he323 := hr) (hm322 := hm) (ev341 := e1) (ev377 := e2)
            (hc409 := hc) .. =>
          subst hc hr hm
          obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.forallE_of_load ld
          have st := ih _ _ _ _ _ _ tele_lt_calls e1 rfl _ src dst k T rfl ht rm
          have sb := ih _ _ _ _ _ _ tele_lt_calls e2 rfl _ src dst (k + 1) B rfl
            (hb.mono e1.heap_extends) (rm.mono e1.heap_extends)
          exact tmExact_store_forallE (st.mono e2.heap_extends) sb
            (hl.mono (e1.heap_extends.trans e2.heap_extends))
        | .Let (ld12 := ld) (he436 := hr) (hm435 := hm) (ev454 := e1) (ev490 := e2)
            (ev526 := e3) (hc551 := hc) .. =>
          subst hc hr hm
          obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := hE.letE_of_load ld
          rw [renameAll_instShift]
          have st := ih _ _ _ _ _ _ tele_lt_calls e1 rfl _ src dst k T rfl ht rm
          have sv := ih _ _ _ _ _ _ tele_lt_calls e2 rfl _ src dst k V rfl
            (hv.mono e1.heap_extends) (rm.mono e1.heap_extends)
          have sb := ih _ _ _ _ _ _ tele_lt_calls e3 rfl _ src dst (k + 1) B rfl
            (hb.mono (e1.heap_extends.trans e2.heap_extends))
            (rm.mono (e1.heap_extends.trans e2.heap_extends))
          exact tmExact_store_letE ((st.mono e2.heap_extends).mono e3.heap_extends)
            (sv.mono e3.heap_extends) sb
        | .Proj (ld12 := ld) (he578 := hr) (hm577 := hm) (ev596 := e1) (ev639 := e2)
            (hc664 := hc) .. =>
          subst hc hr hm
          obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := hE.proj_of_load ld
          obtain ⟨⟨a', ra', hka⟩, rfl⟩ := rename_addr_spec e1 ra rm
          have ses := ih _ _ _ _ _ _ tele_lt_calls e2 rfl _ src dst k Es rfl hes rm
          simp only [renameAll, ← hka]
          exact tmExact_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e2.heap_extends ra') ses
        | .other (ld12 := ld) (hne84 := n1) (hne184 := n2) (hne297 := n3) (hne410 := n4)
            (hne552 := n5) (hne665 := n6) (he670 := hr) (he671 := hh) .. =>
          subst hr hh
          cases hE with
          | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
          | bvarFree _ _ _ hd => exact nomatch hd
          | sort cell rl => exact .sort cell rl
          | const cell _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n1 _ rfl)
          | app cell _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n2 _ rfl)
          | lam cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n3 _ rfl)
          | forallE cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n4 _ rfl)
          | letE cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n5 _ rfl)
          | litNat cell rl hc => exact .litNat cell rl hc
          | litStr cell rb hs => exact .litStr cell rb hs
          | proj cell _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n6 _ rfl))
  intro e src dst r h h' cs k E ev hE rm
  exact hmain _ _ _ _ _ _ ev rfl e src dst k E rfl hE rm

/-- `Tm` counterpart of `rename_exact` (used on `cty_l` after `expr_inst_levels`). -/
theorem rename_tm {κ₁ κ₂ : _root_.Address → KKey} {f : KKey → KKey}
    {Γ₁ Γ₂ : Nat → KExpr} :
    ∀ {e src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr},
      ObsFn W "KernelModeled::rename" [e, src, dst] h r h' cs →
      Tm κ₁ 0 Γ₁ h k E e →
      RenameMap κ₁ κ₂ f h src dst →
      Tm κ₂ 0 Γ₂ h' k (renameAll f E) r := by
  have hmain : ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelModeled::rename" →
      ∀ (e src dst : SourceValue F) (k : Nat) (E : KExpr),
        args = [e, src, dst] →
        Tm κ₁ 0 Γ₁ h k E e → RenameMap κ₁ κ₂ f h src dst →
        Tm κ₂ 0 Γ₂ h' k (renameAll f E) r :=
    ObsFn.strong_induction (world := W)
      (fun fname args h r h' cs => fname = "KernelModeled::rename" →
        ∀ (e src dst : SourceValue F) (k : Nat) (E : KExpr),
          args = [e, src, dst] →
          Tm κ₁ 0 Γ₁ h k E e → RenameMap κ₁ κ₂ f h src dst →
          Tm κ₂ 0 Γ₂ h' k (renameAll f E) r)
      (fun fname args h r h' cs ev ih hfn e src dst k E hargs hE rm => by
        subst hfn hargs
        match Obs.«KernelModeled::rename».obs ev with
        | .Const (ld12 := ld) (he34 := hr) (hm33 := hm) (ev51 := e1) .. =>
          subst hr hm
          obtain ⟨a, us, rfl, ra, ls, rls, hus⟩ := hE.const_of_load ld
          obtain ⟨⟨a', ra', hka⟩, rfl⟩ := rename_addr_spec e1 ra rm
          simp only [renameAll, ← hka]
          exact .const (by simp) (Bytes.repAddressRef_heapMono₂ addrTy (Heap.Extends.snoc _ _) ra')
            (rls.mono (Heap.Extends.snoc _ _)) hus
        | .App (ld12 := ld) (he105 := hr) (hm104 := hm) (ev122 := e1) (ev158 := e2)
            (hc183 := hc) .. =>
          subst hc hr hm
          obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
          have sf := ih _ _ _ _ _ _ tele_lt_calls e1 rfl _ src dst k Ef rfl hf rm
          have sa := ih _ _ _ _ _ _ tele_lt_calls e2 rfl _ src dst k Ea rfl
            (ha.mono e1.heap_extends) (rm.mono e1.heap_extends)
          exact Tm.store_app (sf.mono e2.heap_extends) sa
        | .Lam (ld12 := ld) (he210 := hr) (hm209 := hm) (ev228 := e1) (ev264 := e2)
            (hc296 := hc) .. =>
          subst hc hr hm
          obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.lam_of_load ld
          have st := ih _ _ _ _ _ _ tele_lt_calls e1 rfl _ src dst k T rfl ht rm
          have sb := ih _ _ _ _ _ _ tele_lt_calls e2 rfl _ src dst (k + 1) B rfl
            (hb.mono e1.heap_extends) (rm.mono e1.heap_extends)
          exact SubstAux.tm_store_lam (st.mono e2.heap_extends) sb
            (hl.mono (e1.heap_extends.trans e2.heap_extends))
        | .Forall (ld12 := ld) (he323 := hr) (hm322 := hm) (ev341 := e1) (ev377 := e2)
            (hc409 := hc) .. =>
          subst hc hr hm
          obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.forallE_of_load ld
          have st := ih _ _ _ _ _ _ tele_lt_calls e1 rfl _ src dst k T rfl ht rm
          have sb := ih _ _ _ _ _ _ tele_lt_calls e2 rfl _ src dst (k + 1) B rfl
            (hb.mono e1.heap_extends) (rm.mono e1.heap_extends)
          exact SubstAux.tm_store_forallE (st.mono e2.heap_extends) sb
            (hl.mono (e1.heap_extends.trans e2.heap_extends))
        | .Let (ld12 := ld) (he436 := hr) (hm435 := hm) (ev454 := e1) (ev490 := e2)
            (ev526 := e3) (hc551 := hc) .. =>
          subst hc hr hm
          obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := hE.letE_of_load ld
          rw [renameAll_instShift]
          have st := ih _ _ _ _ _ _ tele_lt_calls e1 rfl _ src dst k T rfl ht rm
          have sv := ih _ _ _ _ _ _ tele_lt_calls e2 rfl _ src dst k V rfl
            (hv.mono e1.heap_extends) (rm.mono e1.heap_extends)
          have sb := ih _ _ _ _ _ _ tele_lt_calls e3 rfl _ src dst (k + 1) B rfl
            (hb.mono (e1.heap_extends.trans e2.heap_extends))
            (rm.mono (e1.heap_extends.trans e2.heap_extends))
          exact SubstAux.tm_store_letE ((st.mono e2.heap_extends).mono e3.heap_extends)
            (sv.mono e3.heap_extends) sb
        | .Proj (ld12 := ld) (he578 := hr) (hm577 := hm) (ev596 := e1) (ev639 := e2)
            (hc664 := hc) .. =>
          subst hc hr hm
          obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := hE.proj_of_load ld
          obtain ⟨⟨a', ra', hka⟩, rfl⟩ := rename_addr_spec e1 ra rm
          have ses := ih _ _ _ _ _ _ tele_lt_calls e2 rfl _ src dst k Es rfl hes rm
          simp only [renameAll, ← hka]
          exact SubstAux.tm_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e2.heap_extends ra') ses
        | .other (ld12 := ld) (hne84 := n1) (hne184 := n2) (hne297 := n3) (hne410 := n4)
            (hne552 := n5) (hne665 := n6) (he670 := hr) (he671 := hh) .. =>
          subst hr hh
          cases hE with
          | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
          | bvarFree _ _ _ hd => exact nomatch hd
          | sort cell rl hu => exact .sort cell rl hu
          | const cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n1 _ rfl)
          | app cell _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n2 _ rfl)
          | lam cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n3 _ rfl)
          | forallE cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n4 _ rfl)
          | letE cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n5 _ rfl)
          | litNat cell rl hc => exact .litNat cell rl hc
          | litStr cell rb hs => exact .litStr cell rb hs
          | proj cell _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n6 _ rfl))
  intro e src dst r h h' cs k E ev hE rm
  exact hmain _ _ _ _ _ _ ev rfl e src dst k E rfl hE rm

theorem rename_list_exact {κ₁ κ₂ : _root_.Address → KKey} {f : KKey → KKey}
    {Γ₁ Γ₂ : Nat → KExpr} {k : Nat} {Es : List KExpr} :
    ∀ {es src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelModeled::rename_list" [es, src, dst] h r h' cs →
      RepList kexprListEnum (fun h E p => TmExact κ₁ 0 Γ₁ h k E p) h Es es →
      RenameMap κ₁ κ₂ f h src dst →
      RepList kexprListEnum (fun h E p => TmExact κ₂ 0 Γ₂ h k E p) h' (Es.map (renameAll f)) r := by
  induction Es with
  | nil =>
    intro es src dst r h h' cs ev hes _
    rcases Obs.«KernelModeled::rename_list».obs ev with ⟨_, rfl, rfl, _⟩ |
      ⟨_, _, _, _, _, _, _, _, ld, _, _, _, _, _⟩
    · exact .nil (by simp)
    · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hes ld; cases he
  | cons E Es ih =>
    intro es src dst r h h' cs ev hes rm
    rcases Obs.«KernelModeled::rename_list».obs ev with ⟨ld, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, ld, rfl, rfl, ev1, ev2, _⟩
    · cases Lib.rep_nil_of_load hes ld
    · obtain ⟨E', Es', he, hE, hEs⟩ := Lib.rep_cons_of_load hes ld
      injection he with h1 h2; subst h1 h2
      have sE := rename_exact (Γ₂ := Γ₂) ev1 hE rm
      have sEs := ih ev2 (RepLinkedList.mono (fun _ _ _ _ ext x => x.mono ext) ev1.heap_extends hEs)
        (rm.mono ev1.heap_extends)
      exact Lib.rep_store_cons (fun _ _ _ _ ext x => x.mono ext) (sE.mono ev2.heap_extends) sEs


/-! ## Telescope algebra, `LamTeleWalkJ`, and `posOf` lifting -/

theorem TmExact.of_depth_zero {κ : _root_.Address → KKey} {Γ Γ' : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : TmExact κ 0 Γ h k E p) :
    ∀ d, TmExact κ d Γ' h k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact fun _ => .bvarLocal cell hs hi
  | bvarFree _ _ _ hd => exact nomatch hd
  | sort cell rl => exact fun _ => .sort cell rl
  | const cell ra rls => exact fun _ => .const cell ra rls
  | app cell _ _ ihf iha => exact fun d => .app cell (ihf d) (iha d)
  | lam cell _ _ rl iht ihb => exact fun d => .lam cell (iht d) (ihb d) rl
  | forallE cell _ _ rl iht ihb => exact fun d => .forallE cell (iht d) (ihb d) rl
  | letE cell _ _ _ iht ihv ihb => exact fun d => .letE cell (iht d) (ihv d) (ihb d)
  | litNat cell rl hc => exact fun _ => .litNat cell rl hc
  | litStr cell rb hs => exact fun _ => .litStr cell rb hs
  | proj cell ra _ ihe => exact fun d => .proj cell ra (ihe d)

theorem constsResolve_lowerBVars (env : Ix.Kernel.Env .anon) (n : Nat) :
    ∀ (e : KExpr) (c : Nat),
      (e.lowerBVars n c).constsResolve env = e.constsResolve env := by
  intro e
  induction e with
  | bvar i => intro c; simp only [Expr.lowerBVars]; split <;> rfl
  | fvar _ ty ih => intro c; simp only [Expr.lowerBVars, Expr.constsResolve, ih c]
  | sort _ | const _ _ | lit _ => intro _; rfl
  | app f a ihf iha =>
    intro c; simp only [Expr.lowerBVars, Expr.constsResolve, ihf c, iha c]
  | lam t b _ iht ihb =>
    intro c; simp only [Expr.lowerBVars, Expr.constsResolve, iht c, ihb (c + 1)]
  | forallE t b _ iht ihb =>
    intro c; simp only [Expr.lowerBVars, Expr.constsResolve, iht c, ihb (c + 1)]
  | letE t v b _ iht ihv ihb =>
    intro c; simp only [Expr.lowerBVars, Expr.constsResolve, iht c, ihv c, ihb (c + 1)]
  | proj _ _ e ih =>
    intro c; simp only [Expr.lowerBVars, Expr.constsResolve, ih c]

/-- `λ`-telescope counterpart of `Ix.Kernel.openPisAtFvars`: opens `n` syntactic `λ`-binders at
fresh free variables `i, …, i + n - 1` annotated with each binder's own progressively opened domain
(matching `KernelModeled::defeq_lam_tele`). -/
def openLamsAtFvars : Nat → KExpr → Nat → Option (List KExpr × KExpr)
  | 0, e, _ => some ([], e)
  | n + 1, .lam dom body _, i =>
    let fv : KExpr := .fvar i dom
    match openLamsAtFvars n (body.instantiate1 fv) (i + 1) with
    | some (fvs, e) => some (fv :: fvs, e)
    | none => none
  | _ + 1, _, _ => none

theorem openLamsAtFvars_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (n : Nat) (e : KExpr) (i : Nat),
      openLamsAtFvars n (e.instantiateLevelParams ks us) i =
        (openLamsAtFvars n e i).map (fun p =>
          (p.1.map (·.instantiateLevelParams ks us), p.2.instantiateLevelParams ks us))
  | 0, _, _ => rfl
  | n + 1, .lam dom body m, i => by
    simp only [Expr.instantiateLevelParams, openLamsAtFvars,
      ← Expr.instantiateLevelParams_instantiate1 ks us body 0,
      openLamsAtFvars_instantiateLevelParams ks us n (body.instantiate1 (.fvar i dom)) (i + 1)]
    cases openLamsAtFvars n (body.instantiate1 (.fvar i dom)) (i + 1) <;> rfl
  | _ + 1, .bvar _, _ | _ + 1, .fvar _ _, _ | _ + 1, .sort _, _ | _ + 1, .const _ _, _
  | _ + 1, .app _ _, _ | _ + 1, .forallE _ _ _, _ | _ + 1, .letE _ _ _ _, _ | _ + 1, .lit _, _
  | _ + 1, .proj _ _ _, _ => rfl

theorem openPisAtFvars_of_posOf {ps : List LevelParam} {n : Nat} {e : KExpr} {i : Nat}
    {fvs_pos : List KExpr} {rem_pos : KExpr}
    (h : Ix.Kernel.openPisAtFvars n (posOf ps e) i = some (fvs_pos, rem_pos)) :
    ∃ fvs rem, Ix.Kernel.openPisAtFvars n e i = some (fvs, rem) ∧
      fvs_pos = fvs.map (posOf ps) ∧ rem_pos = posOf ps rem := by
  unfold posOf at h
  rw [openPisAtFvars_instantiateLevelParams] at h
  cases hop : Ix.Kernel.openPisAtFvars n e i with
  | none => simp [hop] at h
  | some p =>
    rw [hop] at h
    injection h with hp
    injection hp with h1 h2
    exact ⟨p.1, p.2, rfl, h1.symm, h2.symm⟩

theorem openLamsAtFvars_of_posOf {ps : List LevelParam} {n : Nat} {e : KExpr} {i : Nat}
    {fvs_pos : List KExpr} {rem_pos : KExpr}
    (h : openLamsAtFvars n (posOf ps e) i = some (fvs_pos, rem_pos)) :
    ∃ fvs rem, openLamsAtFvars n e i = some (fvs, rem) ∧
      fvs_pos = fvs.map (posOf ps) ∧ rem_pos = posOf ps rem := by
  unfold posOf at h
  rw [openLamsAtFvars_instantiateLevelParams] at h
  cases hop : openLamsAtFvars n e i with
  | none => simp [hop] at h
  | some p =>
    rw [hop] at h
    injection h with hp
    injection hp with h1 h2
    exact ⟨p.1, p.2, rfl, h1.symm, h2.symm⟩

theorem instPisAt_of_posOf {ps : List LevelParam} {xs : List KExpr} {e : KExpr}
    {doms_pos : List KExpr} {rem_pos : KExpr}
    (h : Expr.instPisAt (xs.map (posOf ps)) (posOf ps e) = some (doms_pos, rem_pos)) :
    ∃ doms rem, Expr.instPisAt xs e = some (doms, rem) ∧
      doms_pos = doms.map (posOf ps) ∧ rem_pos = posOf ps rem := by
  unfold posOf at h
  rw [instPisAt_instantiateLevelParams] at h
  cases hip : Expr.instPisAt xs e with
  | none => simp [hip] at h
  | some p =>
    rw [hip] at h
    injection h with hp
    injection hp with h1 h2
    exact ⟨p.1, p.2, rfl, h1.symm, h2.symm⟩

theorem instPisAt_length :
    ∀ {xs : List KExpr} {e : KExpr} {ds : List KExpr} {rest : KExpr},
      Expr.instPisAt xs e = some (ds, rest) → ds.length = xs.length
  | [], _, _, _, h => by injection h with hp; injection hp with h1 _; subst h1; rfl
  | a :: as, .forallE _ body _, _, _, h => by
    simp only [Expr.instPisAt] at h
    cases hip : Expr.instPisAt as (body.instantiate1 a) with
    | none => simp [hip] at h
    | some p =>
      rw [hip] at h
      injection h with hp; injection hp with h1 _
      subst h1
      simp [instPisAt_length hip]
  | _ :: _, .bvar _, _, _, h | _ :: _, .fvar _ _, _, _, h | _ :: _, .sort _, _, _, h
  | _ :: _, .const _ _, _, _, h | _ :: _, .app _ _, _, _, h | _ :: _, .lam _ _ _, _, _, h
  | _ :: _, .letE _ _ _ _, _, _, h | _ :: _, .lit _, _, _, h | _ :: _, .proj _ _ _, _, _, h =>
    nomatch h

theorem instPisAt_append :
    ∀ (xs ys : List KExpr) (e : KExpr),
      Expr.instPisAt (xs ++ ys) e =
        match Expr.instPisAt xs e with
        | some (d1, r1) => (Expr.instPisAt ys r1).map fun (d2, r2) => (d1 ++ d2, r2)
        | none => none
  | [], ys, e => by
    simp only [List.nil_append, Expr.instPisAt]
    cases Expr.instPisAt ys e <;> rfl
  | a :: as, ys, .forallE dom body m => by
    simp only [List.cons_append, Expr.instPisAt, instPisAt_append as ys (body.instantiate1 a)]
    rcases Expr.instPisAt as (body.instantiate1 a) with _ | ⟨d1, r1⟩
    · rfl
    · simp only [Option.map_some]
      rcases Expr.instPisAt ys r1 with _ | ⟨d2, r2⟩ <;> rfl
  | _ :: _, _, .bvar _ | _ :: _, _, .fvar _ _ | _ :: _, _, .sort _ | _ :: _, _, .const _ _
  | _ :: _, _, .app _ _ | _ :: _, _, .lam _ _ _ | _ :: _, _, .letE _ _ _ _ | _ :: _, _, .lit _
  | _ :: _, _, .proj _ _ _ => rfl

theorem openPisAtFvars_spec :
    ∀ (n : Nat) (e : KExpr) (i : Nat) {fvs : List KExpr} {rest : KExpr},
      Ix.Kernel.openPisAtFvars n e i = some (fvs, rest) →
      fvs.length = n ∧
        Expr.instPisAt fvs e = some (fvs.map Expr.fvarTypeD, rest) ∧
        ∀ j (hj : j < fvs.length), fvs[j] = .fvar (i + j) (fvs[j].fvarTypeD)
  | 0, _, _, _, _, h => by
    injection h with hp; injection hp with h1 h2; subst h1 h2
    exact ⟨rfl, rfl, fun _ hj => nomatch hj⟩
  | n + 1, .forallE dom body m, i, _, _, h => by
    simp only [Ix.Kernel.openPisAtFvars] at h
    cases hop : Ix.Kernel.openPisAtFvars n (body.instantiate1 (.fvar i dom)) (i + 1) with
    | none => simp [hop] at h
    | some p =>
      rw [hop] at h
      injection h with hp; injection hp with h1 h2; subst h1 h2
      obtain ⟨hlen, hinst, hfv⟩ := openPisAtFvars_spec n _ (i + 1) hop
      refine ⟨by simp [hlen], by simp [Expr.instPisAt, hinst, Expr.fvarTypeD], ?_⟩
      intro j hj
      cases j with
      | zero => simp [Expr.fvarTypeD]
      | succ k =>
        have hk : k < p.1.length := by simp at hj; omega
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using hfv k hk
  | _ + 1, .bvar _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, h | _ + 1, .sort _, _, _, _, h
  | _ + 1, .const _ _, _, _, _, h | _ + 1, .app _ _, _, _, _, h | _ + 1, .lam _ _ _, _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, _, h | _ + 1, .lit _, _, _, _, h | _ + 1, .proj _ _ _, _, _, _, h =>
    nomatch h

theorem openLamsAtFvars_spec :
    ∀ (n : Nat) (e : KExpr) (i : Nat) {fvs : List KExpr} {rest : KExpr},
      openLamsAtFvars n e i = some (fvs, rest) →
      fvs.length = n ∧
        Expr.instLamsAt fvs e = some (fvs.map Expr.fvarTypeD, rest) ∧
        ∀ j (hj : j < fvs.length), fvs[j] = .fvar (i + j) (fvs[j].fvarTypeD)
  | 0, _, _, _, _, h => by
    injection h with hp; injection hp with h1 h2; subst h1 h2
    exact ⟨rfl, rfl, fun _ hj => nomatch hj⟩
  | n + 1, .lam dom body m, i, _, _, h => by
    simp only [openLamsAtFvars] at h
    cases hop : openLamsAtFvars n (body.instantiate1 (.fvar i dom)) (i + 1) with
    | none => simp [hop] at h
    | some p =>
      rw [hop] at h
      injection h with hp; injection hp with h1 h2; subst h1 h2
      obtain ⟨hlen, hinst, hfv⟩ := openLamsAtFvars_spec n _ (i + 1) hop
      refine ⟨by simp [hlen], by simp [Expr.instLamsAt, hinst, Expr.fvarTypeD], ?_⟩
      intro j hj
      cases j with
      | zero => simp [Expr.fvarTypeD]
      | succ k =>
        have hk : k < p.1.length := by simp at hj; omega
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using hfv k hk
  | _ + 1, .bvar _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, h | _ + 1, .sort _, _, _, _, h
  | _ + 1, .const _ _, _, _, _, h | _ + 1, .app _ _, _, _, _, h | _ + 1, .forallE _ _ _, _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, _, h | _ + 1, .lit _, _, _, _, h | _ + 1, .proj _ _ _, _, _, _, h =>
    nomatch h

theorem openPisAtFvars_split :
    ∀ (n1 n2 : Nat) (e : KExpr) (i : Nat),
      Ix.Kernel.openPisAtFvars (n1 + n2) e i =
        match Ix.Kernel.openPisAtFvars n1 e i with
        | some (fvs1, r1) =>
          (Ix.Kernel.openPisAtFvars n2 r1 (i + n1)).map fun (fvs2, r2) => (fvs1 ++ fvs2, r2)
        | none => none
  | 0, n2, e, i => by
    simp only [Nat.zero_add, Nat.add_zero, Ix.Kernel.openPisAtFvars]
    cases Ix.Kernel.openPisAtFvars n2 e i <;> rfl
  | n1 + 1, n2, .forallE dom body m, i => by
    rw [show n1 + 1 + n2 = n1 + n2 + 1 by omega]
    simp only [Ix.Kernel.openPisAtFvars,
      openPisAtFvars_split n1 n2 (body.instantiate1 (.fvar i dom)) (i + 1),
      show i + 1 + n1 = i + (n1 + 1) by omega]
    rcases Ix.Kernel.openPisAtFvars n1 (body.instantiate1 (.fvar i dom)) (i + 1) with
      _ | ⟨fvs1, r1⟩
    · rfl
    · dsimp only; rcases Ix.Kernel.openPisAtFvars n2 r1 (i + (n1 + 1)) with _ | ⟨fvs2, r2⟩ <;> rfl
  | n1 + 1, n2, .bvar _, _ | n1 + 1, n2, .fvar _ _, _ | n1 + 1, n2, .sort _, _
  | n1 + 1, n2, .const _ _, _ | n1 + 1, n2, .app _ _, _ | n1 + 1, n2, .lam _ _ _, _
  | n1 + 1, n2, .letE _ _ _ _, _ | n1 + 1, n2, .lit _, _ | n1 + 1, n2, .proj _ _ _, _ => by
    rw [show n1 + 1 + n2 = (n1 + n2) + 1 by omega]; rfl

theorem openLamsAtFvars_split :
    ∀ (n1 n2 : Nat) (e : KExpr) (i : Nat),
      openLamsAtFvars (n1 + n2) e i =
        match openLamsAtFvars n1 e i with
        | some (fvs1, r1) =>
          (openLamsAtFvars n2 r1 (i + n1)).map fun (fvs2, r2) => (fvs1 ++ fvs2, r2)
        | none => none
  | 0, n2, e, i => by
    simp only [Nat.zero_add, Nat.add_zero, openLamsAtFvars]
    cases openLamsAtFvars n2 e i <;> rfl
  | n1 + 1, n2, .lam dom body m, i => by
    rw [show n1 + 1 + n2 = n1 + n2 + 1 by omega]
    simp only [openLamsAtFvars,
      openLamsAtFvars_split n1 n2 (body.instantiate1 (.fvar i dom)) (i + 1),
      show i + 1 + n1 = i + (n1 + 1) by omega]
    rcases openLamsAtFvars n1 (body.instantiate1 (.fvar i dom)) (i + 1) with
      _ | ⟨fvs1, r1⟩
    · rfl
    · dsimp only; rcases openLamsAtFvars n2 r1 (i + (n1 + 1)) with _ | ⟨fvs2, r2⟩ <;> rfl
  | n1 + 1, n2, .bvar _, _ | n1 + 1, n2, .fvar _ _, _ | n1 + 1, n2, .sort _, _
  | n1 + 1, n2, .const _ _, _ | n1 + 1, n2, .app _ _, _ | n1 + 1, n2, .forallE _ _ _, _
  | n1 + 1, n2, .letE _ _ _ _, _ | n1 + 1, n2, .lit _, _ | n1 + 1, n2, .proj _ _ _, _ => by
    rw [show n1 + 1 + n2 = (n1 + n2) + 1 by omega]; rfl

/-- VM `defeq_lam_tele` walk judgment: opens `rP + cnF` `λ`-binders of `rhsA` in `rhsA`'s own
domain context `lfvs`, instantiates the recursor's `rP` prefix domains and the constructor's `cnF`
field domains at `lfvs`, and equates `lfvs.map Expr.fvarTypeD` against `pdoms1 ++ pdoms2`. -/
def LamTeleWalkJ (J : Judgements .anon) (envSelf : Ix.Kernel.Env .anon)
    (rP cnF : Nat) (tyA ctyInst : KExpr) (pinsOf : List KExpr → List KExpr)
    (rhsA : KExpr) : Prop :=
  ∃ lfvs lrest pdoms1 tyRest cdomsL crestL pdoms2 crestEnd,
    openLamsAtFvars (rP + cnF) rhsA 0 = some (lfvs, lrest) ∧
    Expr.instPisAt (lfvs.take rP) tyA = some (pdoms1, tyRest) ∧
    Expr.instPisAt (pinsOf (lfvs.take rP)) ctyInst = some (cdomsL, crestL) ∧
    Expr.instPisAt (lfvs.drop rP) crestL = some (pdoms2, crestEnd) ∧
    DefEqListJ J envSelf (rP + cnF) (lfvs.map Expr.fvarTypeD) (pdoms1 ++ pdoms2)

/-! ## `peel_n_foralls`, `build_param_lvls_range`, `peel_n_lams_collect`, `apply_spine` -/

theorem peel_n_foralls_exact (m : Nat) :
    ∀ {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat} {E : KExpr}
      {e r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = m →
      ObsFn W "KernelCheck::peel_n_foralls" [e, .field n] h r h' cs →
      TmExact κ 0 Γ h k E e →
      ∃ bs rem, E.stripPis m = some (bs, rem) ∧ TmExact κ 0 Γ h (k + m) rem r ∧ h' = h := by
  induction m with
  | zero =>
    intro κ Γ k E e r n h h' cs hm ev hE
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with ⟨_, rfl, rfl, _⟩ |
      ⟨_, _, _, _, _, hne, _, _, _, _⟩
    · exact ⟨[], E, rfl, by simpa using hE, rfl⟩
    · have hn : n ≠ 0 := fun e => hne (by rw [e])
      have := Lib.val_sub_one hn; omega
  | succ m ih =>
    intro κ Γ k E e r n h h' cs hm ev hE
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with ⟨hv, _, _, _⟩ |
      ⟨_, x_body, _, _, _, hne, ld, op, ev_rec, _⟩
    · injection hv with hn; subst hn; simp at hm
    · have hn : n ≠ 0 := fun e => hne (by rw [e])
      obtain rfl := Lib.sub_one_inv op
      have hpred := Lib.val_sub_one hn
      obtain ⟨T, B, ℓ, rfl, _, hb, _⟩ := hE.forallE_of_load ld
      obtain ⟨bs, rem, hbs, hrem, rfl⟩ := ih (n := n - 1) (by omega) ev_rec hb
      rw [show k + 1 + m = k + (m + 1) by omega] at hrem
      exact ⟨(T, bmeta ℓ) :: bs, rem, by simp [Expr.stripPis, hbs], hrem, rfl⟩

theorem peel_n_foralls_tm (m : Nat) :
    ∀ {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat} {E : KExpr}
      {e r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = m →
      ObsFn W "KernelCheck::peel_n_foralls" [e, .field n] h r h' cs →
      Tm κ 0 Γ h k E e →
      ∃ bs rem, E.stripPis m = some (bs, rem) ∧ Tm κ 0 Γ h (k + m) rem r ∧ h' = h := by
  induction m with
  | zero =>
    intro κ Γ k E e r n h h' cs hm ev hE
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with ⟨_, rfl, rfl, _⟩ |
      ⟨_, _, _, _, _, hne, _, _, _, _⟩
    · exact ⟨[], E, rfl, by simpa using hE, rfl⟩
    · have hn : n ≠ 0 := fun e => hne (by rw [e])
      have := Lib.val_sub_one hn; omega
  | succ m ih =>
    intro κ Γ k E e r n h h' cs hm ev hE
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with ⟨hv, _, _, _⟩ |
      ⟨_, x_body, _, _, _, hne, ld, op, ev_rec, _⟩
    · injection hv with hn; subst hn; simp at hm
    · have hn : n ≠ 0 := fun e => hne (by rw [e])
      obtain rfl := Lib.sub_one_inv op
      have hpred := Lib.val_sub_one hn
      obtain ⟨T, B, ℓ, rfl, _, hb, _⟩ := hE.forallE_of_load ld
      obtain ⟨bs, rem, hbs, hrem, rfl⟩ := ih (n := n - 1) (by omega) ev_rec hb
      rw [show k + 1 + m = k + (m + 1) by omega] at hrem
      exact ⟨(T, bmeta ℓ) :: bs, rem, by simp [Expr.stripPis, hbs], hrem, rfl⟩

theorem peel_n_foralls_inst_exact {xs : List KExpr} :
    ∀ {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {e r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = xs.length →
      (∀ m (hm : m < xs.length), .fvar (d + m) (Γ (d + m)) = xs[m]) →
      ObsFn W "KernelCheck::peel_n_foralls" [e, .field n] h r h' cs →
      TmExact κ d Γ h 0 E e →
      ∃ doms rem, Expr.instPisAt xs E = some (doms, rem) ∧
        TmExact κ (d + xs.length) Γ h 0 rem r ∧ h' = h := by
  induction xs with
  | nil =>
    intro κ d Γ E e r n h h' cs hm _ ev hE
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with ⟨_, rfl, rfl, _⟩ |
      ⟨_, _, _, _, _, hne, _, _, _, _⟩
    · exact ⟨[], E, rfl, by simpa using hE, rfl⟩
    · simp only [List.length_nil] at hm
      have hn : n ≠ 0 := fun (e : n = 0) => hne (by rw [e])
      have := Lib.val_sub_one hn; omega
  | cons x xs ih =>
    intro κ d Γ E e r n h h' cs hm hxs ev hE
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with ⟨hv, _, _, _⟩ |
      ⟨_, x_body, _, _, _, hne, ld, op, ev_rec, _⟩
    · injection hv with hn; subst hn; simp at hm
    · have hn : n ≠ 0 := fun (e : n = 0) => hne (by rw [e])
      obtain rfl := Lib.sub_one_inv op
      have hpred := Lib.val_sub_one hn
      obtain ⟨T, B, _, rfl, _, hb, _⟩ := hE.forallE_of_load ld
      have hb_open : TmExact κ (d + 1) Γ h 0 (B.instantiate1 x) x_body := by
        have h0 := hxs 0 (by simp)
        simp only [Nat.add_zero, List.getElem_cons_zero] at h0
        rw [← h0]
        exact hb.open_body (Γ' := Γ) rfl (fun _ _ => rfl)
      obtain ⟨ds, rem, hds, hrem, rfl⟩ := ih (d := d + 1) (n := n - 1)
        (by simp at hm; omega)
        (fun m hm' => by
          have h1 := hxs (m + 1) (by simp; omega)
          simp only [List.getElem_cons_succ] at h1
          simpa [Nat.add_assoc, Nat.add_comm 1 m] using h1)
        ev_rec hb_open
      rw [show d + 1 + xs.length = d + (x :: xs).length by simp; omega] at hrem
      exact ⟨T :: ds, rem, by simp [Expr.instPisAt, hds], hrem, rfl⟩

private theorem build_param_lvls_range_go (rem : Nat) :
    ∀ {start count idx : F} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val count = ZMod.val idx + rem →
      ZMod.val start + ZMod.val count < 4294967296 →
      ObsFn W "KernelCheck::build_param_lvls_range" [.field start, .field count, .field idx]
        h r h' cs →
      RepKLevelList h' ((List.range rem).map fun k => .param (ZMod.val start + ZMod.val idx + k)) r := by
  induction rem with
  | zero =>
    intro start count idx r h h' cs hrem _ ev
    rcases Obs.«KernelCheck::build_param_lvls_range».obs ev with ⟨_, rfl, rfl, _⟩ |
      ⟨v1, _, _, _, _, _, _, op17, hne, _, _, _, _, _, _, _⟩
    · obtain ⟨repN, _⟩ := RepKLevelList.allocNil h
      rw [IxVM.Refinement.Levels.klevelList_names] at repN
      simpa using repN
    · rw [SubstAux.sub_ok op17] at hne
      have hv : ZMod.val (count - idx) = 0 := by rw [SubstAux.val_sub (by omega)]; omega
      have hcz : count - idx = 0 := ZMod.val_injective _ (by simpa using hv)
      exact absurd (congrArg Value.field hcz) hne
  | succ rem ih =>
    intro start count idx r h h' cs hrem hlt ev
    rcases Obs.«KernelCheck::build_param_lvls_range».obs ev with ⟨op17, _, _, _⟩ |
      ⟨_, v46, m48, v60, m78, _, v91, op17, _, rfl, rfl, rfl, op74, op119, ev_rec, _⟩
    · have hsub := SubstAux.sub_ok op17
      injection hsub with h0
      have hv : ZMod.val (count - idx) = rem + 1 := by rw [SubstAux.val_sub (by omega)]; omega
      rw [← h0, ZMod.val_zero] at hv; omega
    · rw [SubstAux.add_ok op74] at ev_rec
      rw [SubstAux.add_ok op119] at ev_rec
      have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
      have hval1 : ZMod.val (1 : F) = 1 := rfl
      have hsi_val : ZMod.val (start + idx) = ZMod.val start + ZMod.val idx :=
        SubstAux.val_add (by omega)
      have hsi_cast : ((ZMod.val start + ZMod.val idx : Nat) : F) = start + idx := by
        rw [← hsi_val, ZMod.natCast_zmod_val]
      have hparam : RepKLevel (h ++ [.construct klevelEnum "Param" [.field (start + idx)]])
          (.param (ZMod.val start + ZMod.val idx)) (.ptr (.enum klevelEnum) h.length) :=
        .param (by omega) (by rw [hsi_cast]; simp)
      have hi1 : ZMod.val (idx + 1) = ZMod.val idx + 1 := SubstAux.val_add (by omega)
      have htail := ih (start := start) (count := count) (idx := idx + 1)
        (by omega) hlt ev_rec
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      have htail_eq :
          ((List.range rem).map ((fun k => Level.param (ZMod.val start + ZMod.val idx + k)) ∘ (· + 1))) =
            (List.range rem).map (fun k => .param (ZMod.val start + ZMod.val (idx + 1) + k)) := by
        apply List.map_congr_left
        intro k _
        exact congrArg (fun n : Nat => Level.param n)
          (show (ZMod.val start + ZMod.val idx + (k + 1) : Nat) =
              ZMod.val start + ZMod.val (idx + 1) + k by
            rw [hi1]; omega)
      rw [Nat.add_zero, htail_eq]
      obtain ⟨repC, _⟩ := RepKLevelList.allocCons (hparam.mono ev_rec.heap_extends) htail
      rw [IxVM.Refinement.Levels.klevelList_names] at repC
      exact repC

theorem build_param_lvls_range_spec {nl : F} {r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hnl : ZMod.val nl < 4294967296)
    (ev : ObsFn W "KernelCheck::build_param_lvls_range" [.field 0, .field nl, .field 0] h r h' cs) :
    RepKLevelList h' ((List.range (ZMod.val nl)).map Level.param) r := by
  simpa [ZMod.val_zero] using
    build_param_lvls_range_go (ZMod.val nl) (start := 0) (count := nl) (idx := 0)
      (by simp) (by simpa using hnl) ev

private theorem subst_go_getElem_tele :
    ∀ (ks : List LevelParam) (vs : List KLevel) (i : Nat) (hnd : ks.Nodup)
      (hlen : vs.length = ks.length) (hi : i < ks.length),
      Level.subst.go ks vs ks[i] = vs[i]'(hlen ▸ hi)
  | [], _, _, _, _, hi => nomatch hi
  | _ :: _, [], _, _, hlen, _ => nomatch hlen
  | k :: ks, v :: vs, 0, _, _, _ => by
    show (if k = k then v else Level.subst.go ks vs k) = v
    exact ite_eq_left rfl
  | k :: ks, v :: vs, i + 1, hnd, hlen, hi => by
    obtain ⟨hk_not_mem, hnd'⟩ := List.nodup_cons.mp hnd
    have hi' : i < ks.length := Nat.lt_of_succ_lt_succ hi
    have hlen' : vs.length = ks.length := Nat.succ.inj hlen
    have hne : k ≠ ks[i] := fun heq => hk_not_mem (heq ▸ List.getElem_mem hi')
    show (if k = ks[i] then v else Level.subst.go ks vs ks[i]) = vs[i]'(hlen' ▸ hi')
    rw [ite_eq_right hne]
    exact subst_go_getElem_tele ks vs i hnd' hlen' hi'

theorem posOf_const_self_levels (ps : List LevelParam) (name : KKey) (hnodup : ps.Nodup) :
    posOf ps (.const name (ps.map Level.param)) =
      .const name ((List.range ps.length).map Level.param) := by
  unfold posOf posLevels
  simp only [Expr.instantiateLevelParams, List.map_map]
  congr 1
  have hlen : ((List.range ps.length).map Level.param).length = ps.length := by simp
  apply List.ext_getElem (by simp)
  intro idx hi₁ hi₂
  simp only [List.length_map, List.length_range] at hi₁ hi₂
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, Level.subst]
  simpa using subst_go_getElem_tele ps ((List.range ps.length).map Level.param) idx hnodup hlen hi₁

theorem stripLams_instantiate1_isSome (v : KExpr) :
    ∀ (m : Nat) (e : KExpr) (c : Nat),
      (e.stripLams m).isSome = true → ((e.instantiate1 v c).stripLams m).isSome = true
  | 0, _, _, _ => rfl
  | m + 1, .lam _ body _, c, h => by
    simp only [Expr.instantiate1, Expr.stripLams, Option.isSome_map] at h ⊢
    exact stripLams_instantiate1_isSome v m body (c + 1) h
  | _ + 1, .bvar _, _, h | _ + 1, .fvar _ _, _, h | _ + 1, .sort _, _, h
  | _ + 1, .const _ _, _, h | _ + 1, .app _ _, _, h | _ + 1, .forallE _ _ _, _, h
  | _ + 1, .letE _ _ _ _, _, h | _ + 1, .lit _, _, h | _ + 1, .proj _ _ _, _, h =>
    nomatch h

theorem instLamsAt_of_stripLams :
    ∀ (xs : List KExpr) (e : KExpr),
      (e.stripLams xs.length).isSome = true →
      ∃ ds rem, Expr.instLamsAt xs e = some (ds, rem)
  | [], e, _ => ⟨[], e, rfl⟩
  | a :: as, .lam dom body _, h => by
    simp only [List.length_cons, Expr.stripLams, Option.isSome_map] at h
    obtain ⟨ds, rem, hrem⟩ :=
      instLamsAt_of_stripLams as (body.instantiate1 a) (stripLams_instantiate1_isSome a as.length body 0 h)
    exact ⟨dom :: ds, rem, by simp [Expr.instLamsAt, hrem]⟩
  | _ :: _, .bvar _, h | _ :: _, .fvar _ _, h | _ :: _, .sort _, h | _ :: _, .const _ _, h
  | _ :: _, .app _ _, h | _ :: _, .forallE _ _ _, h | _ :: _, .letE _ _ _ _, h
  | _ :: _, .lit _, h | _ :: _, .proj _ _ _, h =>
    nomatch h

theorem openLamsAtFvars_of_stripLams :
    ∀ (m : Nat) (e : KExpr) (i : Nat),
      (e.stripLams m).isSome = true →
      ∃ fvs rem, openLamsAtFvars m e i = some (fvs, rem)
  | 0, e, _, _ => ⟨[], e, rfl⟩
  | m + 1, .lam dom body _, i, h => by
    simp only [Expr.stripLams, Option.isSome_map] at h
    obtain ⟨fvs, rem, hrem⟩ :=
      openLamsAtFvars_of_stripLams m (body.instantiate1 (.fvar i dom)) (i + 1)
        (stripLams_instantiate1_isSome (.fvar i dom) m body 0 h)
    exact ⟨.fvar i dom :: fvs, rem, by simp [openLamsAtFvars, hrem]⟩
  | _ + 1, .bvar _, _, h | _ + 1, .fvar _ _, _, h | _ + 1, .sort _, _, h
  | _ + 1, .const _ _, _, h | _ + 1, .app _ _, _, h | _ + 1, .forallE _ _ _, _, h
  | _ + 1, .letE _ _ _ _, _, h | _ + 1, .lit _, _, h | _ + 1, .proj _ _ _, _, h =>
    nomatch h

private theorem peel_n_lams_collect_go (rem : Nat) :
    ∀ {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat} {E : KExpr}
      {e acc r_e r_acc : SourceValue F} {n peeled d_out : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = rem →
      ZMod.val peeled + rem < 4294967296 →
      ZMod.val d_out = ZMod.val peeled + rem →
      ObsFn W "KernelCheck::peel_n_lams_collect" [e, .field n, .field peeled, acc]
        h (.tuple [r_e, .field d_out, r_acc]) h' cs →
      TmExact κ 0 Γ h k E e →
      (E.stripLams rem).isSome = true := by
  induction rem with
  | zero =>
    intro κ Γ k E e acc r_e r_acc n peeled d_out h h' cs _ _ _ _ _
    rfl
  | succ rem ih =>
    intro κ Γ k E e acc r_e r_acc n peeled d_out h h' cs hn hlt hd ev hE
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    have hval1 : ZMod.val (1 : F) = 1 := rfl
    rcases Obs.«KernelCheck::peel_n_lams_collect».obs ev with ⟨hv, _, _, _⟩ |
      ⟨x_dom, x_body, _, _, _, _, m131, hne, ld, op_sub, op_add, rfl, ev_rec, _⟩ |
      ⟨_, hne, _, _, he_tup, _, _⟩
    · injection hv with h0; subst h0; simp at hn
    · obtain rfl := Lib.sub_one_inv op_sub
      have hpred := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e]))
      rw [SubstAux.add_ok op_add] at ev_rec
      have hp1 : ZMod.val (peeled + 1) = ZMod.val peeled + 1 := SubstAux.val_add (by omega)
      obtain ⟨T, B, ℓ, rfl, _, hb, _⟩ := hE.lam_of_load ld
      have ext := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [x_dom, acc])
      have hstrip := ih (n := n - 1) (peeled := peeled + 1) (d_out := d_out)
        (by omega) (by omega) (by omega) ev_rec (hb.mono ext)
      simp [Expr.stripLams, hstrip]
    · injection he_tup with h1; injection h1 with _ h2; injection h2 with h2 _
      injection h2 with hpeel; subst hpeel; omega

theorem peel_n_lams_collect_spec {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {e acc r_e r_acc : SourceValue F} {d : F} {h h' : Heap F} {cs : List (Call F)} {E : KExpr}
    (hd : ZMod.val d < 4294967296)
    (ev : ObsFn W "KernelCheck::peel_n_lams_collect" [e, .field d, .field 0, acc]
      h (.tuple [r_e, .field d, r_acc]) h' cs)
    (hE : TmExact κ 0 Γ h 0 E e) :
    (E.stripLams (ZMod.val d)).isSome = true ∧
      ∀ i, ∃ fvs rem, openLamsAtFvars (ZMod.val d) E i = some (fvs, rem) := by
  have hs := peel_n_lams_collect_go (ZMod.val d) rfl (by simpa using hd) (by simp) ev hE
  exact ⟨hs, fun i => openLamsAtFvars_of_stripLams (ZMod.val d) E i hs⟩

theorem mkAppN_getAppFn_getAppArgs : ∀ (e : KExpr), e = Expr.mkAppN e.getAppFn e.getAppArgs
  | .app f a => by
    have ih := mkAppN_getAppFn_getAppArgs f
    have hfn : (Expr.app f a).getAppFn = f.getAppFn := rfl
    have hargs : (Expr.app f a).getAppArgs = f.getAppArgs ++ [a] :=
      getAppArgs_mkAppN [a] f
    rw [hfn, hargs, SubstAux.mkAppN_snoc, ← ih]
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

theorem instantiate1_mkAppN (v : KExpr) (c : Nat) :
    ∀ (args : List KExpr) (f : KExpr),
      (Expr.mkAppN f args).instantiate1 v c =
        Expr.mkAppN (f.instantiate1 v c) (args.map (·.instantiate1 v c))
  | [], _ => rfl
  | a :: args, f => by
    show (Expr.mkAppN (.app f a) args).instantiate1 v c =
      Expr.mkAppN (.app (f.instantiate1 v c) (a.instantiate1 v c)) (args.map (·.instantiate1 v c))
    exact instantiate1_mkAppN v c args (.app f a)

/-- When `e.stripPis m` ends in an application headed by `.const cname clvls` of arity `L`,
`e.instantiate1 v c` preserves that exact `(m, cname, clvls, L)` telescope shape. -/
theorem stripPis_constHead_instantiate1 (v : KExpr) (cname : KKey) (clvls : List KLevel) (L : Nat) :
    ∀ (m : Nat) (e : KExpr) (c : Nat) {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      e.stripPis m = some (bs, rem) →
      rem.getAppFn = .const cname clvls →
      rem.getAppArgs.length = L →
      ∃ bs' rem', (e.instantiate1 v c).stripPis m = some (bs', rem') ∧
        rem'.getAppFn = .const cname clvls ∧
        rem'.getAppArgs.length = L
  | 0, e, c, _, _, hs, hfn, hlen => by
    injection hs with hp; injection hp with _ h2; subst h2
    refine ⟨[], e.instantiate1 v c, rfl, ?_, ?_⟩
    · conv_lhs => rw [mkAppN_getAppFn_getAppArgs e]
      rw [hfn, instantiate1_mkAppN, getAppFn_mkAppN]; rfl
    · conv_lhs => rw [mkAppN_getAppFn_getAppArgs e]
      rw [hfn, instantiate1_mkAppN, getAppArgs_mkAppN]
      simp [Expr.getAppArgs, hlen]
  | m + 1, .forallE dom body bm, c, _, _, hs, hfn, hlen => by
    simp only [Expr.stripPis] at hs
    cases hsb : body.stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with _ h2; subst h2
      obtain ⟨bs', rem', hbs', hfn', hlen'⟩ :=
        stripPis_constHead_instantiate1 v cname clvls L m body (c + 1) hsb hfn hlen
      exact ⟨(dom.instantiate1 v c, bm) :: bs', rem',
        by simp [Expr.instantiate1, Expr.stripPis, hbs'], hfn', hlen'⟩
  | _ + 1, .bvar _, _, _, _, hs, _, _ | _ + 1, .fvar _ _, _, _, _, hs, _, _
  | _ + 1, .sort _, _, _, _, hs, _, _ | _ + 1, .const _ _, _, _, _, hs, _, _
  | _ + 1, .app _ _, _, _, _, hs, _, _ | _ + 1, .lam _ _ _, _, _, _, hs, _, _
  | _ + 1, .letE _ _ _ _, _, _, _, hs, _, _ | _ + 1, .lit _, _, _, _, hs, _, _
  | _ + 1, .proj _ _ _, _, _, _, hs, _, _ => nomatch hs

theorem instPisAt_constHead (cname : KKey) (clvls : List KLevel) (L : Nat) :
    ∀ (xs : List KExpr) (m : Nat) (e : KExpr)
      {bs : List (KExpr × Ix.Kernel.BinderMeta)} {cbody : KExpr},
      e.stripPis (xs.length + m) = some (bs, cbody) →
      cbody.getAppFn = .const cname clvls →
      cbody.getAppArgs.length = L →
      ∃ ds rem bs' cbody', Expr.instPisAt xs e = some (ds, rem) ∧
        rem.stripPis m = some (bs', cbody') ∧
        cbody'.getAppFn = .const cname clvls ∧
        cbody'.getAppArgs.length = L
  | [], m, e, bs, cbody, hs, hfn, hlen =>
    ⟨[], e, bs, cbody, rfl, by simpa using hs, hfn, hlen⟩
  | a :: as, m, .forallE dom body bm, _, cbody, hs, hfn, hlen => by
    rw [show (a :: as).length + m = as.length + m + 1 by simp; omega] at hs
    simp only [Expr.stripPis] at hs
    cases hsb : body.stripPis (as.length + m) with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with _ h2; subst h2
      obtain ⟨bs1, cbody1, hbs1, hfn1, hlen1⟩ :=
        stripPis_constHead_instantiate1 a cname clvls L (as.length + m) body 0 hsb hfn hlen
      obtain ⟨ds, rem, bs', cbody', hinst, hrem, hfn', hlen'⟩ :=
        instPisAt_constHead cname clvls L as m (body.instantiate1 a) hbs1 hfn1 hlen1
      exact ⟨dom :: ds, rem, bs', cbody', by simp [Expr.instPisAt, hinst], hrem, hfn', hlen'⟩
  | a :: as, m, .bvar _, _, _, hs, _, _ | a :: as, m, .fvar _ _, _, _, hs, _, _
  | a :: as, m, .sort _, _, _, hs, _, _ | a :: as, m, .const _ _, _, _, hs, _, _
  | a :: as, m, .app _ _, _, _, hs, _, _ | a :: as, m, .lam _ _ _, _, _, hs, _, _
  | a :: as, m, .letE _ _ _ _, _, _, hs, _, _ | a :: as, m, .lit _, _, _, hs, _, _
  | a :: as, m, .proj _ _ _, _, _, hs, _, _ => by
    rw [show (a :: as).length + m = (as.length + m) + 1 by simp; omega] at hs; nomatch hs

theorem openPisAtFvars_constHead (cname : KKey) (clvls : List KLevel) (L : Nat) :
    ∀ (m : Nat) (e : KExpr) (i : Nat)
      {bs : List (KExpr × Ix.Kernel.BinderMeta)} {cbody : KExpr},
      e.stripPis m = some (bs, cbody) →
      cbody.getAppFn = .const cname clvls →
      cbody.getAppArgs.length = L →
      ∃ fvs rem, Ix.Kernel.openPisAtFvars m e i = some (fvs, rem) ∧
        rem.getAppFn = .const cname clvls ∧
        rem.getAppArgs.length = L
  | 0, e, _, _, cbody, hs, hfn, hlen => by
    injection hs with hp; injection hp with _ h2; subst h2
    exact ⟨[], e, rfl, hfn, hlen⟩
  | m + 1, .forallE dom body bm, i, _, cbody, hs, hfn, hlen => by
    simp only [Expr.stripPis] at hs
    cases hsb : body.stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with _ h2; subst h2
      obtain ⟨bs1, cbody1, hbs1, hfn1, hlen1⟩ :=
        stripPis_constHead_instantiate1 (.fvar i dom) cname clvls L m body 0 hsb hfn hlen
      obtain ⟨fvs, rem, hop, hfn', hlen'⟩ :=
        openPisAtFvars_constHead cname clvls L m (body.instantiate1 (.fvar i dom)) (i + 1)
          hbs1 hfn1 hlen1
      exact ⟨.fvar i dom :: fvs, rem, by simp [Ix.Kernel.openPisAtFvars, hop], hfn', hlen'⟩
  | _ + 1, .bvar _, _, _, _, hs, _, _ | _ + 1, .fvar _ _, _, _, _, hs, _, _
  | _ + 1, .sort _, _, _, _, hs, _, _ | _ + 1, .const _ _, _, _, _, hs, _, _
  | _ + 1, .app _ _, _, _, _, hs, _, _ | _ + 1, .lam _ _ _, _, _, _, hs, _, _
  | _ + 1, .letE _ _ _ _, _, _, _, hs, _, _ | _ + 1, .lit _, _, _, _, hs, _, _
  | _ + 1, .proj _ _ _, _, _, _, hs, _, _ => nomatch hs

theorem apply_spine_exact {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {As : List KExpr} :
    ∀ {H : KExpr} {head spine r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelWhnf::apply_spine" [head, spine] h r h' cs →
      TmExact κ d Γ h k H head →
      RepList kexprListEnum (fun h A p => TmExact κ d Γ h k A p) h As spine →
      TmExact κ d Γ h' k (Expr.mkAppN H As) r := by
  induction As with
  | nil =>
    intro H head spine r h h' cs ev hH hAs
    match Obs.«KernelWhnf::apply_spine».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. => subst hr hh; exact hH
    | .Cons (ld12 := ld) .. => obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hAs ld; cases he
  | cons A As ih =>
    intro H head spine r h h' cs ev hH hAs
    match Obs.«KernelWhnf::apply_spine».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hAs ld
    | .Cons (x_a := xa) (x_rest := xrest) (m50 := m50) (ld12 := ld) (hm58 := hm)
        (ev46 := ev_rec) .. =>
      subst hm
      obtain ⟨A', As', he, hA, hAs'⟩ := Lib.rep_cons_of_load hAs ld
      injection he with h1 h2; subst h1 h2
      have ext := Heap.Extends.snoc h (.construct kexprEnum "App" [head, xa])
      exact ih ev_rec (tmExact_store_app hH hA)
        (RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext hAs')

theorem apply_spine_tm {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {As : List KExpr} :
    ∀ {H : KExpr} {head spine r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelWhnf::apply_spine" [head, spine] h r h' cs →
      Tm κ d Γ h k H head →
      RepList kexprListEnum (fun h A p => Tm κ d Γ h k A p) h As spine →
      Tm κ d Γ h' k (Expr.mkAppN H As) r := by
  induction As with
  | nil =>
    intro H head spine r h h' cs ev hH hAs
    match Obs.«KernelWhnf::apply_spine».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. => subst hr hh; exact hH
    | .Cons (ld12 := ld) .. => obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hAs ld; cases he
  | cons A As ih =>
    intro H head spine r h h' cs ev hH hAs
    match Obs.«KernelWhnf::apply_spine».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hAs ld
    | .Cons (x_a := xa) (x_rest := xrest) (m50 := m50) (ld12 := ld) (hm58 := hm)
        (ev46 := ev_rec) .. =>
      subst hm
      obtain ⟨A', As', he, hA, hAs'⟩ := Lib.rep_cons_of_load hAs ld
      injection he with h1 h2; subst h1 h2
      have ext := Heap.Extends.snoc h (.construct kexprEnum "App" [head, xa])
      exact ih ev_rec (Tm.store_app hH hA)
        (RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext hAs')

/-! ## Raw `Rules` list judgements and `posOf` lifting to `posRulesJ` -/

def RawDefEqList (env : Ix.Kernel.Env .anon) (d : Nat) : List KExpr → List KExpr → Prop
  | [], [] => True
  | a :: as, b :: bs => DefEq env d a b ∧ RawDefEqList env d as bs
  | _, _ => False

def RawTypedList (env : Ix.Kernel.Env .anon) (d : Nat) : List KExpr → List KExpr → Prop
  | [], [] => True
  | a :: as, b :: bs =>
    (∃ ty, Infer env .full d a ty ∧ DefEq env d ty b) ∧ RawTypedList env d as bs
  | _, _ => False

theorem rawDefEqList_append {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ {xs₁ ys₁ xs₂ ys₂ : List KExpr},
      RawDefEqList env d xs₁ ys₁ → RawDefEqList env d xs₂ ys₂ →
      RawDefEqList env d (xs₁ ++ xs₂) (ys₁ ++ ys₂)
  | [], [], _, _, _, h₂ => h₂
  | _ :: _, _ :: _, _, _, ⟨h0, h₁⟩, h₂ => ⟨h0, rawDefEqList_append h₁ h₂⟩
  | [], _ :: _, _, _, h₁, _ | _ :: _, [], _, _, h₁, _ => nomatch h₁

theorem rawDefEqList_to_posRulesJ {ps : List LevelParam}
    (hperm : ps.Perm (List.range ps.length)) {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ {as bs : List KExpr},
      RawDefEqList env d (as.map (posOf ps)) (bs.map (posOf ps)) →
      DefEqListJ posRulesJ env d as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h0, hrest⟩ =>
    ⟨posRulesJ_defeq_of_pos hperm h0, rawDefEqList_to_posRulesJ hperm hrest⟩
  | [], _ :: _, h | _ :: _, [], h => nomatch h

theorem rawTypedList_to_posRulesJ {ps : List LevelParam}
    (hperm : ps.Perm (List.range ps.length)) {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ {as bs : List KExpr},
      RawTypedList env d (as.map (posOf ps)) (bs.map (posOf ps)) →
      TypedListJ posRulesJ env d as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨⟨ty_pos, hinf, hde⟩, hrest⟩ => by
    refine ⟨⟨invPosOf ps ty_pos, ?_, ?_⟩, rawTypedList_to_posRulesJ hperm hrest⟩
    · exact posRulesJ_infer_of_pos hperm hinf
    · exact posRulesJ_defeq_of_pos hperm (by rwa [posOf_invPosOf hperm])
  | [], _ :: _, h | _ :: _, [], h => nomatch h

/-! ## `defeq_list_ok`, `assert_index_vars`, `lower_pins`, and `rec_major_pins` -/

theorem defeq_list_ok_spec (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    {Γ : Nat → KExpr} {d : Nat} {Xs : List KExpr} :
    ∀ {Ys : List KExpr} {rc xs_ptr ys_ptr types : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      EnvFacts c → LoadFacts c → Good c cs →
      ObsFn W "KernelModeled::defeq_list_ok" [rc, xs_ptr, ys_ptr, types] h (.field 1) h' cs →
      RepList kexprListEnum (fun h X p => Tm c.κ d Γ h 0 X p) h Xs xs_ptr →
      RepList kexprListEnum (fun h Y p => Tm c.κ d Γ h 0 Y p) h Ys ys_ptr →
      RawDefEqList c.env d Xs Ys := by
  induction Xs with
  | nil =>
    intro Ys rc xs_ptr ys_ptr types h h' cs _ _ _ _ _ _ ev hxs hys
    match Obs.«KernelModeled::defeq_list_ok».obs ev with
    | .Nil_Nil (ld31 := ld_y) .. =>
      obtain rfl := Lib.rep_nil_of_load hys ld_y
      trivial
    | .Nil_other (he46 := hr) .. => injection hr with hf; exact absurd hf one_ne_zero
    | .Cons_Nil (ld12 := ld_x) .. | .Cons_Cons_n1 (ld12 := ld_x) ..
    | .Cons_Cons_other (ld12 := ld_x) .. =>
      obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hxs ld_x; cases he
  | cons X Xs ih =>
    intro Ys rc xs_ptr ys_ptr types h h' cs hrc hty hsc hef hlf hgood ev hxs hys
    match Obs.«KernelModeled::defeq_list_ok».obs ev with
    | .Nil_Nil (ld12 := ld_x) .. | .Nil_other (ld12 := ld_x) .. =>
      cases Lib.rep_nil_of_load hxs ld_x
    | .Cons_Nil (he85 := hr) .. | .Cons_Cons_other (he199 := hr) .. =>
      injection hr with hf; exact absurd hf one_ne_zero
    | .Cons_Cons_n1 (ld12 := ld_x) (ld77 := ld_y) (ev119 := ev_de) (ev161 := ev_rec)
        (hc194 := hc) .. =>
      subst hc
      obtain ⟨X', Xs', hx_eq, hX, hXs⟩ := Lib.rep_cons_of_load hxs ld_x
      obtain ⟨Y', Ys', hy_eq, hY, hYs⟩ := Lib.rep_cons_of_load hys ld_y
      injection hx_eq with h1 h2; subst h1 h2
      subst hy_eq
      have hde := core_defeq hCore hrc hty hsc hef hlf
        (hgood.sub tele_sub_calls) ev_de hX hY
      have ext := ev_de.heap_extends
      refine ⟨hde, ih (hrc.mono ext) (hty.mono ext) hsc hef hlf
        (hgood.sub fun _ hx => by simp [hx]) ev_rec
        (RepLinkedList.mono tmE_heapMono₂ ext hXs)
        (RepLinkedList.mono tmE_heapMono₂ ext hYs)⟩

private theorem assert_index_vars_go (rem : Nat) :
    ∀ {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat} {As : List KExpr}
      {args_ptr r : SourceValue F} {ni idx : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val ni = ZMod.val idx + rem →
      ZMod.val ni < 4294967296 →
      As.length = rem →
      ObsFn W "KernelModeled::assert_index_vars" [args_ptr, .field ni, .field idx] h r h' cs →
      RepList kexprListEnum (fun h E p => TmExact κ 0 Γ h k E p) h As args_ptr →
      As = ((List.range rem).map fun m => .bvar (ZMod.val ni - 1 - (ZMod.val idx + m))) ∧ h' = h := by
  induction rem with
  | zero =>
    intro κ Γ k As args_ptr r ni idx h h' cs hrem _ hlen ev _
    match Obs.«KernelModeled::assert_index_vars».obs ev with
    | .n0 (he27 := hh) .. =>
      exact ⟨List.eq_nil_of_length_eq_zero hlen, hh⟩
    | .other (op17 := op17) (hne29 := hne) .. =>
      rw [SubstAux.sub_ok op17] at hne
      have hv : ZMod.val (ni - idx) = 0 := by rw [SubstAux.val_sub (by omega)]; omega
      have hcz : ni - idx = 0 := ZMod.val_injective _ (by simpa using hv)
      exact absurd (congrArg Value.field hcz) hne
  | succ rem ih =>
    intro κ Γ k As args_ptr r ni idx h h' cs hrem hni hlen ev hAs
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    have hval1 : ZMod.val (1 : F) = 1 := rfl
    match Obs.«KernelModeled::assert_index_vars».obs ev with
    | .n0 (op17 := op17) .. =>
      have hsub := SubstAux.sub_ok op17
      injection hsub with h0
      have hv : ZMod.val (ni - idx) = rem + 1 := by rw [SubstAux.val_sub (by omega)]; omega
      rw [← h0, ZMod.val_zero] at hv; omega
    | .other (ld43 := ld_cons) (ld69 := ld_bv) (op123 := op_ni1) (op115 := op_sub)
        (heq126 := heq_j) (op163 := op_inc) (ev132 := ev_rec) .. =>
      obtain ⟨A, As', hcons_eq, hA, hAs'⟩ := Lib.rep_cons_of_load hAs ld_cons
      subst hcons_eq
      obtain ⟨j, hj_eq, _, hbc⟩ := hA.bvar_of_load ld_bv
      subst hj_eq
      rw [SubstAux.sub_ok op_ni1] at op_sub
      rw [SubstAux.sub_ok op_sub] at heq_j
      injection heq_j with hj_val
      rw [SubstAux.add_ok op_inc] at ev_rec
      have hni1 : ZMod.val (ni - 1) = ZMod.val ni - 1 := SubstAux.val_sub (by omega)
      have hj_nat : ZMod.val j = ZMod.val ni - 1 - ZMod.val idx := by
        rw [hj_val, SubstAux.val_sub (by omega), hni1]
      have hA_eq : A = .bvar (ZMod.val ni - 1 - ZMod.val idx) := by
        rcases hbc with ⟨_, rfl⟩ | ⟨_, hd, _⟩
        · rw [hj_nat]
        · exact nomatch hd
      have hi1 : ZMod.val (idx + 1) = ZMod.val idx + 1 := SubstAux.val_add (by omega)
      obtain ⟨htail, hh⟩ := ih (ni := ni) (idx := idx + 1)
        (by omega) hni (by simp at hlen; omega) ev_rec hAs'
      refine ⟨?_, hh⟩
      rw [hA_eq, htail, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero, List.cons.injEq, true_and]
      apply List.map_congr_left
      intro m _; simp only [Function.comp_apply, hi1]; congr 1; omega

theorem assert_index_vars_spec {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat}
    {As : List KExpr} {args_ptr r : SourceValue F} {ni : F} {h h' : Heap F} {cs : List (Call F)}
    (hni : ZMod.val ni < 4294967296) (hlen : As.length = ZMod.val ni)
    (ev : ObsFn W "KernelModeled::assert_index_vars" [args_ptr, .field ni, .field 0] h r h' cs)
    (hAs : RepList kexprListEnum (fun h E p => TmExact κ 0 Γ h k E p) h As args_ptr) :
    As = ((List.range (ZMod.val ni)).map fun m => .bvar (ZMod.val ni - 1 - m)) ∧ h' = h := by
  simpa [ZMod.val_zero] using assert_index_vars_go (ZMod.val ni) (ni := ni) (idx := 0)
    (by simp) hni hlen ev hAs

theorem lower_pins_spec {κ : _root_.Address → KKey} {rp : Nat} {Γ : Nat → KExpr} {Ps : List KExpr} :
    ∀ {ps_ptr r : SourceValue F} {ni : F} {h h' : Heap F} {cs : List (Call F)},
      IxVM.Consistency.Bounded cs →
      ZMod.val ni < 288230376151711744 →
      ObsFn W "KernelModeled::lower_pins" [ps_ptr, .field ni] h r h' cs →
      RepList kexprListEnum (fun h E p => TmExact κ 0 Γ h (rp + ZMod.val ni) E p) h Ps ps_ptr →
      (∀ P ∈ Ps, noLooseIn 0 (ZMod.val ni) P = true) ∧
        RepList kexprListEnum (fun h E p => TmExact κ 0 Γ h rp E p) h'
          (Ps.map (Expr.lowerBVars (ZMod.val ni) 0)) r := by
  induction Ps with
  | nil =>
    intro ps_ptr r ni h h' cs _ _ ev hps
    match Obs.«KernelModeled::lower_pins».obs ev with
    | .Nil (he24 := hr) (hm23 := hh) .. =>
      subst hr hh
      exact ⟨fun _ hm => (nomatch hm), RepLinkedList.nil (by simp)⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hps ld; cases he
  | cons P Ps ih =>
    intro ps_ptr r ni h h' cs bd hni ev hps
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    match Obs.«KernelModeled::lower_pins».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hps ld
    | .Cons (ld12 := ld) (ev70 := ev_hb) (heq100 := hv0) (he105 := hr) (hm104 := hh)
        (ev122 := ev_low) (ev157 := ev_rec) (hc174 := hc) .. =>
      subst hc hr hh
      obtain ⟨P', Ps', he, hP, hPs⟩ := Lib.rep_cons_of_load hps ld
      injection he with h1 h2; subst h1 h2
      obtain ⟨rfl, -, hnoF⟩ := SubstAux.gall κ .has_bvar_in_range _ _ _ _ _ ev_hb
        _ _ _ rfl (bounded_sub tele_sub_calls bd)
      have hnf := hnoF hv0 0 Γ (rp + ZMod.val ni) P hP.toTm
      simp only [ZMod.val_zero] at hnf
      have hnidx := SubstAux.noIdx_of_noIdxF_tm hP.toTm (by omega) hnf
      have hnoP : noLooseIn 0 (ZMod.val ni) P = true := by
        simpa using noLooseIn_of_noIdx_tmExact (c := 0) (m := 0) (ni := ZMod.val ni) hP
          (SubstAux.idxAll_mono hnidx fun n i h1 => by simpa using h1)
      have hP_low := expr_lower_local_exact (rp := rp)
        (bounded_sub (fun _ hx => by simp [hx]) bd) ev_low hP hnidx
      obtain ⟨hnoPs, hPs_low⟩ := ih
        (bounded_sub (fun _ hx => by simp [hx]) bd) hni ev_rec
        (RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ev_low.heap_extends hPs)
      refine ⟨fun Q hQ => ?_,
        Lib.rep_store_cons (fun _ _ _ _ e x => x.mono e) (hP_low.mono ev_rec.heap_extends) hPs_low⟩
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact hnoP
      · exact hnoPs Q hQ

theorem rec_major_pins_spec {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {E : KExpr}
    {ty_ptr r : SourceValue F} {rp ni : F} {h h' : Heap F} {cs : List (Call F)}
    (bd : IxVM.Consistency.Bounded cs)
    (hrp : ZMod.val rp < 288230376151711744)
    (hni : ZMod.val ni < 4294967296)
    (ev : ObsFn W "KernelModeled::rec_major_pins" [ty_ptr, .field rp, .field ni] h r h' cs)
    (hE : TmExact κ 0 Γ h 0 E ty_ptr) :
    ∃ iaddr ilvls_ptr pins_ptr a_ind, ∃ (inp : F), ∃ bs dom body m_maj lvls_pos As,
      r = .tuple [iaddr, ilvls_ptr, pins_ptr] ∧
      Bytes.RepAddressRef addrTy h' a_ind iaddr ∧
      RepKLevelList h' lvls_pos ilvls_ptr ∧
      E.stripPis (ZMod.val rp + ZMod.val ni) = some (bs, .forallE dom body m_maj) ∧
      dom.getAppFn = .const (κ (ixAddr a_ind)) lvls_pos ∧
      dom.getAppArgs = As ∧
      ZMod.val inp ≤ As.length ∧
      (As.length : F) = inp + ni ∧
      As.drop (ZMod.val inp) =
        ((List.range (ZMod.val ni)).map fun m => .bvar (ZMod.val ni - 1 - m)) ∧
      (∀ P ∈ As.take (ZMod.val inp), noLooseIn 0 (ZMod.val ni) P = true) ∧
      RepList kexprListEnum (fun h P p => TmExact κ 0 Γ h (ZMod.val rp) P p) h'
        ((As.take (ZMod.val inp)).map (Expr.lowerBVars (ZMod.val ni) 0)) pins_ptr ∧
      As.length = ZMod.val inp + ZMod.val ni ∧
      (∃ p149 m77 m141 cs155 w172 w173 w174 w175 w176 w177,
        Heap.Extends h m77 ∧ Heap.Extends m141 h' ∧
        ObsFn W "Ingress::get_ci" [iaddr] m77 p149 m141 cs155 ∧
        loadValue m141 p149 = .ok (.construct kciEnum "Induct"
          [w172, w173, .field inp, .field ni, w174, w175, w176, w177])) := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  match Obs.«KernelModeled::rec_major_pins».obs ev with
  | .run (x_args := x_args) (x_iaddr := iaddr) (x_ilvls := ilvls_ptr) (m141 := m141)
      (x_inp := x_inp) (v358 := pins_ptr)
      (op37 := op_mi) (ev14 := ev_peel) (ld51 := ld_fa) (ev89 := ev_sp) (ld122 := ld_c)
      (ev157 := ev_ci) (ld151 := ld_ind) (heq245 := heq_ini) (ev270 := ev_len)
      (op292 := op_add_inp) (heq295 := heq_len) (ev324 := ev_drop) (ev309 := ev_idx)
      (he359 := hr) (ev399 := ev_take) (ev385 := ev_low) (he423 := hh) (hc424 := hc) .. =>
    subst hc hr hh heq_ini
    rw [SubstAux.add_ok op_mi] at ev_peel
    have hmi_val : ZMod.val (rp + ni) = ZMod.val rp + ZMod.val ni := SubstAux.val_add (by omega)
    obtain ⟨bs, rem, hstrip, hrem, rfl⟩ :=
      peel_n_foralls_exact (ZMod.val rp + ZMod.val ni) hmi_val ev_peel hE
    rw [Nat.zero_add] at hrem
    obtain ⟨dom, body, ℓ_maj, rfl, hdom, _, _⟩ := hrem.forallE_of_load ld_fa
    obtain ⟨hd, sp, H, As, htup, hH, hAs, hdom_eq⟩ := collect_spine_exact ev_sp hdom
    injection htup with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    obtain ⟨a_ind, lvls_pos, rfl, ra_ind, rlvls⟩ := hH.const_of_load ld_c
    have hfn_dom : dom.getAppFn = .const (κ (ixAddr a_ind)) lvls_pos := by
      rw [hdom_eq, getAppFn_mkAppN]; rfl
    have hargs_dom : dom.getAppArgs = As := by
      rw [hdom_eq, getAppArgs_mkAppN]; rfl
    cases x_inp with
    | field inp =>
      rw [SubstAux.add_ok op_add_inp] at heq_len
      have ext_ci := ev_ci.heap_extends
      have hAs1 := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_ci hAs
      have hAs_lt : As.length < 2 ^ 39 :=
        IxVM.Refinement.RomBound.bounded_length_lt bd
          (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_args], m141⟩)
          (by simp) (by simp) hAs1
      obtain ⟨hv257, rfl⟩ := tele_klength ev_len hAs1
      rw [hv257] at heq_len
      injection heq_len with hlen_f
      obtain ⟨hinp_le, hdrop, rfl⟩ := tele_kdrop ev_drop hAs1
      have hAs_len : As.length = ZMod.val inp + ZMod.val ni := by
        have hv := congrArg ZMod.val hlen_f
        rw [SubstAux.val_natCast (by omega), SubstAux.val_add (by omega)] at hv
        exact hv
      obtain ⟨hdrop_eq, rfl⟩ :=
        assert_index_vars_spec hni (by simp [hAs_len]) ev_idx hdrop
      obtain ⟨_, htake⟩ := tele_ktake (fun _ _ _ _ e x => x.mono e) ev_take hAs1
      obtain ⟨hno_take, hpins⟩ := lower_pins_spec (rp := ZMod.val rp)
        (bounded_sub (fun _ hx => by simp [hx]) bd) (by omega) ev_low htake
      have ext_tail := ev_take.heap_extends.trans ev_low.heap_extends
      have ext_sp_end := ext_ci.trans ext_tail
      exact ⟨iaddr, ilvls_ptr, pins_ptr, a_ind, inp, bs, dom, body, bmeta ℓ_maj, lvls_pos, As,
        rfl,
        Bytes.repAddressRef_heapMono₂ addrTy ext_sp_end ra_ind,
        rlvls.mono ext_sp_end,
        hstrip, hfn_dom, hargs_dom, hinp_le, hlen_f, hdrop_eq, hno_take, hpins, hAs_len,
        ⟨_, _, _, _, _, _, _, _, _, _, ev_sp.heap_extends, ext_tail, ev_ci, ld_ind⟩⟩
    | tuple _ | ptr _ _ | construct _ _ _ => cases op_add_inp

/-! ## `peel_collect`, `bvars_desc`, `lift_list`, `inst_params`, `inst_params_typed`, `defeq_tele`, `defeq_lam_tele` -/

theorem typesRep_snoc_extend {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F}
    {d : Nat} {T : KExpr} {tp ctx : SourceValue F}
    (ht : TypesRep κ Γ h d ctx) (hT : Tm κ d Γ h 0 T tp) :
    TypesRep κ (Ghost.extend Γ d T) (h ++ [.construct kexprListEnum "Cons" [tp, ctx]]) (d + 1)
      (.ptr (.enum kexprListEnum) h.length) := by
  have ext := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [tp, ctx])
  have ht' : TypesRep κ (Ghost.extend Γ d T) (h ++ [.construct kexprListEnum "Cons" [tp, ctx]])
      d ctx :=
    typesRep_congr_ghost (fun j hj => Ghost.extend_below Γ d T j hj) (ht.mono ext)
  have hT' : Tm κ d (Ghost.extend Γ d T) (h ++ [.construct kexprListEnum "Cons" [tp, ctx]])
      0 (Ghost.extend Γ d T d) tp :=
    (Ghost.extend_at Γ d T).symm ▸ Tm.congr_ghost (Ghost.extend_below Γ d T) (hT.mono ext)
  exact .cons (by simp) hT' ht'

theorem peel_collect_open_exact (m : Nat) :
    ∀ {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {e ctx r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = m →
      ObsFn W "KernelModeled::peel_collect" [e, .field n, ctx] h r h' cs →
      TmExact κ d Γ h 0 E e →
      TypesRep κ Γ h d ctx →
      GhostScoped Γ d →
      ∃ r_e r_ctx Γ' fvs rem,
        r = .tuple [r_e, r_ctx] ∧
        Ix.Kernel.openPisAtFvars m E d = some (fvs, rem) ∧
        (∀ j < d, Γ' j = Γ j) ∧
        (∀ k (hk : k < fvs.length), Γ' (d + k) = fvs[k].fvarTypeD) ∧
        TmExact κ (d + m) Γ' h' 0 rem r_e ∧
        TypesRep κ Γ' h' (d + m) r_ctx ∧
        GhostScoped Γ' (d + m) := by
  induction m with
  | zero =>
    intro κ d Γ E e ctx r n h h' cs hm ev hE hty hsc
    match Obs.«KernelModeled::peel_collect».obs ev with
    | .n0 (he19 := hr) (he34 := hh) .. =>
      subst hr hh
      exact ⟨e, ctx, Γ, [], E, rfl, rfl, fun _ _ => rfl,
        fun _ hk => absurd hk (Nat.not_lt_zero _),
        by simpa using hE, by simpa using hty, by simpa using hsc⟩
    | .other (hne36 := hne) .. =>
      have := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e])); omega
  | succ m ih =>
    intro κ d Γ E e ctx r n h h' cs hm ev hE hty hsc
    match Obs.«KernelModeled::peel_collect».obs ev with
    | .n0 (hv14 := hv) .. => injection hv with hn; subst hn; simp at hm
    | .other (x_d := xd) (x_b := xb) (m107 := m107) (hne36 := hne) (ld51 := ld)
        (op104 := op_sub) (hm115 := hm107) (ev80 := ev_rec) .. =>
      subst hm107
      obtain rfl := Lib.sub_one_inv op_sub
      have hpred := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e]))
      obtain ⟨T, B, _, rfl, hT, hb, _⟩ := hE.forallE_of_load ld
      let Γ₁ := Ghost.extend Γ d T
      have ext := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [xd, ctx])
      have hb_open : TmExact κ (d + 1) Γ₁
          (h ++ [.construct kexprListEnum "Cons" [xd, ctx]]) 0
          (B.instantiate1 (.fvar d T)) xb :=
        (hb.mono ext).open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)
      have hty₁ := typesRep_snoc_extend hty hT.toTm
      have hsc₁ := hsc.extend (Tm.wscopedB hsc hT.toTm)
      obtain ⟨r_e, r_ctx, Γ', fvs, rem, hr_eq, hop, hΓ_lo, hΓ_hi, hrem, hty', hsc'⟩ :=
        ih (d := d + 1) (n := n - 1) (by omega) ev_rec hb_open hty₁ hsc₁
      rw [show d + 1 + m = d + (m + 1) by omega] at hrem hty' hsc'
      refine ⟨r_e, r_ctx, Γ', .fvar d T :: fvs, rem, hr_eq,
        by simp [Ix.Kernel.openPisAtFvars, hop],
        fun j hj => (hΓ_lo j (by omega)).trans (Ghost.extend_below Γ d T j hj),
        ?_, hrem, hty', hsc'⟩
      intro k hk
      cases k with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero, Expr.fvarTypeD]
        exact (hΓ_lo d (by omega)).trans (Ghost.extend_at Γ d T)
      | succ k' =>
        have hk' : k' < fvs.length := by simp at hk; omega
        simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hΓ_hi k' hk'

theorem peel_collect_inst_tm {xs : List KExpr} :
    ∀ {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {e ctx r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = xs.length →
      (∀ k (hk : k < xs.length), .fvar (d + k) (Γ (d + k)) = xs[k]) →
      ObsFn W "KernelModeled::peel_collect" [e, .field n, ctx] h r h' cs →
      Tm κ d Γ h 0 E e →
      ∃ r_e r_ctx doms rem,
        r = .tuple [r_e, r_ctx] ∧
        Expr.instPisAt xs E = some (doms, rem) ∧
        Tm κ (d + xs.length) Γ h' 0 rem r_e := by
  induction xs with
  | nil =>
    intro κ d Γ E e ctx r n h h' cs hm _ ev hE
    match Obs.«KernelModeled::peel_collect».obs ev with
    | .n0 (he19 := hr) (he34 := hh) .. =>
      subst hr hh
      exact ⟨e, ctx, [], E, rfl, rfl, by simpa using hE⟩
    | .other (hne36 := hne) .. =>
      simp only [List.length_nil] at hm
      have := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e])); omega
  | cons x xs ih =>
    intro κ d Γ E e ctx r n h h' cs hm hxs ev hE
    match Obs.«KernelModeled::peel_collect».obs ev with
    | .n0 (hv14 := hv) .. => injection hv with hn; subst hn; simp at hm
    | .other (x_d := xd) (x_b := xb) (hne36 := hne) (ld51 := ld) (op104 := op_sub)
        (hm115 := hm107) (ev80 := ev_rec) .. =>
      subst hm107
      obtain rfl := Lib.sub_one_inv op_sub
      have hpred := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e]))
      obtain ⟨T, B, _, rfl, _, hb, _⟩ := hE.forallE_of_load ld
      have ext := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [xd, ctx])
      have hb_open : Tm κ (d + 1) Γ (h ++ [.construct kexprListEnum "Cons" [xd, ctx]]) 0
          (B.instantiate1 x) xb := by
        have h0 := hxs 0 (by simp)
        simp only [Nat.add_zero, List.getElem_cons_zero] at h0
        rw [← h0]
        exact (hb.mono ext).open_body (Γ' := Γ) rfl (fun _ _ => rfl)
      obtain ⟨r_e, r_ctx, ds, rem, hr_eq, hds, hrem⟩ := ih (d := d + 1) (n := n - 1)
        (by simp at hm; omega)
        (fun k hk' => by
          have h1 := hxs (k + 1) (by simp; omega)
          simp only [List.getElem_cons_succ] at h1
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using h1)
        ev_rec hb_open
      rw [show d + 1 + xs.length = d + (x :: xs).length by simp; omega] at hrem
      exact ⟨r_e, r_ctx, T :: ds, rem, hr_eq, by simp [Expr.instPisAt, hds], hrem⟩

private theorem bvars_desc_go (rem : Nat) :
    ∀ {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
      {top cnt : F} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val cnt = rem →
      rem ≤ ZMod.val top →
      ZMod.val top ≤ d →
      d < 4294967296 →
      ObsFn W "KernelModeled::bvars_desc" [.field top, .field cnt] h r h' cs →
      RepList kexprListEnum (fun h E p => TmExact κ d Γ h 0 E p) h'
        ((List.range rem).map fun m => .fvar (d - ZMod.val top + m) (Γ (d - ZMod.val top + m))) r := by
  induction rem with
  | zero =>
    intro κ d Γ top cnt r h h' cs hrem _ _ _ ev
    match Obs.«KernelModeled::bvars_desc».obs ev with
    | .n0 (he19 := hr) (hm18 := hh) .. =>
      subst hr hh; exact .nil (by simp)
    | .other (hne24 := hne) .. =>
      have := Lib.val_sub_one (fun (e : cnt = 0) => hne (by rw [e])); omega
  | succ rem ih =>
    intro κ d Γ top cnt r h h' cs hrem hle_top htop_d hd_lt ev
    match Obs.«KernelModeled::bvars_desc».obs ev with
    | .n0 (hv14 := hv) .. => injection hv with h0; subst h0; simp at hrem
    | .other (v37 := v_tail) (m39 := m39) (m68 := m68) (hne24 := hne)
        (he32 := hr) (hm31 := hh) (hm47 := hm39) (op65 := op_t1) (op94 := op_t2)
        (op109 := op_c1) (ev78 := ev_rec) .. =>
      subst hr hh hm39
      obtain rfl := Lib.sub_one_inv op_t1
      obtain rfl := Lib.sub_one_inv op_t2
      obtain rfl := Lib.sub_one_inv op_c1
      have hcnt1 := Lib.val_sub_one (fun (e : cnt = 0) => hne (by rw [e]))
      have htop_ne : top ≠ 0 := by intro e; subst e; simp at hle_top
      have htop1 := Lib.val_sub_one htop_ne
      have hhead : TmExact κ d Γ (h ++ [.construct kexprEnum "BVar" [.field (top - 1)]]) 0
          (.fvar (d - ZMod.val top) (Γ (d - ZMod.val top)))
          (.ptr (.enum kexprEnum) h.length) :=
        tmExact_store_bvarFree_eq (by omega) (by omega) (by omega) (by unfold fvIdx; omega)
      have htail := ih (κ := κ) (Γ := Γ) (top := top - 1) (cnt := cnt - 1)
        (by omega) (by omega) (by omega) hd_lt ev_rec
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
      have htail_eq :
          ((List.range rem).map
            ((fun m => Expr.fvar (d - ZMod.val top + m) (Γ (d - ZMod.val top + m))) ∘ (· + 1))) =
          (List.range rem).map
            (fun m => .fvar (d - ZMod.val (top - 1) + m) (Γ (d - ZMod.val (top - 1) + m))) := by
        apply List.map_congr_left
        intro m _; simp only [Function.comp_apply]
        have heq_idx : d - ZMod.val top + (m + 1) = d - ZMod.val (top - 1) + m := by omega
        rw [heq_idx]
      rw [htail_eq]
      exact Lib.rep_store_cons (fun _ _ _ _ e x => x.mono e) (hhead.mono ev_rec.heap_extends) htail

theorem bvars_desc_exact {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {top cnt : F} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hle_top : ZMod.val cnt ≤ ZMod.val top) (htop_d : ZMod.val top ≤ d) (hd_lt : d < 4294967296)
    (ev : ObsFn W "KernelModeled::bvars_desc" [.field top, .field cnt] h r h' cs) :
    RepList kexprListEnum (fun h E p => TmExact κ d Γ h 0 E p) h'
      ((List.range (ZMod.val cnt)).map fun m =>
        .fvar (d - ZMod.val top + m) (Γ (d - ZMod.val top + m))) r :=
  bvars_desc_go (ZMod.val cnt) rfl hle_top htop_d hd_lt ev

theorem lift_list_exact {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {Es : List KExpr} :
    ∀ {es_ptr r : SourceValue F} {shift : F} {h h' : Heap F} {cs : List (Call F)},
      IxVM.Consistency.Bounded cs →
      ZMod.val shift < 4611686018427387904 →
      ObsFn W "KernelModeled::lift_list" [es_ptr, .field shift] h r h' cs →
      RepList kexprListEnum (fun h E p => TmExact κ d Γ h 0 E p) h Es es_ptr →
      RepList kexprListEnum (fun h E p => TmExact κ (d + ZMod.val shift) Γ h 0 E p) h' Es r := by
  induction Es with
  | nil =>
    intro es_ptr r shift h h' cs _ _ ev hes
    match Obs.«KernelModeled::lift_list».obs ev with
    | .Nil (he24 := hr) (hm23 := hh) .. => subst hr hh; exact .nil (by simp)
    | .Cons (ld12 := ld) .. => obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hes ld; cases he
  | cons E Es ih =>
    intro es_ptr r shift h h' cs bd hs ev hes
    match Obs.«KernelModeled::lift_list».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hes ld
    | .Cons (ld12 := ld) (he50 := hr) (hm49 := hh) (ev67 := ev_lift) (ev102 := ev_rec)
        (hc119 := hc) .. =>
      subst hc hr hh
      obtain ⟨E', Es', he, hE, hEs⟩ := Lib.rep_cons_of_load hes ld
      injection he with h1 h2; subst h1 h2
      have hE' := expr_lift_open_exact (bounded_sub tele_sub_calls bd) hs ev_lift hE
      have hEs' := ih (bounded_sub (fun _ hx => by simp [hx]) bd) hs ev_rec
        (RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ev_lift.heap_extends hEs)
      exact Lib.rep_store_cons (fun _ _ _ _ e x => x.mono e) (hE'.mono ev_rec.heap_extends) hEs'

theorem inst_params_tm {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {Ps : List KExpr} :
    ∀ {E : KExpr} {e ps_ptr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      IxVM.Consistency.Bounded cs →
      ObsFn W "KernelModeled::inst_params" [e, ps_ptr] h r h' cs →
      Tm κ d Γ h 0 E e →
      RepList kexprListEnum (fun h P p => Tm κ d Γ h 0 P p) h Ps ps_ptr →
      ∃ doms rem, Expr.instPisAt Ps E = some (doms, rem) ∧ Tm κ d Γ h' 0 rem r := by
  induction Ps with
  | nil =>
    intro E e ps_ptr r h h' cs _ ev hE hps
    match Obs.«KernelModeled::inst_params».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. => subst hr hh; exact ⟨[], E, rfl, hE⟩
    | .Cons (ld12 := ld) .. => obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hps ld; cases he
  | cons P Ps ih =>
    intro E e ps_ptr r h h' cs bd ev hE hps
    match Obs.«KernelModeled::inst_params».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hps ld
    | .Cons (ld12 := ld) (ld52 := ld_fa) (ev96 := ev_inst) (ev82 := ev_rec) (hc127 := hc) .. =>
      subst hc
      obtain ⟨P', Ps', he, hP, hPs⟩ := Lib.rep_cons_of_load hps ld
      injection he with h1 h2; subst h1 h2
      obtain ⟨T, B, _, rfl, _, hb, _⟩ := hE.forallE_of_load ld_fa
      have hinst := SubstAux.gall κ .expr_inst1 _ _ _ _ _ ev_inst _ _ _ rfl
        (bounded_sub tele_sub_calls bd) d Γ B P
        (by simpa [ZMod.val_zero] using hb) hP
      simp only [ZMod.val_zero] at hinst
      obtain ⟨ds, rem, hds, hrem⟩ := ih (bounded_sub (fun _ hx => by simp [hx]) bd)
        ev_rec hinst (RepLinkedList.mono tmE_heapMono₂ ev_inst.heap_extends hPs)
      exact ⟨T :: ds, rem, by simp [Expr.instPisAt, hds], hrem⟩

theorem inst_params_typed_spec (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    (hsc_env : Ix.Kernel.StoreClosed c.env)
    {Γ₁ Γ₂ : Nat → KExpr} {d₁ d₂ depth : Nat} (hle : d₁ ≤ depth) {Ps₁ : List KExpr} :
    ∀ {Ps₂ : List KExpr} {E₁ E₂ : KExpr} {rc e ps_ptr ctx r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ₁ h d₁ ctx →
      GhostScoped Γ₁ d₁ →
      EnvFacts c → LoadFacts c → Good c cs →
      ObsFn W "KernelModeled::inst_params_typed" [rc, e, ps_ptr, ctx] h r h' cs →
      Tm c.κ d₁ Γ₁ h 0 E₁ e →
      Tm c.κ d₂ Γ₂ h 0 E₂ e →
      RepList kexprListEnum (fun h P p => Tm c.κ d₁ Γ₁ h 0 P p) h Ps₁ ps_ptr →
      RepList kexprListEnum (fun h P p => Tm c.κ d₂ Γ₂ h 0 P p) h Ps₂ ps_ptr →
      ∃ doms₁ rem₁ doms₂ rem₂,
        Expr.instPisAt Ps₁ E₁ = some (doms₁, rem₁) ∧
        Expr.instPisAt Ps₂ E₂ = some (doms₂, rem₂) ∧
        Tm c.κ d₁ Γ₁ h' 0 rem₁ r ∧
        Tm c.κ d₂ Γ₂ h' 0 rem₂ r ∧
        RawTypedList c.env depth Ps₁ doms₁ := by
  induction Ps₁ with
  | nil =>
    intro Ps₂ E₁ E₂ rc e ps_ptr ctx r h h' cs _ _ _ _ _ _ ev hE₁ hE₂ hps₁ hps₂
    match Obs.«KernelModeled::inst_params_typed».obs ev with
    | .Nil (ld12 := ld) (he21 := hr) (he22 := hh) .. =>
      subst hr hh
      obtain rfl := Lib.rep_nil_of_load hps₂ ld
      exact ⟨[], E₁, [], E₂, rfl, rfl, hE₁, hE₂, trivial⟩
    | .Cons (ld12 := ld) .. => obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hps₁ ld; cases he
  | cons P₁ Ps₁ ih =>
    intro Ps₂ E₁ E₂ rc e ps_ptr ctx r h h' cs hrc hty hsc hef hlf hgood ev hE₁ hE₂ hps₁ hps₂
    match Obs.«KernelModeled::inst_params_typed».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hps₁ ld
    | .Cons (ld12 := ld) (ld52 := ld_fa) (ev89 := ev_inf) (ev138 := ev_de)
        (heq177 := hv1) (ev206 := ev_inst) (ev183 := ev_rec) (hc244 := hc) .. =>
      subst hc hv1
      obtain ⟨P₁', Ps₁', he₁, hP₁, hPs₁⟩ := Lib.rep_cons_of_load hps₁ ld
      obtain ⟨P₂, Ps₂', he₂, hP₂, hPs₂⟩ := Lib.rep_cons_of_load hps₂ ld
      injection he₁ with h1 h2; subst h1 h2
      subst he₂
      obtain ⟨T₁, B₁, _, rfl, hT₁, hb₁, _⟩ := hE₁.forallE_of_load ld_fa
      obtain ⟨T₂, B₂, _, rfl, _, hb₂, _⟩ := hE₂.forallE_of_load ld_fa
      obtain ⟨tt, htt, hinf⟩ := core_infer hCore hrc hty hsc hef hlf
        (hgood.sub tele_sub_calls) ev_inf hP₁
      have e_inf := ev_inf.heap_extends
      have hde := core_defeq hCore (hrc.mono e_inf) (hty.mono e_inf) hsc hef hlf
        (hgood.sub fun _ hx => by simp [hx]) ev_de htt (hT₁.mono e_inf)
      have hinf_d := infer_lift_to hsc_env hle hsc hP₁ htt hinf
      have hde_d := defEq_lift_to hsc_env hle hsc htt (hT₁.mono e_inf) hde
      have e_de := e_inf.trans ev_de.heap_extends
      have hinst₁ := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ ev_inst _ _ _ rfl
        (bounded_sub (fun _ hx => by simp [hx]) hgood.2) d₁ Γ₁ B₁ P₁
        (by simpa [ZMod.val_zero] using hb₁.mono e_de) (hP₁.mono e_de)
      have hinst₂ := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ ev_inst _ _ _ rfl
        (bounded_sub (fun _ hx => by simp [hx]) hgood.2) d₂ Γ₂ B₂ P₂
        (by simpa [ZMod.val_zero] using hb₂.mono e_de) (hP₂.mono e_de)
      simp only [ZMod.val_zero] at hinst₁ hinst₂
      have e_all := e_de.trans ev_inst.heap_extends
      obtain ⟨ds₁, rem₁, ds₂, rem₂, hds₁, hds₂, hrem₁, hrem₂, htyped⟩ :=
        ih (hrc.mono e_all) (hty.mono e_all) hsc hef hlf
          (hgood.sub fun _ hx => by simp [hx]) ev_rec hinst₁ hinst₂
          (RepLinkedList.mono tmE_heapMono₂ e_all hPs₁)
          (RepLinkedList.mono tmE_heapMono₂ e_all hPs₂)
      exact ⟨T₁ :: ds₁, rem₁, T₂ :: ds₂, rem₂,
        by simp [Expr.instPisAt, hds₁], by simp [Expr.instPisAt, hds₂],
        hrem₁, hrem₂, ⟨⟨tt, hinf_d, hde_d⟩, htyped⟩⟩

theorem defeq_tele_spec (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    (hsc_env : Ix.Kernel.StoreClosed c.env) (m : Nat) :
    ∀ {Γ : Nat → KExpr} {d depth : Nat} {Ea Eb : KExpr}
      {rc a b ctx r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = m →
      d + m ≤ depth →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d ctx →
      GhostScoped Γ d →
      EnvFacts c → LoadFacts c → Good c cs →
      ObsFn W "KernelModeled::defeq_tele" [rc, a, b, .field n, ctx] h r h' cs →
      TmExact c.κ d Γ h 0 Ea a →
      Tm c.κ d Γ h 0 Eb b →
      ∃ fvs remA domsB remB,
        Ix.Kernel.openPisAtFvars m Ea d = some (fvs, remA) ∧
        Expr.instPisAt fvs Eb = some (domsB, remB) ∧
        RawDefEqList c.env depth (fvs.map Expr.fvarTypeD) domsB := by
  induction m with
  | zero =>
    intro Γ d depth Ea Eb rc a b ctx r n h h' cs hm _ _ _ _ _ _ _ ev _ _
    match Obs.«KernelModeled::defeq_tele».obs ev with
    | .n0 .. => exact ⟨[], Ea, [], Eb, rfl, rfl, trivial⟩
    | .other (hne20 := hne) .. =>
      have := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e])); omega
  | succ m ih =>
    intro Γ d depth Ea Eb rc a b ctx r n h h' cs hm hle hrc hty hsc hef hlf hgood ev hEa hEb
    match Obs.«KernelModeled::defeq_tele».obs ev with
    | .n0 (hv14 := hv) .. => injection hv with hn; subst hn; simp at hm
    | .other (x_da := xda) (x_ba := xba) (x_db := xdb) (x_bb := xbb) (m108 := m108)
        (hne20 := hne) (ld35 := ld_a) (ld70 := ld_b) (ev118 := ev_de) (heq157 := hv1)
        (op203 := op_sub) (hm214 := hm206) (ev163 := ev_rec) (hc234 := hc) .. =>
      subst hc hv1 hm206
      obtain rfl := Lib.sub_one_inv op_sub
      have hpred := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e]))
      obtain ⟨Ta, Ba, _, rfl, hTa, hBa, _⟩ := hEa.forallE_of_load ld_a
      obtain ⟨Tb, Bb, _, rfl, hTb, hBb, _⟩ := hEb.forallE_of_load ld_b
      have hde := core_defeq hCore hrc hty hsc hef hlf
        (hgood.sub tele_sub_calls) ev_de hTa.toTm hTb
      have hde_d := defEq_lift_to (depth := depth) hsc_env (by omega) hsc hTa.toTm hTb hde
      have e_de := ev_de.heap_extends
      have ext_cons := Heap.Extends.snoc m108 (.construct kexprListEnum "Cons" [xda, ctx])
      have e_all := e_de.trans ext_cons
      let Γ₁ := Ghost.extend Γ d Ta
      have hBa_open : TmExact c.κ (d + 1) Γ₁
          (m108 ++ [.construct kexprListEnum "Cons" [xda, ctx]]) 0
          (Ba.instantiate1 (.fvar d Ta)) xba :=
        (hBa.mono e_all).open_body (Ghost.extend_at Γ d Ta) (Ghost.extend_below Γ d Ta)
      have hBb_open : Tm c.κ (d + 1) Γ₁
          (m108 ++ [.construct kexprListEnum "Cons" [xda, ctx]]) 0
          (Bb.instantiate1 (.fvar d Ta)) xbb :=
        (hBb.mono e_all).open_body (Ghost.extend_at Γ d Ta) (Ghost.extend_below Γ d Ta)
      have hty₁ := typesRep_snoc_extend (hty.mono e_de) (hTa.toTm.mono e_de)
      have hsc₁ := hsc.extend (Tm.wscopedB hsc hTa.toTm)
      obtain ⟨fvs, remA, domsB, remB, hop, hinst, hlist⟩ :=
        ih (Γ := Γ₁) (d := d + 1) (depth := depth) (n := n - 1) (by omega) (by omega)
          (hrc.mono e_all) hty₁ hsc₁ hef hlf (hgood.sub fun _ hx => by simp [hx])
          ev_rec hBa_open hBb_open
      exact ⟨.fvar d Ta :: fvs, remA, Tb :: domsB, remB,
        by simp [Ix.Kernel.openPisAtFvars, hop],
        by simp [Expr.instPisAt, hinst],
        ⟨hde_d, hlist⟩⟩

theorem defeq_lam_tele_spec (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    (hsc_env : Ix.Kernel.StoreClosed c.env) (m : Nat) :
    ∀ {Γ : Nat → KExpr} {d depth : Nat} {El Ep : KExpr}
      {rc l p ctx r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = m →
      d + m ≤ depth →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d ctx →
      GhostScoped Γ d →
      EnvFacts c → LoadFacts c → Good c cs →
      ObsFn W "KernelModeled::defeq_lam_tele" [rc, l, p, .field n, ctx] h r h' cs →
      Tm c.κ d Γ h 0 El l →
      Tm c.κ d Γ h 0 Ep p →
      ∃ r_l r_ctx Γ' lfvs remL domsP remP,
        r = .tuple [r_l, r_ctx] ∧
        openLamsAtFvars m El d = some (lfvs, remL) ∧
        Expr.instPisAt lfvs Ep = some (domsP, remP) ∧
        (∀ j < d, Γ' j = Γ j) ∧
        (∀ k (hk : k < lfvs.length), Γ' (d + k) = lfvs[k].fvarTypeD) ∧
        Tm c.κ (d + m) Γ' h' 0 remL r_l ∧
        TypesRep c.κ Γ' h' (d + m) r_ctx ∧
        GhostScoped Γ' (d + m) ∧
        RawDefEqList c.env depth (lfvs.map Expr.fvarTypeD) domsP := by
  induction m with
  | zero =>
    intro Γ d depth El Ep rc l p ctx r n h h' cs hm _ _ hty hsc _ _ _ ev hEl _
    match Obs.«KernelModeled::defeq_lam_tele».obs ev with
    | .n0 (he19 := hr) (he34 := hh) .. =>
      subst hr hh
      exact ⟨l, ctx, Γ, [], El, [], Ep, rfl, rfl, rfl, fun _ _ => rfl,
        fun _ hk => absurd hk (Nat.not_lt_zero _), by simpa using hEl, by simpa using hty,
        by simpa using hsc, trivial⟩
    | .other (hne36 := hne) .. =>
      have := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e])); omega
  | succ m ih =>
    intro Γ d depth El Ep rc l p ctx r n h h' cs hm hle hrc hty hsc hef hlf hgood ev hEl hEp
    match Obs.«KernelModeled::defeq_lam_tele».obs ev with
    | .n0 (hv14 := hv) .. => injection hv with hn; subst hn; simp at hm
    | .other (x_dl := xdl) (x_bl := xbl) (x_dp := xdp) (x_bp := xbp) (m124 := m124)
        (hne36 := hne) (ld51 := ld_l) (ld86 := ld_p) (ev134 := ev_de) (heq173 := hv1)
        (op219 := op_sub) (hm230 := hm222) (ev179 := ev_rec) (hc250 := hc) .. =>
      subst hc hv1 hm222
      obtain rfl := Lib.sub_one_inv op_sub
      have hpred := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e]))
      obtain ⟨Tl, Bl, _, rfl, hTl, hBl, _⟩ := hEl.lam_of_load ld_l
      obtain ⟨Tp, Bp, _, rfl, hTp, hBp, _⟩ := hEp.forallE_of_load ld_p
      have hde := core_defeq hCore hrc hty hsc hef hlf
        (hgood.sub tele_sub_calls) ev_de hTl hTp
      have hde_d := defEq_lift_to (depth := depth) hsc_env (by omega) hsc hTl hTp hde
      have e_de := ev_de.heap_extends
      have ext_cons := Heap.Extends.snoc m124 (.construct kexprListEnum "Cons" [xdl, ctx])
      have e_all := e_de.trans ext_cons
      let Γ₁ := Ghost.extend Γ d Tl
      have hBl_open : Tm c.κ (d + 1) Γ₁
          (m124 ++ [.construct kexprListEnum "Cons" [xdl, ctx]]) 0
          (Bl.instantiate1 (.fvar d Tl)) xbl :=
        (hBl.mono e_all).open_body (Ghost.extend_at Γ d Tl) (Ghost.extend_below Γ d Tl)
      have hBp_open : Tm c.κ (d + 1) Γ₁
          (m124 ++ [.construct kexprListEnum "Cons" [xdl, ctx]]) 0
          (Bp.instantiate1 (.fvar d Tl)) xbp :=
        (hBp.mono e_all).open_body (Ghost.extend_at Γ d Tl) (Ghost.extend_below Γ d Tl)
      have hty₁ := typesRep_snoc_extend (hty.mono e_de) (hTl.mono e_de)
      have hsc₁ := hsc.extend (Tm.wscopedB hsc hTl)
      obtain ⟨r_l, r_ctx, Γ', lfvs, remL, domsP, remP, hr_eq, hop, hinst, hΓ_lo, hΓ_hi,
          hremL, hty', hsc', hlist⟩ :=
        ih (Γ := Γ₁) (d := d + 1) (depth := depth) (n := n - 1) (by omega) (by omega)
          (hrc.mono e_all) hty₁ hsc₁ hef hlf (hgood.sub fun _ hx => by simp [hx])
          ev_rec hBl_open hBp_open
      rw [show d + 1 + m = d + (m + 1) by omega] at hremL hty' hsc'
      refine ⟨r_l, r_ctx, Γ', .fvar d Tl :: lfvs, remL, Tp :: domsP, remP, hr_eq,
        by simp [openLamsAtFvars, hop],
        by simp [Expr.instPisAt, hinst],
        fun j hj => (hΓ_lo j (by omega)).trans (Ghost.extend_below Γ d Tl j hj),
        ?_, hremL, hty', hsc', ⟨hde_d, hlist⟩⟩
      intro k hk
      cases k with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero, Expr.fvarTypeD]
        exact (hΓ_lo d (by omega)).trans (Ghost.extend_at Γ d Tl)
      | succ k' =>
        have hk' : k' < lfvs.length := by simp at hk; omega
        simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hΓ_hi k' hk'

end IxVM.Refinement.Decl
