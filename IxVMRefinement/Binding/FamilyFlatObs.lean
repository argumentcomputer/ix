import IxVMRefinement.Binding.FamilyReconCanon
import IxVMRefinement.Core.SpineChain
import IxVMRefinement.Obs.KernelCheck0
import IxVMRefinement.Obs.KernelCheck1
import IxVMRefinement.Obs.KernelCheck2
import IxVMRefinement.Obs.KernelCheck3
import IxVMRefinement.Obs.KernelCheck4
import IxVMRefinement.Obs.KernelModeled3
import IxVMRefinement.Obs.KernelModeled4
import IxVMRefinement.Obs.KernelModeled6

/-! # Flattened-family observation refinement on `TmOExact`

Refines the flattened-family derivation (`KernelModeled::check_nested_aux`, `nested_walk`,
`ctors_scan`, `occ_scan`, `occ_mentions_block`, `add_block_members`, `aux_all_in`) and the
record-driven flattened-family builder (`KernelCheck::build_flat_block`,
`primary_parent_block_of`, `build_flat_originals`, `detect_aux_from_recrs_ex`,
`rec_to_parent_addr`, `extract_aux_spec_params_from_rec`, `extract_aux_occ_us`) directly on
`TmOExact`, `FlatEntryRepExact`, and `AddrIn (Held R) (Core.keyOf t)` against `FamilyFlat`.

Binder depth in `KernelModeled::occ_scan` is bounded below `2^39` directly from `Bounded cs`
using ROM validity (`shapeOf` / `exprSize_eq_of_represents`): every `Lam`/`Forall` descent
strictly decreases `exprSize` while every valid ROM address determines `shapeOf` (hence
`exprSize`), so the ancestor addresses along any binder chain are pairwise distinct. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
  (FlatEntry IndInfo FlatView indInfoAt ctorTypeAt membersAt keyAddr
   orB peer mentions mentionsList hasBVarIn occParamsLower auxEntryIn addBlockMembers
   scanList constOf nestedAt appCase occScanF exprSize instCtorParams ctorBody
   ctorScan ctorsLoop ctorsScan nestedWalk originals derivedFlatAt
   mutsRoot loadedAt binderDomAfter indcAddrs Held exprInstLevels)
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum kexprListEnum klevelEnum klevelListEnum
  kciEnum addrTy addrListEnum ixAddr bmeta)
open IxVM.Refinement.Decl (TmExact)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM (F)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## `exprSize` inequalities and ROM-address size determinism -/

theorem exprSize_pos (E : KExpr) : 0 < exprSize E := by
  cases E <;> simp [exprSize]

theorem exprSize_getAppFn_le : ∀ E : KExpr, exprSize E.getAppFn ≤ exprSize E
  | .app f a => by
    simp only [Ix.Kernel.Expr.getAppFn, exprSize]
    have h := exprSize_getAppFn_le f
    omega
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ => Nat.le_refl _

theorem exprSize_getAppFn_lt (f a : KExpr) :
    exprSize (Ix.Kernel.Expr.app f a).getAppFn < exprSize (.app f a) := by
  simp only [Ix.Kernel.Expr.getAppFn, exprSize]
  have h := exprSize_getAppFn_le f
  omega

theorem exprSize_getAppArgs_lt : ∀ (E x : KExpr), x ∈ E.getAppArgs → exprSize x < exprSize E
  | .app f a, x, hx => by
    simp only [Ix.Kernel.Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    simp only [exprSize]
    rcases hx with h | rfl
    · have := exprSize_getAppArgs_lt f x h; omega
    · omega
  | .bvar _, _, hx | .fvar _ _, _, hx | .sort _, _, hx | .const _ _, _, hx
  | .lam _ _ _, _, hx | .forallE _ _ _, _, hx | .letE _ _ _ _, _, hx
  | .lit _, _, hx | .proj _ _ _, _, hx => by
    simp [Ix.Kernel.Expr.getAppArgs] at hx

/-- Structural skeleton of a kernel expression, erasing non-structural metadata while preserving
`bvar`, `app`, `lam`, `forallE`, `letE`, and `proj` shape (hence `exprSize`). -/
def shapeOf : KExpr → KExpr
  | .bvar i => .bvar i
  | .app f a => .app (shapeOf f) (shapeOf a)
  | .lam t b _ => .lam (shapeOf t) (shapeOf b) (bmeta .zero)
  | .forallE t b _ => .forallE (shapeOf t) (shapeOf b) (bmeta .zero)
  | .letE t v b m => .letE (shapeOf t) (shapeOf v) (shapeOf b) m
  | .proj _ _ e => .proj (.id default) 0 (shapeOf e)
  | _ => .sort .zero

theorem exprSize_shapeOf : ∀ E : KExpr, exprSize (shapeOf E) = exprSize E
  | .bvar _ => rfl
  | .fvar _ _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f a => by simp [shapeOf, exprSize, exprSize_shapeOf f, exprSize_shapeOf a]
  | .lam t b _ => by simp [shapeOf, exprSize, exprSize_shapeOf t, exprSize_shapeOf b]
  | .forallE t b _ => by simp [shapeOf, exprSize, exprSize_shapeOf t, exprSize_shapeOf b]
  | .letE t v b _ => by
    simp [shapeOf, exprSize, exprSize_shapeOf t, exprSize_shapeOf v, exprSize_shapeOf b]
  | .lit _ => rfl
  | .proj _ _ e => by simp [shapeOf, exprSize, exprSize_shapeOf e]

theorem shapeOf_liftLooseBVars (s : Nat) : ∀ (E : KExpr) (c : Nat),
    shapeOf (E.liftLooseBVars s c) = (shapeOf E).liftLooseBVars s c
  | .bvar i, c => by
    simp only [Ix.Kernel.Expr.liftLooseBVars, shapeOf]
    split <;> rfl
  | .fvar _ _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app f a, c => by
    simp [Ix.Kernel.Expr.liftLooseBVars, shapeOf,
      shapeOf_liftLooseBVars s f c, shapeOf_liftLooseBVars s a c]
  | .lam t b _, c => by
    simp [Ix.Kernel.Expr.liftLooseBVars, shapeOf,
      shapeOf_liftLooseBVars s t c, shapeOf_liftLooseBVars s b (c + 1)]
  | .forallE t b _, c => by
    simp [Ix.Kernel.Expr.liftLooseBVars, shapeOf,
      shapeOf_liftLooseBVars s t c, shapeOf_liftLooseBVars s b (c + 1)]
  | .letE t v b _, c => by
    simp [Ix.Kernel.Expr.liftLooseBVars, shapeOf,
      shapeOf_liftLooseBVars s t c, shapeOf_liftLooseBVars s v c,
      shapeOf_liftLooseBVars s b (c + 1)]
  | .lit _, _ => rfl
  | .proj _ _ e, c => by
    simp [Ix.Kernel.Expr.liftLooseBVars, shapeOf, shapeOf_liftLooseBVars s e c]

theorem shapeOf_instantiate1Lift (V : KExpr) : ∀ (B : KExpr) (d : Nat),
    shapeOf (B.instantiate1Lift V d) = (shapeOf B).instantiate1Lift (shapeOf V) d
  | .bvar i, d => by
    simp only [Ix.Kernel.Expr.instantiate1Lift, shapeOf]
    split
    · exact shapeOf_liftLooseBVars d V 0
    · split <;> rfl
  | .fvar _ _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app f a, d => by
    simp [Ix.Kernel.Expr.instantiate1Lift, shapeOf,
      shapeOf_instantiate1Lift V f d, shapeOf_instantiate1Lift V a d]
  | .lam t b _, d => by
    simp [Ix.Kernel.Expr.instantiate1Lift, shapeOf,
      shapeOf_instantiate1Lift V t d, shapeOf_instantiate1Lift V b (d + 1)]
  | .forallE t b _, d => by
    simp [Ix.Kernel.Expr.instantiate1Lift, shapeOf,
      shapeOf_instantiate1Lift V t d, shapeOf_instantiate1Lift V b (d + 1)]
  | .letE t v b _, d => by
    simp [Ix.Kernel.Expr.instantiate1Lift, shapeOf,
      shapeOf_instantiate1Lift V t d, shapeOf_instantiate1Lift V v d,
      shapeOf_instantiate1Lift V b (d + 1)]
  | .lit _, _ => rfl
  | .proj _ _ e, d => by
    simp [Ix.Kernel.Expr.instantiate1Lift, shapeOf, shapeOf_instantiate1Lift V e d]

private theorem represents_ptr_inv' {rom : ROM F} {h : Heap F} {t : Aiur.Ty} {loc : Nat}
    {w : Value F} (r : Represents rom h (.ptr t loc) w) :
    ∃ stored address encoded, h[loc]? = some stored ∧ (address, encoded) ∈ rom.entries ∧
      Represents rom h stored encoded ∧ w = .ptr encoded.type address := by
  generalize hp : (Value.ptr t loc : SourceValue F) = p at r
  cases r with
  | ptr source cell contents =>
    injection hp with _ hl; subst hl
    exact ⟨_, _, _, source, cell, contents, rfl⟩
  | field => cases hp
  | tuple _ => cases hp
  | construct _ => cases hp

private theorem represents_construct_inv {rom : ROM F} {h : Heap F} {en tag : String}
    {args : List (SourceValue F)} {w : Value F}
    (r : Represents rom h (.construct en tag args) w) :
    ∃ encArgs, w = .construct en tag encArgs ∧ List.Forall₂ (Represents rom h) args encArgs := by
  generalize hv : (Value.construct en tag args : SourceValue F) = v at r
  cases r with
  | construct items =>
    injection hv with h1 h2 h3; subst h1 h2 h3
    exact ⟨_, rfl, items⟩
  | field => cases hv
  | tuple _ => cases hv
  | ptr _ _ _ => cases hv

private theorem represents_field_inv {rom : ROM F} {h : Heap F} {x : F} {w : Value F}
    (r : Represents rom h (.field x) w) : w = .field x := by
  generalize hv : (Value.field x : SourceValue F) = v at r
  cases r with
  | field => injection hv with hx; subst hx; rfl
  | tuple _ => cases hv
  | construct _ => cases hv
  | ptr _ _ _ => cases hv

/-- A pointer represented in a valid ROM uniquely determines `shapeOf E` for any `TmExact κ 0`
term at that pointer. -/
theorem shapeOf_eq_of_represents {rom : ROM F} (hvalid : rom.Valid) {κ : _root_.Address → KKey}
    {h₁ : Heap F} {k₁ : Nat} {E₁ : KExpr} {p₁ : SourceValue F}
    (rep₁ : TmExact κ 0 ghost0 h₁ k₁ E₁ p₁) :
    ∀ {h₂ : Heap F} {k₂ : Nat} {E₂ : KExpr} {p₂ : SourceValue F} {w : Value F},
      Represents rom h₁ p₁ w → Represents rom h₂ p₂ w →
      TmExact κ 0 ghost0 h₂ k₂ E₂ p₂ → shapeOf E₁ = shapeOf E₂ := by
  induction rep₁ with
  | @bvarLocal k₁ addr₁ i₁ cell₁ _ _ =>
    intro h₂ k₂ E₂ p₂ w r₁ r₂ rep₂
    obtain ⟨s₁, a₁, enc₁, hs₁, hmem₁, hrep₁, rfl⟩ := represents_ptr_inv' r₁
    rw [cell₁] at hs₁; cases hs₁
    obtain ⟨ea₁, rfl, hf₁⟩ := represents_construct_inv hrep₁
    cases hf₁ with
    | cons hf11 hfn =>
      cases hfn
      have h11 := represents_field_inv hf11
      subst h11
      cases rep₂ with
      | @bvarLocal _ addr₂ i₂ cell₂ _ _ =>
        obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
        rw [cell₂] at hs₂; cases hs₂
        injection hweq with hty ha; subst ha
        obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
        obtain ⟨ea₂, henc, hf₂⟩ := represents_construct_inv hrep₂
        injection henc with _ _ hea; subst hea
        cases hf₂ with
        | cons hf21 hfn2 =>
          cases hfn2
          have h21 := represents_field_inv hf21
          injection h21 with hi; subst hi; rfl
      | @bvarFree _ _ _ _ _ _ hd => omega
      | @sort _ addr₂ _ _ cell₂ _ | @const _ addr₂ _ _ _ _ _ cell₂ _ _
      | @app _ addr₂ _ _ _ _ cell₂ _ _ | @lam _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
      | @forallE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _ | @letE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
      | @litNat _ addr₂ _ _ cell₂ _ _ | @litStr _ addr₂ _ _ _ cell₂ _ _
      | @proj _ addr₂ _ _ _ _ _ _ _ cell₂ _ _ =>
        obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
        rw [cell₂] at hs₂; cases hs₂
        injection hweq with hty ha; subst ha
        obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
        obtain ⟨_, henc, _⟩ := represents_construct_inv hrep₂
        simp at henc
  | bvarFree _ _ _ hd => omega
  | @sort _ addr₁ _ _ cell₁ _ =>
    intro h₂ k₂ E₂ p₂ w r₁ r₂ rep₂
    obtain ⟨s₁, a₁, enc₁, hs₁, hmem₁, hrep₁, rfl⟩ := represents_ptr_inv' r₁
    rw [cell₁] at hs₁; cases hs₁
    obtain ⟨ea₁, rfl, _⟩ := represents_construct_inv hrep₁
    cases rep₂ with
    | sort _ _ => rfl
    | bvarFree _ _ _ hd => omega
    | @bvarLocal _ addr₂ _ cell₂ _ _ | @const _ addr₂ _ _ _ _ _ cell₂ _ _
    | @app _ addr₂ _ _ _ _ cell₂ _ _ | @lam _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
    | @forallE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _ | @letE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
    | @litNat _ addr₂ _ _ cell₂ _ _ | @litStr _ addr₂ _ _ _ cell₂ _ _
    | @proj _ addr₂ _ _ _ _ _ _ _ cell₂ _ _ =>
      obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
      rw [cell₂] at hs₂; cases hs₂
      injection hweq with hty ha; subst ha
      obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
      obtain ⟨_, henc, _⟩ := represents_construct_inv hrep₂
      simp at henc
  | @const _ addr₁ _ _ _ _ _ cell₁ _ _ =>
    intro h₂ k₂ E₂ p₂ w r₁ r₂ rep₂
    obtain ⟨s₁, a₁, enc₁, hs₁, hmem₁, hrep₁, rfl⟩ := represents_ptr_inv' r₁
    rw [cell₁] at hs₁; cases hs₁
    obtain ⟨ea₁, rfl, _⟩ := represents_construct_inv hrep₁
    cases rep₂ with
    | const _ _ _ => rfl
    | bvarFree _ _ _ hd => omega
    | @bvarLocal _ addr₂ _ cell₂ _ _ | @sort _ addr₂ _ _ cell₂ _
    | @app _ addr₂ _ _ _ _ cell₂ _ _ | @lam _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
    | @forallE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _ | @letE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
    | @litNat _ addr₂ _ _ cell₂ _ _ | @litStr _ addr₂ _ _ _ cell₂ _ _
    | @proj _ addr₂ _ _ _ _ _ _ _ cell₂ _ _ =>
      obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
      rw [cell₂] at hs₂; cases hs₂
      injection hweq with hty ha; subst ha
      obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
      obtain ⟨_, henc, _⟩ := represents_construct_inv hrep₂
      simp at henc
  | @app _ addr₁ fp₁ ap₁ Ef₁ Ea₁ cell₁ rf₁ ra₁ ihf iha =>
    intro h₂ k₂ E₂ p₂ w r₁ r₂ rep₂
    obtain ⟨s₁, a₁, enc₁, hs₁, hmem₁, hrep₁, rfl⟩ := represents_ptr_inv' r₁
    rw [cell₁] at hs₁; cases hs₁
    obtain ⟨ea₁, rfl, hf₁⟩ := represents_construct_inv hrep₁
    cases hf₁ with
    | cons hrf1 hf1' =>
      cases hf1' with
      | cons hra1 hfn =>
        cases hfn
        cases rep₂ with
        | @app _ addr₂ fp₂ ap₂ Ef₂ Ea₂ cell₂ rf₂ ra₂ =>
          obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
          rw [cell₂] at hs₂; cases hs₂
          injection hweq with hty ha; subst ha
          obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
          obtain ⟨ea₂, henc, hf₂⟩ := represents_construct_inv hrep₂
          injection henc with _ _ hea; subst hea
          cases hf₂ with
          | cons hrf2 hf2' =>
            cases hf2' with
            | cons hra2 hfn2 =>
              cases hfn2
              simp [shapeOf, ihf hrf1 hrf2 rf₂, iha hra1 hra2 ra₂]
        | bvarFree _ _ _ hd => omega
        | @bvarLocal _ addr₂ _ cell₂ _ _ | @sort _ addr₂ _ _ cell₂ _
        | @const _ addr₂ _ _ _ _ _ cell₂ _ _ | @lam _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
        | @forallE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _ | @letE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
        | @litNat _ addr₂ _ _ cell₂ _ _ | @litStr _ addr₂ _ _ _ cell₂ _ _
        | @proj _ addr₂ _ _ _ _ _ _ _ cell₂ _ _ =>
          obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
          rw [cell₂] at hs₂; cases hs₂
          injection hweq with hty ha; subst ha
          obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
          obtain ⟨_, henc, _⟩ := represents_construct_inv hrep₂
          simp at henc
  | @lam _ addr₁ tp₁ bp₁ lp₁ T₁ B₁ ℓ₁ cell₁ rt₁ rb₁ _ iht ihb =>
    intro h₂ k₂ E₂ p₂ w r₁ r₂ rep₂
    obtain ⟨s₁, a₁, enc₁, hs₁, hmem₁, hrep₁, rfl⟩ := represents_ptr_inv' r₁
    rw [cell₁] at hs₁; cases hs₁
    obtain ⟨ea₁, rfl, hf₁⟩ := represents_construct_inv hrep₁
    cases hf₁ with
    | cons hrt1 hf1' =>
      cases hf1' with
      | cons hrb1 hf1'' =>
        cases hf1'' with
        | cons _ hfn =>
          cases hfn
          cases rep₂ with
          | @lam _ addr₂ tp₂ bp₂ lp₂ T₂ B₂ ℓ₂ cell₂ rt₂ rb₂ _ =>
            obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
            rw [cell₂] at hs₂; cases hs₂
            injection hweq with hty ha; subst ha
            obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
            obtain ⟨ea₂, henc, hf₂⟩ := represents_construct_inv hrep₂
            injection henc with _ _ hea; subst hea
            cases hf₂ with
            | cons hrt2 hf2' =>
              cases hf2' with
              | cons hrb2 hf2'' =>
                cases hf2'' with
                | cons _ hfn2 =>
                  cases hfn2
                  simp [shapeOf, iht hrt1 hrt2 rt₂, ihb hrb1 hrb2 rb₂]
          | bvarFree _ _ _ hd => omega
          | @bvarLocal _ addr₂ _ cell₂ _ _ | @sort _ addr₂ _ _ cell₂ _
          | @const _ addr₂ _ _ _ _ _ cell₂ _ _ | @app _ addr₂ _ _ _ _ cell₂ _ _
          | @forallE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _ | @letE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
          | @litNat _ addr₂ _ _ cell₂ _ _ | @litStr _ addr₂ _ _ _ cell₂ _ _
          | @proj _ addr₂ _ _ _ _ _ _ _ cell₂ _ _ =>
            obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
            rw [cell₂] at hs₂; cases hs₂
            injection hweq with hty ha; subst ha
            obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
            obtain ⟨_, henc, _⟩ := represents_construct_inv hrep₂
            simp at henc
  | @forallE _ addr₁ tp₁ bp₁ lp₁ T₁ B₁ ℓ₁ cell₁ rt₁ rb₁ _ iht ihb =>
    intro h₂ k₂ E₂ p₂ w r₁ r₂ rep₂
    obtain ⟨s₁, a₁, enc₁, hs₁, hmem₁, hrep₁, rfl⟩ := represents_ptr_inv' r₁
    rw [cell₁] at hs₁; cases hs₁
    obtain ⟨ea₁, rfl, hf₁⟩ := represents_construct_inv hrep₁
    cases hf₁ with
    | cons hrt1 hf1' =>
      cases hf1' with
      | cons hrb1 hf1'' =>
        cases hf1'' with
        | cons _ hfn =>
          cases hfn
          cases rep₂ with
          | @forallE _ addr₂ tp₂ bp₂ lp₂ T₂ B₂ ℓ₂ cell₂ rt₂ rb₂ _ =>
            obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
            rw [cell₂] at hs₂; cases hs₂
            injection hweq with hty ha; subst ha
            obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
            obtain ⟨ea₂, henc, hf₂⟩ := represents_construct_inv hrep₂
            injection henc with _ _ hea; subst hea
            cases hf₂ with
            | cons hrt2 hf2' =>
              cases hf2' with
              | cons hrb2 hf2'' =>
                cases hf2'' with
                | cons _ hfn2 =>
                  cases hfn2
                  simp [shapeOf, iht hrt1 hrt2 rt₂, ihb hrb1 hrb2 rb₂]
          | bvarFree _ _ _ hd => omega
          | @bvarLocal _ addr₂ _ cell₂ _ _ | @sort _ addr₂ _ _ cell₂ _
          | @const _ addr₂ _ _ _ _ _ cell₂ _ _ | @app _ addr₂ _ _ _ _ cell₂ _ _
          | @lam _ addr₂ _ _ _ _ _ _ cell₂ _ _ _ | @letE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
          | @litNat _ addr₂ _ _ cell₂ _ _ | @litStr _ addr₂ _ _ _ cell₂ _ _
          | @proj _ addr₂ _ _ _ _ _ _ _ cell₂ _ _ =>
            obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
            rw [cell₂] at hs₂; cases hs₂
            injection hweq with hty ha; subst ha
            obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
            obtain ⟨_, henc, _⟩ := represents_construct_inv hrep₂
            simp at henc
  | @letE _ addr₁ tp₁ vp₁ bp₁ T₁ V₁ B₁ cell₁ _ rv₁ rb₁ _ ihv ihb =>
    intro h₂ k₂ E₂ p₂ w r₁ r₂ rep₂
    obtain ⟨s₁, a₁, enc₁, hs₁, hmem₁, hrep₁, rfl⟩ := represents_ptr_inv' r₁
    rw [cell₁] at hs₁; cases hs₁
    obtain ⟨ea₁, rfl, hf₁⟩ := represents_construct_inv hrep₁
    cases hf₁ with
    | cons _ hf1' =>
      cases hf1' with
      | cons hrv1 hf1'' =>
        cases hf1'' with
        | cons hrb1 hfn =>
          cases hfn
          cases rep₂ with
          | @letE _ addr₂ tp₂ vp₂ bp₂ T₂ V₂ B₂ cell₂ _ rv₂ rb₂ =>
            obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
            rw [cell₂] at hs₂; cases hs₂
            injection hweq with hty ha; subst ha
            obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
            obtain ⟨ea₂, henc, hf₂⟩ := represents_construct_inv hrep₂
            injection henc with _ _ hea; subst hea
            cases hf₂ with
            | cons _ hf2' =>
              cases hf2' with
              | cons hrv2 hf2'' =>
                cases hf2'' with
                | cons hrb2 hfn2 =>
                  cases hfn2
                  change shapeOf (B₁.instantiate1Lift V₁ 0) = shapeOf (B₂.instantiate1Lift V₂ 0)
                  rw [shapeOf_instantiate1Lift, shapeOf_instantiate1Lift,
                    ihv hrv1 hrv2 rv₂, ihb hrb1 hrb2 rb₂]
          | bvarFree _ _ _ hd => omega
          | @bvarLocal _ addr₂ _ cell₂ _ _ | @sort _ addr₂ _ _ cell₂ _
          | @const _ addr₂ _ _ _ _ _ cell₂ _ _ | @app _ addr₂ _ _ _ _ cell₂ _ _
          | @lam _ addr₂ _ _ _ _ _ _ cell₂ _ _ _ | @forallE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
          | @litNat _ addr₂ _ _ cell₂ _ _ | @litStr _ addr₂ _ _ _ cell₂ _ _
          | @proj _ addr₂ _ _ _ _ _ _ _ cell₂ _ _ =>
            obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
            rw [cell₂] at hs₂; cases hs₂
            injection hweq with hty ha; subst ha
            obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
            obtain ⟨_, henc, _⟩ := represents_construct_inv hrep₂
            simp at henc
  | @litNat _ addr₁ _ _ cell₁ _ _ =>
    intro h₂ k₂ E₂ p₂ w r₁ r₂ rep₂
    obtain ⟨s₁, a₁, enc₁, hs₁, hmem₁, hrep₁, rfl⟩ := represents_ptr_inv' r₁
    rw [cell₁] at hs₁; cases hs₁
    obtain ⟨ea₁, rfl, _⟩ := represents_construct_inv hrep₁
    cases rep₂ with
    | litNat _ _ _ | litStr _ _ _ => rfl
    | bvarFree _ _ _ hd => omega
    | @bvarLocal _ addr₂ _ cell₂ _ _ | @sort _ addr₂ _ _ cell₂ _
    | @const _ addr₂ _ _ _ _ _ cell₂ _ _ | @app _ addr₂ _ _ _ _ cell₂ _ _
    | @lam _ addr₂ _ _ _ _ _ _ cell₂ _ _ _ | @forallE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
    | @letE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _ | @proj _ addr₂ _ _ _ _ _ _ _ cell₂ _ _ =>
      obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
      rw [cell₂] at hs₂; cases hs₂
      injection hweq with hty ha; subst ha
      obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
      obtain ⟨_, henc, _⟩ := represents_construct_inv hrep₂
      simp at henc
  | @litStr _ addr₁ _ _ _ cell₁ _ _ =>
    intro h₂ k₂ E₂ p₂ w r₁ r₂ rep₂
    obtain ⟨s₁, a₁, enc₁, hs₁, hmem₁, hrep₁, rfl⟩ := represents_ptr_inv' r₁
    rw [cell₁] at hs₁; cases hs₁
    obtain ⟨ea₁, rfl, _⟩ := represents_construct_inv hrep₁
    cases rep₂ with
    | litNat _ _ _ | litStr _ _ _ => rfl
    | bvarFree _ _ _ hd => omega
    | @bvarLocal _ addr₂ _ cell₂ _ _ | @sort _ addr₂ _ _ cell₂ _
    | @const _ addr₂ _ _ _ _ _ cell₂ _ _ | @app _ addr₂ _ _ _ _ cell₂ _ _
    | @lam _ addr₂ _ _ _ _ _ _ cell₂ _ _ _ | @forallE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
    | @letE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _ | @proj _ addr₂ _ _ _ _ _ _ _ cell₂ _ _ =>
      obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
      rw [cell₂] at hs₂; cases hs₂
      injection hweq with hty ha; subst ha
      obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
      obtain ⟨_, henc, _⟩ := represents_construct_inv hrep₂
      simp at henc
  | @proj _ addr₁ _ ep₁ _ _ E₁' _ _ cell₁ _ re₁ ihe =>
    intro h₂ k₂ E₂ p₂ w r₁ r₂ rep₂
    obtain ⟨s₁, a₁, enc₁, hs₁, hmem₁, hrep₁, rfl⟩ := represents_ptr_inv' r₁
    rw [cell₁] at hs₁; cases hs₁
    obtain ⟨ea₁, rfl, hf₁⟩ := represents_construct_inv hrep₁
    cases hf₁ with
    | cons _ hf1' =>
      cases hf1' with
      | cons _ hf1'' =>
        cases hf1'' with
        | cons hre1 hfn =>
          cases hfn
          cases rep₂ with
          | @proj _ addr₂ _ ep₂ _ _ E₂' _ _ cell₂ _ re₂ =>
            obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
            rw [cell₂] at hs₂; cases hs₂
            injection hweq with hty ha; subst ha
            obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
            obtain ⟨ea₂, henc, hf₂⟩ := represents_construct_inv hrep₂
            injection henc with _ _ hea; subst hea
            cases hf₂ with
            | cons _ hf2' =>
              cases hf2' with
              | cons _ hf2'' =>
                cases hf2'' with
                | cons hre2 hfn2 =>
                  cases hfn2
                  simp [shapeOf, ihe hre1 hre2 re₂]
          | bvarFree _ _ _ hd => omega
          | @bvarLocal _ addr₂ _ cell₂ _ _ | @sort _ addr₂ _ _ cell₂ _
          | @const _ addr₂ _ _ _ _ _ cell₂ _ _ | @app _ addr₂ _ _ _ _ cell₂ _ _
          | @lam _ addr₂ _ _ _ _ _ _ cell₂ _ _ _ | @forallE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _
          | @letE _ addr₂ _ _ _ _ _ _ cell₂ _ _ _ | @litNat _ addr₂ _ _ cell₂ _ _
          | @litStr _ addr₂ _ _ _ cell₂ _ _ =>
            obtain ⟨s₂, a₂, enc₂, hs₂, hmem₂, hrep₂, hweq⟩ := represents_ptr_inv' r₂
            rw [cell₂] at hs₂; cases hs₂
            injection hweq with hty ha; subst ha
            obtain rfl : enc₂ = _ := hvalid _ hmem₂ _ hmem₁ rfl hty.symm
            obtain ⟨_, henc, _⟩ := represents_construct_inv hrep₂
            simp at henc

/-- A valid ROM address determines `exprSize` for any `TmOExact` term it represents. -/
theorem exprSize_eq_of_represents {rom : ROM F} (hvalid : rom.Valid) {κ : _root_.Address → KKey}
    {h₁ h₂ : Heap F} {E₁ E₂ : KExpr} {p₁ p₂ : SourceValue F} {w : Value F}
    (r₁ : Represents rom h₁ p₁ w) (r₂ : Represents rom h₂ p₂ w)
    (hE₁ : TmOExact κ h₁ E₁ p₁) (hE₂ : TmOExact κ h₂ E₂ p₂) :
    exprSize E₁ = exprSize E₂ := by
  obtain ⟨k₁, rep₁⟩ := hE₁
  obtain ⟨k₂, rep₂⟩ := hE₂
  rw [← exprSize_shapeOf E₁, ← exprSize_shapeOf E₂,
    shapeOf_eq_of_represents hvalid rep₁ r₁ r₂ rep₂]

/-- Every `TmOExact` pointer represented in a ROM encodes to `.ptr (.enum kexprEnum) addr` for
some entry `(addr, enc) ∈ rom.entries`. -/
theorem represents_ptr_of_tmOExact {rom : ROM F} {κ : _root_.Address → KKey} {h : Heap F}
    {E : KExpr} {p : SourceValue F} {w : Value F}
    (hE : TmOExact κ h E p) (r : Represents rom h p w) :
    ∃ addr enc, (addr, enc) ∈ rom.entries ∧ w = .ptr (.enum kexprEnum) addr := by
  obtain ⟨k, rep⟩ := hE
  cases rep with
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _
  | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _
  | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    obtain ⟨s, addr, enc, hs, hmem, hrep, rfl⟩ := represents_ptr_inv' r
    rw [cell] at hs; cases hs
    obtain ⟨_, rfl, _⟩ := represents_construct_inv hrep
    exact ⟨addr, _, hmem, by simp [Value.type]⟩

private theorem call_arg_rep_of_obs {rom : ROM F} {nm : String} {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {cs cs' : List (Call F)} {v : SourceValue F}
    (hcar : CallsInROM rom cs) (_ev : ObsFn W nm args h r h' cs')
    (hmem : (⟨nm, args, h⟩ : Call F) ∈ cs) (hv : v ∈ args) :
    ∃ w, Represents rom h v w :=
  hcar ⟨nm, args, h⟩ hmem v hv

private theorem repList_length_lt_of_obs {en : String} {α : Type*}
    {R : Heap F → α → SourceValue F → Prop} {xs : List α} {p : SourceValue F}
    {nm : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    {cs cs' rootCalls : List (Call F)}
    (hbd : Bounded rootCalls) (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (_ev : ObsFn W nm args h r h' cs')
    (hmem : (⟨nm, args, h⟩ : Call F) ∈ cs) (hp : p ∈ args)
    (hrep : RepList en R h xs p) : xs.length < 2 ^ 39 :=
  RomBound.bounded_length_lt hbd (hsub ⟨nm, args, h⟩ hmem) hp hrep

/-! ## List wrappers, `peel_n_foralls`, `collect_spine`, and record helpers -/

/-- The Aiur type of a flattened-family entry tuple. -/
abbrev flatEntryTy : Generic.Ty :=
  .tuple [(.ptr (.array .field 32)), .field,
    (.ptr (.named "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))])),
    (.ptr (.named "Lists::Node" [(.ptr (.named "KernelTypes::KLevelNode" []))]))]

theorem flat_length_spec {κ : _root_.Address → KKey} {es : List FlatEntry}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>»
      [l] h r h' cs)
    (hl : RepList flatListEnum (FlatEntryRepExact κ) h es l) :
    r = .field (es.length : F) ∧ h' = h := by
  exact Lib.Lists.length_spec (t := flatEntryTy)
    (by rw [Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact hl)

theorem flat_lookup_spec {κ : _root_.Address → KKey} {es : List FlatEntry}
    {l r : SourceValue F} {i : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::lookup<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>»
      [l, .field i] h r h' cs)
    (hl : RepList flatListEnum (FlatEntryRepExact κ) h es l) :
    (∃ e, es[i.val]? = some e ∧ FlatEntryRepExact κ h e r) ∧ h' = h := by
  exact Lib.Lists.lookup_spec (t := flatEntryTy)
    (by rw [Obs.Names.«Lists::lookup<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact hl)

theorem flat_snoc_spec {κ : _root_.Address → KKey} {es : List FlatEntry} {e : FlatEntry}
    {l v r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::snoc<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>»
      [l, v] h r h' cs)
    (hl : RepList flatListEnum (FlatEntryRepExact κ) h es l)
    (he : FlatEntryRepExact κ h e v) :
    RepList flatListEnum (FlatEntryRepExact κ) h' (es ++ [e]) r := by
  have h1 := Lib.Lists.snoc_spec (t := flatEntryTy) (flatEntryRepExact_heapMono₂ (κ := κ))
    (by rw [Obs.Names.«Lists::snoc<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact hl)
    he
  rwa [Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol] at h1

theorem kexpr_length_spec {κ : _root_.Address → KKey} {xs : List KExpr}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum (TmOExact κ) h xs l) :
    r = .field (xs.length : F) ∧ h' = h := by
  exact Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

theorem kexpr_take_spec {κ : _root_.Address → KKey} {xs : List KExpr}
    {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::take<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : RepList kexprListEnum (TmOExact κ) h xs l) :
    n.val ≤ xs.length ∧ RepList kexprListEnum (TmOExact κ) h' (xs.take n.val) r := by
  have h1 := Lib.Lists.take_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (tmOExact_heapMono₂ (κ := κ))
    (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at h1

theorem kexpr_snoc_spec {κ : _root_.Address → KKey} {xs : List KExpr} {x : KExpr}
    {l v r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>» [l, v] h r h' cs)
    (hl : RepList kexprListEnum (TmOExact κ) h xs l)
    (hx : TmOExact κ h x v) :
    RepList kexprListEnum (TmOExact κ) h' (xs ++ [x]) r := by
  have h1 := Lib.Lists.snoc_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (tmOExact_heapMono₂ (κ := κ))
    (by rw [Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
    hx
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at h1

theorem addrIn_peelForalls {S : _root_.Address → Prop} {κ : _root_.Address → KKey} :
    ∀ {n : Nat} {E E' : KExpr},
      AddrIn S κ E → FamilyFlat.peelForalls n E = some E' → AddrIn S κ E'
  | 0, _, _, hE, h => by simp [FamilyFlat.peelForalls] at h; subst h; exact hE
  | n + 1, .forallE _ B _, _, hE, h => addrIn_peelForalls hE.2 h
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, h | _ + 1, .lit _, _, _, h | _ + 1, .proj _ _ _, _, _, h => by
    simp [FamilyFlat.peelForalls] at h

theorem addrIn_binderDomAfter {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {n : Nat} {E d : KExpr} (hE : AddrIn S κ E) (hd : binderDomAfter n E = some d) :
    AddrIn S κ d := by
  unfold binderDomAfter at hd
  cases hp : FamilyFlat.peelForalls n E with
  | none => rw [hp] at hd; cases hd
  | some E' =>
    rw [hp] at hd
    cases E' with
    | forallE D _ _ =>
      injection hd with hd'; subst hd'
      exact (addrIn_peelForalls hE hp).1
    | _ => cases hd

theorem addrIn_instCtorParams {S : _root_.Address → Prop} {κ : _root_.Address → KKey} :
    ∀ {E E' : KExpr} {sp : List KExpr},
      AddrIn S κ E → (∀ p ∈ sp, AddrIn S κ p) →
      instCtorParams E sp = some E' → AddrIn S κ E'
  | _, _, [], hE, _, h => by simp [instCtorParams] at h; subst h; exact hE
  | .forallE _ B _, _, v :: vs, hE, hsp, h =>
    addrIn_instCtorParams
      (addrIn_instantiate1Lift (hsp v (List.mem_cons_self ..)) (d := 0) hE.2)
      (fun p hp => hsp p (List.mem_cons_of_mem _ hp)) h
  | .bvar _, _, _ :: _, _, _, h | .fvar _ _, _, _ :: _, _, _, h | .sort _, _, _ :: _, _, _, h
  | .const _ _, _, _ :: _, _, _, h | .app _ _, _, _ :: _, _, _, h | .lam _ _ _, _, _ :: _, _, _, h
  | .letE _ _ _ _, _, _ :: _, _, _, h | .lit _, _, _ :: _, _, _, h
  | .proj _ _ _, _, _ :: _, _, _, h => by simp [instCtorParams] at h

/-- **`KernelCheck::peel_n_foralls`** on `TmOExact`: succeeds only when the leading `n` nodes
are `Forall`s, matching `peelForalls n E` with zero heap allocation. -/
theorem peel_n_foralls_tmOExact {κ : _root_.Address → KKey} :
    ∀ (n : Nat) {E : KExpr} {xe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 9223372036854775808 →
      ObsFn W "KernelCheck::peel_n_foralls" [xe, .field (n : F)] h r h' cs →
      TmOExact κ h E xe →
      h' = h ∧ ∃ E', FamilyFlat.peelForalls n E = some E' ∧ TmOExact κ h E' r := by
  intro n
  induction n with
  | zero =>
    intro E xe r h h' cs _ ev hE
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. => cases hr; cases hh; exact ⟨rfl, E, rfl, hE⟩
    | .other (hne19 := hne) .. => exact (hne rfl).elim
  | succ n ih =>
    intro E xe r h h' cs hn ev hE
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (hv14 := hv) .. =>
      exact (field_succ_ne_zero n (by omega) hv).elim
    | .other (x_body := xb) (v66 := vn) (ld34 := ld) (op87 := op) (ev64 := ev1) .. =>
      obtain ⟨D, B, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load hE ld
      obtain rfl := evalBinOp_sub_succ n op
      obtain ⟨rfl, E', hp, hE'⟩ := ih (by omega) ev1 hB
      exact ⟨rfl, E', hp, hE'⟩

/-- `KernelCheck::peel_n_foralls` is deterministic on pointer output across heap extensions. -/
theorem peel_n_foralls_det :
    ∀ {n : Nat} {xe r₁ r₂ : SourceValue F} {h₁ h₁' h₂ h₂' : Heap F} {cs₁ cs₂ : List (Call F)},
      n < 9223372036854775808 → Heap.Extends h₁ h₂ →
      ObsFn W "KernelCheck::peel_n_foralls" [xe, .field (n : F)] h₁ r₁ h₁' cs₁ →
      ObsFn W "KernelCheck::peel_n_foralls" [xe, .field (n : F)] h₂ r₂ h₂' cs₂ →
      r₁ = r₂ := by
  intro n
  induction n with
  | zero =>
    intro xe r₁ r₂ h₁ h₁' h₂ h₂' cs₁ cs₂ _ _ ev₁ ev₂
    match Obs.«KernelCheck::peel_n_foralls».obs ev₁, Obs.«KernelCheck::peel_n_foralls».obs ev₂ with
    | .n0 (he16 := hr1) .., .n0 (he16 := hr2) .. => rw [hr1, hr2]
    | .other (hne19 := hne) .., _ => exact (hne rfl).elim
    | _, .other (hne19 := hne) .. => exact (hne rfl).elim
  | succ n ih =>
    intro xe r₁ r₂ h₁ h₁' h₂ h₂' cs₁ cs₂ hn ext ev₁ ev₂
    match Obs.«KernelCheck::peel_n_foralls».obs ev₁, Obs.«KernelCheck::peel_n_foralls».obs ev₂ with
    | .n0 (hv14 := hv) .., _ => exact (field_succ_ne_zero n (by omega) hv).elim
    | _, .n0 (hv14 := hv) .. => exact (field_succ_ne_zero n (by omega) hv).elim
    | .other (x_body := xb1) (v66 := vn1) (ld34 := ld1) (op87 := op1) (ev64 := e1) ..,
      .other (x_body := xb2) (v66 := vn2) (ld34 := ld2) (op87 := op2) (ev64 := e2) .. =>
      have hld := (loadValue_mono ext ld1).symm.trans ld2
      injection hld with hc; injection hc with _ _ hl
      injection hl with _ hl; injection hl with hxb _; subst hxb
      obtain rfl := evalBinOp_sub_succ n op1
      obtain rfl := evalBinOp_sub_succ n op2
      exact ih (by omega) ext e1 e2

private theorem loadValue_of_tmOExact {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr}
    {xe : SourceValue F} (hE : TmOExact κ h E xe) : ∃ v, loadValue h xe = .ok v := by
  obtain ⟨_, rep⟩ := hE
  cases rep with
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _
  | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _
  | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    simp only [loadValue, cell, Value.type, ne_eq, not_true_eq_false, ↓reduceIte,
      bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩

private theorem mkAppN_snoc (hd : KExpr) (args : List KExpr) (a : KExpr) :
    Ix.Kernel.Expr.mkAppN hd (args ++ [a]) = .app (Ix.Kernel.Expr.mkAppN hd args) a := by
  induction args generalizing hd with
  | nil => rfl
  | cons x xs ih => exact ih (.app hd x)

/-- **`KernelTypes::collect_spine`** on `TmOExact`: splits `E = mkAppN hd args` where `xhd`
is not an `App` cell. -/
theorem collect_spine_tmOExact {κ : _root_.Address → KKey} {E : KExpr}
    {xe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelTypes::collect_spine" [xe] h r h' cs)
    (hE : TmOExact κ h E xe) :
    ∃ (xhd xargs : SourceValue F) (hd : KExpr) (args : List KExpr),
      r = .tuple [xhd, xargs] ∧
      TmOExact κ h' hd xhd ∧
      RepList kexprListEnum (TmOExact κ) h' args xargs ∧
      Ix.Kernel.Expr.mkAppN hd args = E ∧
      (∀ v, loadValue h' xhd = .ok v → ∀ vs, vs.length = 2 →
        v ≠ .construct kexprEnum "App" vs) := by
  obtain ⟨xhd, xargs, ps, rfl, hch, -, hrep⟩ := Core.collect_spine_chain ev
  have hch' := hch.mono ev.heap_extends
  have haux :
      ∀ {xe xhd' : SourceValue F} {ps : List (SourceValue F)},
        Core.SpineChain h' xe xhd' ps →
        ∀ {E : KExpr}, TmOExact κ h' E xe →
          ∃ (hd : KExpr) (args : List KExpr),
            TmOExact κ h' hd xhd' ∧
            List.Forall₂ (fun X p => TmOExact κ h' X p) args ps ∧
            Ix.Kernel.Expr.mkAppN hd args = E := by
    intro xe xhd' ps sc
    induction sc with
    | head _ _ =>
      intro E hE'
      exact ⟨E, [], hE', .nil, rfl⟩
    | app ld _ ih =>
      intro E hE'
      obtain ⟨Ef, Ea, rfl, hEf, hEa⟩ := TmOExact.app_of_load hE' ld
      obtain ⟨hd, args, hhd, hargs, hmk⟩ := ih hEf
      refine ⟨hd, args ++ [Ea], hhd, Core.forall₂_append hargs (.cons hEa .nil), ?_⟩
      rw [mkAppN_snoc, hmk]
  obtain ⟨hd, args, hhd, hargs, hmk⟩ := haux hch' (hE.mono ev.heap_extends)
  obtain ⟨v0, hlv0, hne0⟩ := hch'.head_load
  refine ⟨xhd, xargs, hd, args, rfl, hhd, Core.repList_of_eq_forall₂ hrep hargs, hmk, ?_⟩
  intro v hlv vs hlen hcon
  have hsame := hlv0.symm.trans hlv
  injection hsame with hv; subst hv
  exact hne0 vs hlen hcon

/-- `KernelTypes::collect_spine` produces the exact same head pointer across heap extensions. -/
theorem collect_spine_det_head {xe xhd₁ xargs₁ xhd₂ xargs₂ : SourceValue F}
    {h₁ h₁' h₂ h₂' : Heap F} {cs₁ cs₂ : List (Call F)} (ext : Heap.Extends h₁ h₂)
    (ev₁ : ObsFn W "KernelTypes::collect_spine" [xe] h₁ (.tuple [xhd₁, xargs₁]) h₁' cs₁)
    (ev₂ : ObsFn W "KernelTypes::collect_spine" [xe] h₂ (.tuple [xhd₂, xargs₂]) h₂' cs₂) :
    xhd₁ = xhd₂ := by
  obtain ⟨_, hch₁, -, -⟩ := Core.collect_spine_chain_tup ev₁
  obtain ⟨_, hch₂, -, -⟩ := Core.collect_spine_chain_tup ev₂
  exact (hch₁.det ext hch₂).1

theorem getAppFn_mkAppN_const (k : KKey) (us : List KLevel) :
    ∀ (args : List KExpr), (Ix.Kernel.Expr.mkAppN (.const k us) args).getAppFn = .const k us
  | [] => rfl
  | a :: as => by
    suffices h : ∀ (hd : KExpr) (xs : List KExpr),
        (Ix.Kernel.Expr.mkAppN hd xs).getAppFn = hd.getAppFn by
      exact h (.const k us) (a :: as)
    intro hd xs
    induction xs generalizing hd with
    | nil => rfl
    | cons x xs ih =>
      simp only [Ix.Kernel.Expr.mkAppN, List.foldl_cons]
      exact ih (.app hd x)

theorem getAppArgs_mkAppN_const (k : KKey) (us : List KLevel) (args : List KExpr) :
    (Ix.Kernel.Expr.mkAppN (.const k us) args).getAppArgs = args := by
  suffices h : ∀ (hd : KExpr) (xs : List KExpr),
      (Ix.Kernel.Expr.mkAppN hd xs).getAppArgs = hd.getAppArgs ++ xs by
    simpa [Ix.Kernel.Expr.getAppArgs] using h (.const k us) args
  intro hd xs
  induction xs generalizing hd with
  | nil => simp [Ix.Kernel.Expr.mkAppN]
  | cons x xs ih =>
    simp only [Ix.Kernel.Expr.mkAppN, List.foldl_cons]
    rw [ih (.app hd x)]
    simp [Ix.Kernel.Expr.getAppArgs, List.append_assoc]

private theorem record_eq_of_hashed_flat {rootCalls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    {a : _root_.Address} {c c' : Ixon.Constant} {raw : ByteArray}
    (hrec : recordOf E₀ a = some c) (hh : Hashed cs raw)
    (ha : Address.blake3Pure raw = a) (hde : Ixon.deConstantExact raw = .ok c') :
    c' = c := by
  rw [hS.recordOf_eq_recordAt] at hrec
  exact hS.record_eq hrec (Core.hashed_mono hsub hh) ha hde

private theorem held_of_agree_flat {E₀ R : Ixon.Env}
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    {a : _root_.Address} {c : Ixon.Constant} (hSa : Held R a) (hcE : recordOf E₀ a = some c) :
    recordOf R a = some c := by
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hSa
  have := hRagree a c' c hc' hcE
  subst this; exact hc'

theorem tag0Bytes_size_le9 (v : UInt64) :
    (Ixon.Verify.Codec.tag0Bytes v).size ≤ 9 := by
  unfold Ixon.Verify.Codec.tag0Bytes
  rw [Ixon.Verify.Codec.tagNBytes_size]
  unfold Ixon.tagNByteWidth
  repeat' split
  all_goals omega

theorem serConstant_iprj_size_lt (i : UInt64) (b : Bytes.Address) :
    (Ixon.serConstant ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩).size < 4294967296 := by
  open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant in
  have hb : AddressWireWF (Core.ixAddr b) := b.size_toArray
  open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant in
  have hcwf : NonrecursiveConstantWireWF ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ :=
    { info := .iPrj hb
      sharingCount := by show (#[] : Array Ixon.Expr).size < UInt64.size; decide
      sharingEntries := by simp
      refsCount := by show (#[] : Array _root_.Address).size < UInt64.size; decide
      refsEntries := by simp
      univsCount := by show (#[] : Array Ixon.Univ).size < UInt64.size; decide
      univsEntries := by simp
      binders := by simp [Ixon.bindersWireWF] }
  open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant in
  have hser : Ixon.serConstant ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ =
      nonrecursiveConstantBytes ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ := by
    unfold Ixon.serConstant
    exact (putConstant_writes_nonrecursive _ hcwf).runPut
  open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant in
  have hbytes : nonrecursiveConstantBytes ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ =
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_IPRJ ++
        (tag0Bytes i ++ (Core.ixAddr b).hash) ++
        tag0Bytes 0 ++ ByteArray.empty ++ tag0Bytes 0 ++ ByteArray.empty ++
        tag0Bytes 0 ++ ByteArray.empty ++ bindersBytes #[] := rfl
  rw [hser, hbytes]
  have h1 := tag0Bytes_size_le9 i
  have ht4 : (Ixon.Verify.Codec.tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_IPRJ).size = 1 := by
    decide
  have ht0 : (Ixon.Verify.Codec.tag0Bytes 0).size = 1 := by decide
  have hbd0 : (Ixon.Verify.Codec.ConstantTables.bindersBytes #[]).size = 1 := by decide
  have hh : (Core.ixAddr b).hash.size = 32 := hb
  simp only [ByteArray.size_append, ByteArray.size_empty]
  omega

/-- Helper: decoding `Ingress::load_verified_constant` at a `Muts` block address in `E₀`. -/
theorem load_verified_muts_of_record {rootCalls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    {ba : Bytes.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {xba val : SourceValue F} {h h' : Heap F}
    (hcbE : recordOf E₀ (ixAddr ba) = some cb) (hmuts : cb.info = .muts ms)
    (rba : Bytes.RepAddressRef addrTy h ba xba)
    (ev : ObsFn W "Ingress::load_verified_constant" [xba] h val h' cs) :
    ∃ x_members w1 w2 w3 w4,
      val = .construct "Ixon::Constant" "Mk"
        [.construct "Ixon::ConstantInfo" "Muts" [x_members], w1, w2, w3, w4] ∧
      Core.Specs.Callees.MembersRep h' ms.toList x_members := by
  obtain ⟨-, bytes, c, hh, ha, hex, -, -, -, -, -, -, rep⟩ :=
    L1.load_verified_constant_decode rba ev
  have hcEq := record_eq_of_hashed_flat hS hsub hcbE hh ha hex
  subst hcEq
  obtain ⟨iv, sh, rf, un, bd, rfl, hinfo⟩ := rep.toConstShapeRep
  rw [hmuts] at hinfo
  obtain ⟨xm, rfl, hms⟩ := hinfo
  exact ⟨xm, sh, rf, un, bd, rfl, hms⟩

/-! ## `addr_list_contains`, `caddr_is_peer`, `occ_mentions_block`, `occ_any_mentions_block` -/

/-- **`KernelCheck::addr_list_contains`** decides membership of `target` in `xs` with no
allocation. -/
theorem addr_list_contains_spec :
    ∀ (xs : List Bytes.Address) {target : Bytes.Address}
      {xxs xtarget r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelCheck::addr_list_contains" [xxs, xtarget] h r h' cs →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h xs xxs →
      Bytes.RepAddressRef addrTy h target xtarget →
      r = .field (if xs.any (fun a => a == target) then 1 else 0) ∧ h' = h := by
  intro xs
  induction xs with
  | nil =>
    intro target xxs xtarget r h h' cs ev hxs _
    match Obs.«KernelCheck::addr_list_contains».obs ev with
    | .Nil (he20 := hr) (he21 := hh) .. => cases hr; cases hh; exact ⟨rfl, rfl⟩
    | .Cons_n1 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hxs ld
      cases hcons
  | cons a rest ih =>
    intro target xxs xtarget r h h' cs ev hxs rtarget
    match Obs.«KernelCheck::addr_list_contains».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hxs ld
    | .Cons_n1 (ld12 := ld) (ev54 := evaeq) (he75 := hr) (he76 := hh) .. =>
      cases hr; cases hh
      obtain ⟨a', rest', h1, ha', -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hxs ld
      injection h1 with h1a h1r; subst h1a h1r
      obtain ⟨hv, rfl⟩ := Lib.address_eq_spec evaeq ha' rtarget
      have heq : a = target := by
        by_contra hne; rw [ite_eq_right hne] at hv
        exact absurd (Value.field.inj hv) (by decide)
      subst heq
      exact ⟨by simp, rfl⟩
    | .Cons_other (ld12 := ld) (ev54 := evaeq) (hne78 := hne) (ev87 := evrec) .. =>
      obtain ⟨a', rest', h1, ha', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hxs ld
      injection h1 with h1a h1r; subst h1a h1r
      obtain ⟨hv, rfl⟩ := Lib.address_eq_spec evaeq ha' rtarget
      have hdiff : a ≠ target := fun h => by rw [ite_eq_left h] at hv; exact hne hv
      obtain ⟨hr, hh⟩ := ih evrec hrest rtarget
      have hbf : (a == target) = false := beq_eq_false_iff_ne.mpr hdiff
      exact ⟨by simp [hbf, hr], hh⟩

/-- **`KernelCheck::caddr_is_peer`** against singleton `[B]` computes
`peer (FlatView.ofStore t E₀) B (Core.keyOf t (ixAddr a))`. -/
theorem caddr_is_peer_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env} (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c') (hcl : UsedClosed R)
    {a ba : Bytes.Address} {xa xblks r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls) (hSa : Held R (ixAddr a))
    (ra : Bytes.RepAddressRef addrTy h a xa)
    (rblks : RepList addrListEnum (Bytes.RepAddressRef addrTy) h [ba] xblks)
    (ev : ObsFn W "KernelCheck::caddr_is_peer" [xa, xblks] h r h' cs) :
    ∃ b : Bool,
      peer (FlatView.ofStore t E₀) (ixAddr ba) (Core.keyOf t (ixAddr a)) = some b ∧
      r = .field (if b then 1 else 0) := by
  have hka : keyAddr t (Core.keyOf t (ixAddr a)) = some (ixAddr a) :=
    addrOf_ofStore (E₀ := E₀) hwf (ixAddr a)
  match Obs.«KernelCheck::caddr_is_peer».obs ev with
  | .Induct (m2 := m2) (p9 := p9) (cs15 := cs1) (x_ba := xba) (ev17 := evci) (ld11 := ldci)
      (ev94 := evin) (hc111 := hc) .. =>
    have hsub1 : ∀ c ∈ cs1, c ∈ rootCalls := fun c hc' => hsub c (by rw [hc]; simp [hc'])
    obtain ⟨hInd, -⟩ := indInfo_of_get_ci hS hH hbd hRagree hcl hsub1 hSa ra evci ldci
    obtain ⟨info, iba, hinfo, -, -, -, -, -, -, -, -, hiba, riba, -⟩ :=
      hInd _ _ _ _ _ _ _ _ rfl
    have rblks' := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
      evci.heap_extends rblks
    obtain ⟨hr, -⟩ := addr_list_contains_spec [ba] evin rblks' riba
    have hbeq : (ba == iba) = (info.blk == ixAddr ba) := by
      rw [← hiba]
      by_cases h : ba = iba
      · subst h; simp
      · have hne : ixAddr iba ≠ ixAddr ba := fun he => h (ixAddr_inj he).symm
        rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr hne]
    refine ⟨info.blk == ixAddr ba, ?_, ?_⟩
    · simp [peer, FlatView.ofStore, hka, hinfo]
    · simpa [hbeq] using hr
  | .other (cs15 := cs1) (ev17 := evci) (ld11 := ldci) (hne112 := hne) (he116 := hr)
      (hc118 := hc) .. =>
    cases hr
    have hsub1 : ∀ c ∈ cs1, c ∈ rootCalls := fun c hc' => hsub c (by rw [hc]; simp [hc'])
    obtain ⟨-, hOther⟩ := indInfo_of_get_ci hS hH hbd hRagree hcl hsub1 hSa ra evci ldci
    have hinfo := hOther hne
    exact ⟨false, by simp [peer, FlatView.ofStore, hka, hinfo], rfl⟩

/-- **`KernelModeled::occ_mentions_block`** against singleton `[B]` computes
`mentions (FlatView.ofStore t E₀) B E` on `TmOExact` (stepping through `Let` nodes). -/
theorem occ_mentions_block_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env} (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c') (hcl : UsedClosed R)
    {ba : Bytes.Address} {E : KExpr} {xe xblks r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (hE : TmOExact (Core.keyOf t) h E xe) (hEin : AddrIn (Held R) (Core.keyOf t) E)
    (rblks : RepList addrListEnum (Bytes.RepAddressRef addrTy) h [ba] xblks)
    (ev : ObsFn W "KernelModeled::occ_mentions_block" [xe, xblks] h r h' cs) :
    ∃ b : Bool,
      mentions (FlatView.ofStore t E₀) (ixAddr ba) E = some b ∧
      r = .field (if b then 1 else 0) := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → ∀ c ∈ cs', c ∈ rootCalls :=
    fun hs c hc => hsub c (hs c hc)
  have bnd_sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
    fun hs => RomBound.bounded_mono hbd (sub hs)
  match Obs.«KernelModeled::occ_mentions_block».obs ev with
  | .BVar (ld_bolbylmd := ld) (he_njbtkguh := hr0) .. =>
    cases hr0
    obtain ⟨_, -, -, rfl⟩ := TmOExact.bvar_of_load hE ld
    exact ⟨false, rfl, rfl⟩
  | .Srt (ld_bolbylmd := ld) (he_etzrxboe := hr0) .. =>
    cases hr0
    obtain ⟨_, rfl, -⟩ := TmOExact.sort_of_load hE ld
    exact ⟨false, rfl, rfl⟩
  | .Const (cs_anabekbn := cs1) (ld_bolbylmd := ld) (ev_okamjwqm := evp) (hc_atlxlyhr := hc) .. =>
    obtain ⟨a, us, rfl, ra, -⟩ := TmOExact.const_of_load hE ld
    have hSa : Held R (ixAddr a) := hEin (ixAddr a) rfl
    obtain ⟨b, hb, hr⟩ := caddr_is_peer_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) hSa ra rblks evp
    exact ⟨b, hb, hr⟩
  | .App_n1 (cs_nlxcjtbe := cs1) (ld_bolbylmd := ld) (ev_cwxibbky := evf) (he_sqbyfahs := hr0)
      (hc_gmeblcmg := hc) .. =>
    cases hr0
    obtain ⟨Ef, Ea, rfl, hEf, -⟩ := TmOExact.app_of_load hE ld
    have hlt : cs1.length < cs.length := by rw [hc]; simp
    obtain ⟨b, hb, hr⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) hEf hEin.1 rblks evf
    cases b with
    | true => exact ⟨true, by simp [mentions, orB, hb], rfl⟩
    | false => exact absurd (Value.field.inj hr) (by decide)
  | .App_other (cs_nlxcjtbe := cs1) (cs_jlnluzll := cs2) (ld_bolbylmd := ld)
      (ev_cwxibbky := evf) (hne_rvlihvhx := hne) (ev_cgdhukiy := eva) (hc_imahflfm := hc) .. =>
    obtain ⟨Ef, Ea, rfl, hEf, hEa⟩ := TmOExact.app_of_load hE ld
    have hlt1 : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    have hlt2 : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨b1, hb1, hr1⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) hEf hEin.1 rblks evf
    cases b1 with
    | true => exact (hne hr1).elim
    | false =>
      have rblks' := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
        evf.heap_extends rblks
      obtain ⟨b2, hb2, hr2⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
        (sub fun c hc' => by rw [hc]; simp [hc']) (hEa.mono evf.heap_extends) hEin.2 rblks' eva
      exact ⟨b2, by simp [mentions, orB, hb1, hb2], hr2⟩
  | .Lam_n1 (cs_sdfuhkpl := cs1) (ld_bolbylmd := ld) (ev_ulwgmnpt := evt) (he_opcvlshe := hr0)
      (hc_sgloqhqt := hc) .. =>
    cases hr0
    obtain ⟨T, B, ℓ, rfl, hT, -, -⟩ := TmOExact.lam_of_load hE ld
    have hlt : cs1.length < cs.length := by rw [hc]; simp
    obtain ⟨b, hb, hr⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) hT hEin.1 rblks evt
    cases b with
    | true => exact ⟨true, by simp [mentions, orB, hb], rfl⟩
    | false => exact absurd (Value.field.inj hr) (by decide)
  | .Lam_other (cs_sdfuhkpl := cs1) (cs_yskgpazx := cs2) (ld_bolbylmd := ld)
      (ev_ulwgmnpt := evt) (hne_puvcobve := hne) (ev_dizlvils := evb) (hc_kjyrsefa := hc) .. =>
    obtain ⟨T, B, ℓ, rfl, hT, hB, -⟩ := TmOExact.lam_of_load hE ld
    have hlt1 : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    have hlt2 : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨b1, hb1, hr1⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) hT hEin.1 rblks evt
    cases b1 with
    | true => exact (hne hr1).elim
    | false =>
      have rblks' := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
        evt.heap_extends rblks
      obtain ⟨b2, hb2, hr2⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
        (sub fun c hc' => by rw [hc]; simp [hc']) (hB.mono evt.heap_extends) hEin.2 rblks' evb
      exact ⟨b2, by simp [mentions, orB, hb1, hb2], hr2⟩
  | .Forall_n1 (cs_jnsilbfh := cs1) (ld_bolbylmd := ld) (ev_jphceggz := evt) (he_aimigplr := hr0)
      (hc_gwofqrgs := hc) .. =>
    cases hr0
    obtain ⟨T, B, ℓ, rfl, hT, -, -⟩ := TmOExact.forallE_of_load hE ld
    have hlt : cs1.length < cs.length := by rw [hc]; simp
    obtain ⟨b, hb, hr⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) hT hEin.1 rblks evt
    cases b with
    | true => exact ⟨true, by simp [mentions, orB, hb], rfl⟩
    | false => exact absurd (Value.field.inj hr) (by decide)
  | .Forall_other (cs_jnsilbfh := cs1) (cs_gnwuatpb := cs2) (ld_bolbylmd := ld)
      (ev_jphceggz := evt) (hne_oaofvnuw := hne) (ev_dbsnzmoy := evb) (hc_hkhtpxta := hc) .. =>
    obtain ⟨T, B, ℓ, rfl, hT, hB, -⟩ := TmOExact.forallE_of_load hE ld
    have hlt1 : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    have hlt2 : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨b1, hb1, hr1⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) hT hEin.1 rblks evt
    cases b1 with
    | true => exact (hne hr1).elim
    | false =>
      have rblks' := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
        evt.heap_extends rblks
      obtain ⟨b2, hb2, hr2⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
        (sub fun c hc' => by rw [hc]; simp [hc']) (hB.mono evt.heap_extends) hEin.2 rblks' evb
      exact ⟨b2, by simp [mentions, orB, hb1, hb2], hr2⟩
  | .Let (cs_wjijdite := cs2) (cs_yqrxeseo := cs1) (ld_bolbylmd := ld) (ev_gemvpjgn := evi)
      (ev_rbprmbdg := evrec) (hc_qubwlzze := hc) .. =>
    obtain ⟨T, V0, B, rfl, -, hV, hB⟩ := TmOExact.letE_of_load hE ld
    have hv' := expr_inst1_tmOExact (bnd_sub fun c hc' => by rw [hc]; simp [hc']) hB hV evi
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    have rblks' := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
      evi.heap_extends rblks
    exact occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) hv' hEin rblks' evrec
  | .Lit (ld_bolbylmd := ld) (he_pgejtxya := hr0) .. =>
    cases hr0
    obtain ⟨k, rep⟩ := hE
    cases rep with
    | litNat _ _ _ | litStr _ _ _ => exact ⟨false, rfl, rfl⟩
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _
    | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _
    | proj cell _ _ =>
      simp [loadValue, cell, kexprEnum] at ld
  | .Proj (cs_yblrkquu := cs1) (ld_bolbylmd := ld) (ev_fnwcywxx := evp) (hc_rksetomy := hc) .. =>
    obtain ⟨a, i, E1, -, rfl, -, hE1⟩ := TmOExact.proj_of_load hE ld
    have hlt : cs1.length < cs.length := by rw [hc]; simp
    obtain ⟨b, hb, hr⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) hE1 hEin.2 rblks evp
    exact ⟨b, hb, hr⟩
termination_by cs.length

/-- **`KernelModeled::occ_any_mentions_block`** against singleton `[B]` computes
`mentionsList (FlatView.ofStore t E₀) B es`. -/
theorem occ_any_mentions_block_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env} (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c') (hcl : UsedClosed R)
    {ba : Bytes.Address} :
    ∀ (es : List KExpr) {xes xblks r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ c ∈ cs, c ∈ rootCalls) →
      RepList kexprListEnum (TmOExact (Core.keyOf t)) h es xes →
      (∀ E ∈ es, AddrIn (Held R) (Core.keyOf t) E) →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h [ba] xblks →
      ObsFn W "KernelModeled::occ_any_mentions_block" [xes, xblks] h r h' cs →
      ∃ b : Bool,
        mentionsList (FlatView.ofStore t E₀) (ixAddr ba) es = some b ∧
        r = .field (if b then 1 else 0) := by
  intro es
  induction es with
  | nil =>
    intro xes xblks r h h' cs _ hes _ _ ev
    match Obs.«KernelModeled::occ_any_mentions_block».obs ev with
    | .Nil (he_szuveosd := hr0) .. => cases hr0; exact ⟨false, rfl, rfl⟩
    | .Cons_n1 (ld_bolbylmd := ld) .. | .Cons_other (ld_bolbylmd := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e rest ih =>
    intro xes xblks r h h' cs hsub hes hIn rblks ev
    match Obs.«KernelModeled::occ_any_mentions_block».obs ev with
    | .Nil (ld_bolbylmd := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_n1 (cs_jubaoqto := cs1) (ld_bolbylmd := ld) (ev_bibwviky := ev1)
        (he_gwkmofqm := hr0) (hc_gsysyyvr := hc) .. =>
      cases hr0
      obtain ⟨e', rest', h1, he', -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with h1e h1r; subst h1e h1r
      obtain ⟨b, hb, hr⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) he' (hIn e (List.mem_cons_self ..))
        rblks ev1
      cases b with
      | true => exact ⟨true, by simp [mentionsList, orB, hb], rfl⟩
      | false => exact absurd (Value.field.inj hr) (by decide)
    | .Cons_other (cs_jubaoqto := cs1) (cs_omdssxud := cs2) (ld_bolbylmd := ld)
        (ev_bibwviky := ev1) (hne_ubqoerny := hne) (ev_cpwcgvda := ev2)
        (hc_tmxzbzju := hc) .. =>
      obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with h1e h1r; subst h1e h1r
      obtain ⟨b1, hb1, hr1⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) he' (hIn e (List.mem_cons_self ..))
        rblks ev1
      cases b1 with
      | true => exact (hne hr1).elim
      | false =>
        have rblks' := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
          ev1.heap_extends rblks
        obtain ⟨b2, hb2, hr2⟩ := ih (fun c hc' => hsub c (by rw [hc]; simp [hc']))
          (tmOExactList_mono ev1.heap_extends hrest)
          (fun x hx => hIn x (List.mem_cons_of_mem _ hx)) rblks' ev2
        exact ⟨b2, by simp [mentionsList, orB, hb1, hb2], hr2⟩

/-! ## `build_param_lvls_range`, `flat_originals_walk`, `build_flat_originals` -/

/-- **`KernelCheck::build_param_lvls_range(start, count, i)`** builds
`((List.range count).drop i).map (fun j => .param (start + j))`. -/
theorem build_param_lvls_range_spec (start count : Nat)
    (hsum : start + count ≤ 4294967296) :
    ∀ (k i : Nat) {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      i + k = count →
      ObsFn W "KernelCheck::build_param_lvls_range"
        [.field (start : F), .field (count : F), .field (i : F)] h r h' cs →
      RepKLevelList h' (((List.range count).drop i).map fun j => .param (start + j)) r := by
  intro k
  induction k with
  | zero =>
    intro i r h h' cs hik ev
    have hi : i = count := by omega
    subst hi
    match Obs.«KernelCheck::build_param_lvls_range».obs ev with
    | .n0 (he28 := hr0) (hm27 := hm0) .. =>
      cases hr0; cases hm0
      simp only [List.drop_eq_nil_of_le (by simp : (List.range i).length ≤ i), List.map_nil]
      obtain ⟨repN, _⟩ := RepKLevelList.allocNil h
      rw [IxVM.Refinement.Levels.klevelList_names] at repN
      exact repN
    | .other (op17 := op) (hne33 := hne) .. =>
      simp only [evalBinOp, sub_self, Except.ok.injEq] at op
      exact (hne op.symm).elim
  | succ k ih =>
    intro i r h h' cs hik ev
    match Obs.«KernelCheck::build_param_lvls_range».obs ev with
    | .n0 (op17 := op) .. =>
      have h0 : ((count : F) - (i : F)) = 0 := by
        simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op; exact op
      have h1 : ((count : F)) = (i : F) := sub_eq_zero.mp h0
      have h2 : count = i := by
        have hc := fval_natCast (n := count) (by omega)
        have hi := fval_natCast (n := i) (by omega)
        rw [← hc, ← hi, h1]
      omega
    | .other (v46 := vrest) (m48 := m1) (v60 := vp) (m78 := m2) (op17 := op)
        (he41 := hr0) (hm40 := hm0) (hm56 := hm1) (op74 := opadd) (op119 := opi1)
        (ev88 := evrec) .. =>
      cases hr0; cases hm0; cases hm1
      obtain rfl := binop_add_nat opadd
      obtain rfl := binop_add_one_nat opi1
      have hrec := ih (i + 1) (by omega) evrec
      have hdrop : (List.range count).drop i = i :: (List.range count).drop (i + 1) := by
        have hlt : i < (List.range count).length := by simp; omega
        rw [List.drop_eq_getElem_cons hlt]; simp
      rw [hdrop, List.map_cons]
      have hparam : RepKLevel (h ++ [.construct klevelEnum "Param" [.field ((start + i : Nat) : F)]])
          (.param (start + i)) (.ptr (.enum klevelEnum) h.length) :=
        KernelLevels.RepKLevel.param (by omega) (by simp [klevelEnum, KernelLevels.klevelEnum])
      have hparam' : RepKLevel m2 (.param (start + i)) (.ptr (.enum klevelEnum) h.length) :=
        hparam.mono evrec.heap_extends
      obtain ⟨repC, _⟩ := RepKLevelList.allocCons hparam' hrec
      rw [IxVM.Refinement.Levels.klevelList_names] at repC
      exact repC

private theorem flat_originals_walk_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R)
    {ba : Bytes.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {off : Nat} (hoff : off ≤ 1)
    (hSb : Held R (ixAddr ba)) (hcbE : recordOf E₀ (ixAddr ba) = some cb)
    (hmuts : cb.info = .muts ms) :
    ∀ (cur : List Ixon.MutConst) (pos : Nat)
      {xall xcur xba r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ c ∈ cs, c ∈ rootCalls) →
      pos + cur.length = ms.size →
      (∀ i m, cur[i]? = some m → ms[pos + i]? = some m) →
      Core.Specs.Callees.MembersRep h ms.toList xall →
      Core.Specs.Callees.MembersRep h cur xcur →
      Bytes.RepAddressRef addrTy h ba xba →
      ObsFn W "KernelCheck::flat_originals_walk"
        [xall, xcur, xba, .field (off : F), .field (pos : F)] h r h' cs →
      ∃ os : List FlatEntry,
        originals (FlatView.ofStore t E₀) off (indcAddrs (ixAddr ba) pos cur) = some os ∧
        RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h' os r ∧
        os.map (·.addr) = indcAddrs (ixAddr ba) pos cur ∧
        (∀ e ∈ os, e.aux = false ∧ e.params = [] ∧ Held R e.addr ∧
          ∃ idx ind, ms[idx]? = some (.indc ind) ∧
            e.addr = memberAddr (ixAddr ba) idx (.indc ind)) := by
  intro cur
  induction cur with
  | nil =>
    intro pos xall xcur xba r h h' cs _ _ _ _ hcur _ ev
    match Obs.«KernelCheck::flat_originals_walk».obs ev with
    | .Nil (he24 := hr0) (hm23 := hm0) .. =>
      cases hr0; cases hm0
      exact ⟨[], rfl, Lib.rep_store_nil h, rfl, fun _ hm => nomatch hm⟩
    | .Cons_Indc (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      cases hcons
  | cons m rest ih =>
    intro pos xall xcur xba r h h' cs hsub hlen hidx hall hcur rba ev
    have hm_at : ms[pos]? = some m := by simpa using hidx 0 m rfl
    have hidx' : ∀ i m', rest[i]? = some m' → ms[(pos + 1) + i]? = some m' := fun i m' hi => by
      have h1 := hidx (i + 1) m' (by simpa using hi)
      rwa [show pos + (i + 1) = (pos + 1) + i by omega] at h1
    match Obs.«KernelCheck::flat_originals_walk».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hcur ld
    | .Cons_Indc (x_rest := xrest) (v68 := xpaddr) (m69 := m1) (cs79 := cs1)
        (v106 := vci) (m107 := m2) (p114 := pci) (cs120 := cs2)
        (v213 := vnl) (m214 := m3) (cs216 := cs3) (v222 := vlvls) (m223 := m4) (cs233 := cs4)
        (v268 := vtail) (m295 := m5) (m315 := m6) (cs323 := cs5) (v330 := vpos1)
        (ld12 := ld) (ev81 := evpa) (ev122 := eviprj) (ld116 := ldci) (sg221 := sg)
        (ev235 := evlvls) (he263 := hr0) (hm262 := hm0) (hm303 := hm1) (op372 := op1)
        (ev325 := evrec) (hc374 := hc) .. =>
      cases hr0; cases hm0; cases hm1
      obtain ⟨m', rest', h1, hm', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      injection h1 with h1m h1r; subst h1m h1r
      cases m with
      | defn _ => obtain ⟨_, hshape⟩ := hm'; simp [Core.Specs.Callees.mutCtor] at hshape
      | recr _ => obtain ⟨_, hshape⟩ := hm'; simp [Core.Specs.Callees.mutCtor] at hshape
      | indc ind =>
        obtain ⟨ext1, hpos56, -, mc, ma, hmc, rma, hma, hh_proj⟩ :=
          L1.projection_addr_hashed_spec hall rba evpa
        have hpos_val : ((pos : F)).val = pos := by
          have hsz : pos < ms.size := (Array.getElem?_eq_some_iff.mp hm_at).1
          have hbd2 : Bounded cs2 := RomBound.bounded_mono hbd (fun c hc' => hsub c (by rw [hc]; simp [hc']))
          obtain ⟨-, -, blkBytes, cb', _, _, _, _, hhB, haB, hexB, -, -, -, -, -, -⟩ :=
            L1.get_ci_iprj_spec hbd2 (Bytes.repAddressRef_heapMono₂ addrTy ext1 rba) eviprj
          have hcb_eq : cb' = cb :=
            record_eq_of_hashed_flat hS (fun c hc' => hsub c (by rw [hc]; simp [hc']))
              hcbE hhB haB hexB
          subst cb'
          obtain ⟨c0, hc0, -, inp, hargs, hrep⟩ := hhB
          have hbl : blkBytes.size < 2 ^ 39 := by
            have hlt := RomBound.bounded_length_lt hbd2 hc0 (by rw [hargs]; simp) hrep
            change blkBytes.data.toList.length < 2 ^ 39 at hlt
            have hsz' : blkBytes.size = blkBytes.data.toList.length := by
              simp only [ByteArray.size, Array.length_toList]
            omega
          have := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound blkBytes cb hexB
          have := Claim.muts_size_le hmuts
          exact fval_natCast (by omega)
        rw [hpos_val] at hmc hpos56 hma hh_proj
        have hmc' : ms[pos]? = some mc := by rw [← Array.getElem?_toList]; exact hmc
        have hmc_eq : mc = .indc ind := Option.some.inj (hmc'.symm.trans hm_at)
        subst hmc_eq
        have hbd2 : Bounded cs2 := RomBound.bounded_mono hbd (fun c hc' => hsub c (by rw [hc]; simp [hc']))
        obtain ⟨ext2, -, blkBytes, cb', ms', ind', blobs, vci', hhB, haB, hexB, -, hcb', hms',
          -, hld', hrawI⟩ :=
          L1.get_ci_iprj_spec hbd2 (Bytes.repAddressRef_heapMono₂ addrTy ext1 rba) eviprj
        rw [hpos_val] at hms' hrawI
        rw [hld'] at ldci; injection ldci with hv; subst hv
        have hcb_eq : cb' = cb :=
          record_eq_of_hashed_flat hS (fun c hc' => hsub c (by rw [hc]; simp [hc']))
            hcbE hhB haB hexB
        subst cb'
        have hmsEq := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hmuts)
        subst ms'
        have hindEq : ind' = ind := by
          have : ms[pos]? = some (.indc ind') := by rw [← Array.getElem?_toList]; exact hms'
          exact Ixon.MutConst.indc.inj (Option.some.inj (this.symm.trans hm_at))
        subst ind'
        obtain ⟨hnl, _, _, _, _, _, _, _, _, _, hshape, _⟩ := hrawI
        have hsg : vnl = .field (ind.lvls.toNat : F) ∧ m3 = m2 := by
          cases sg with
          | Induct _ _ _ _ _ _ _ _ hv hr hh _ =>
            rw [hshape] at hv
            injection hv with _ _ hl; injection hl with h1 _; exact ⟨hr.trans h1.symm, hh⟩
          | other hne _ _ _ => exact (hne _ rfl hshape).elim
        obtain ⟨rfl, hm3⟩ := hsg
        subst m3
        have evlvls' : ObsFn W "KernelCheck::build_param_lvls_range"
            [.field (off : F), .field (ind.lvls.toNat : F), .field ((0 : Nat) : F)]
            m2 vlvls m4 cs4 := by simpa using evlvls
        have hlvls := build_param_lvls_range_spec off ind.lvls.toNat (by omega)
          ind.lvls.toNat 0 (by omega) evlvls'
        simp only [List.drop_zero] at hlvls
        obtain rfl := binop_add_one_nat op1
        have ext14 := ext1.trans (ext2.trans evlvls.heap_extends)
        have ext45 : Heap.Extends m4 (m4 ++ [.construct kexprListEnum "Nil" []]) :=
          Heap.Extends.snoc _ _
        have ext15 := ext14.trans ext45
        obtain ⟨os, hos, hrep_os, haddrs, hprops⟩ := ih (pos + 1)
          (fun c hc' => hsub c (by rw [hc]; simp [hc'])) (by simp at hlen; omega) hidx'
          (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext15 hall)
          (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext15 hrest)
          (Bytes.repAddressRef_heapMono₂ addrTy ext15 rba) evrec
        have hcbR : recordOf R (ixAddr ba) = some cb := held_of_agree_flat hRagree hSb hcbE
        have hprojR := (hcl.2 (ixAddr ba) cb ms hcbR hmuts pos (.indc ind) hm_at).1
        have hprojE : recordOf E₀ (memberAddr (ixAddr ba) pos (.indc ind)) =
            some (memberProjection (ixAddr ba) pos (.indc ind)) := by
          have hwf_p := L1.projConstant_wireWF_iPrj pos.toUInt64 ba
          have hex_p := Ixon.Verify.deConstantExact_serConstant _ hwf_p
          have hsz_p := serConstant_iprj_size_lt pos.toUInt64 ba
          have hh_p : Hashed rootCalls (Ixon.serConstant (memberProjection (ixAddr ba) pos (.indc ind))) :=
            Core.hashed_mono (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hh_proj
          exact Claim.recordOf_of_hashed hH hh_p hsz_p hex_p
        have hpos64 : pos.toUInt64.toNat = pos := by
          change (UInt64.ofNat pos).toNat = pos
          rw [UInt64.toNat_ofNat']
          have h64 : UInt64.size = 18446744073709551616 := rfl
          exact Nat.mod_eq_of_lt (by omega)
        have hinfo_at : indInfoAt E₀ (memberAddr (ixAddr ba) pos (.indc ind)) =
            some (some ⟨ind.lvls.toNat, ind.params.toNat, ind.ctors.size, ixAddr ba, pos⟩) := by
          unfold indInfoAt
          simp only [hprojE, memberProjection, hcbE, hmuts, hpos64, hm_at]
        have hma_eq : ixAddr ma = memberAddr (ixAddr ba) pos (.indc ind) := hma
        have hnil_e : RepList kexprListEnum (TmOExact (Core.keyOf t))
            (m4 ++ [.construct kexprListEnum "Nil" []]) [] (.ptr (.enum kexprListEnum) m4.length) :=
          Lib.rep_store_nil m4
        have ext_m4_m6 := ext45.trans evrec.heap_extends
        have hentry : FlatEntryRepExact (Core.keyOf t) m6
            ⟨memberAddr (ixAddr ba) pos (.indc ind), false, [],
              (List.range ind.lvls.toNat).map fun j => .param (off + j)⟩
            (.tuple [xpaddr, .field 0, .ptr (.enum kexprListEnum) m4.length, vlvls]) :=
          ⟨xpaddr, .ptr (.enum kexprListEnum) m4.length, vlvls, ma, rfl,
            Bytes.repAddressRef_heapMono₂ addrTy
              (ext2.trans (evlvls.heap_extends.trans ext_m4_m6)) rma,
            hma_eq, tmOExactList_mono evrec.heap_extends hnil_e, hlvls.mono ext_m4_m6⟩
        refine ⟨⟨memberAddr (ixAddr ba) pos (.indc ind), false, [],
            (List.range ind.lvls.toNat).map fun j => .param (off + j)⟩ :: os, ?_, ?_, ?_, ?_⟩
        · simp only [indcAddrs, originals]
          rw [show (FlatView.ofStore t E₀).ci (memberAddr (ixAddr ba) pos (.indc ind)) =
            some (some ⟨ind.lvls.toNat, ind.params.toNat, ind.ctors.size, ixAddr ba, pos⟩) from hinfo_at,
            hos]
        · exact Lib.rep_store_cons flatEntryRepExact_heapMono₂ hentry hrep_os
        · simp [indcAddrs, haddrs]
        · intro e he
          rcases List.mem_cons.mp he with rfl | hmem
          · exact ⟨rfl, rfl, Option.isSome_iff_exists.mpr ⟨_, hprojR⟩, pos, ind, hm_at, rfl⟩
          · exact hprops e hmem
    | .Cons_other (x_m := xm) (x_rest := xrest) (cs382 := cs1) (v389 := vpos1) (ld12 := ld)
        (hne375 := hne) (op431 := op1) (ev384 := evrec) (hc433 := hc) .. =>
      obtain ⟨m', rest', h1, hm', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      injection h1 with h1m h1r; subst h1m h1r
      cases m with
      | indc _ => obtain ⟨_, hshape⟩ := hm'; exact (hne _ rfl hshape).elim
      | defn _ | recr _ =>
        obtain rfl := binop_add_one_nat op1
        obtain ⟨os, hos, hrep_os, haddrs, hprops⟩ := ih (pos + 1)
          (fun c hc' => hsub c (by rw [hc]; simp [hc'])) (by simp at hlen; omega) hidx'
          hall hrest rba evrec
        exact ⟨os, by simpa [indcAddrs] using hos, hrep_os, by simpa [indcAddrs] using haddrs,
          hprops⟩

/-- **`KernelCheck::build_flat_originals`** on a `Muts` block computes
`originals (FlatView.ofStore t E₀) off (indcAddrs B 0 ms.toList)`. -/
theorem build_flat_originals_muts_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R)
    {ba : Bytes.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {off : Nat} {xba r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hoff : off ≤ 1) (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (hSb : Held R (ixAddr ba)) (hcbE : recordOf E₀ (ixAddr ba) = some cb)
    (hmuts : cb.info = .muts ms)
    (rba : Bytes.RepAddressRef addrTy h ba xba)
    (ev : ObsFn W "KernelCheck::build_flat_originals" [xba, .field (off : F)] h r h' cs) :
    ∃ os : List FlatEntry,
      originals (FlatView.ofStore t E₀) off (indcAddrs (ixAddr ba) 0 ms.toList) = some os ∧
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h' os r ∧
      os.map (·.addr) = indcAddrs (ixAddr ba) 0 ms.toList ∧
      (∀ e ∈ os, e.aux = false ∧ e.params = [] ∧ Held R e.addr ∧
        ∃ idx ind, ms[idx]? = some (.indc ind) ∧
          e.addr = memberAddr (ixAddr ba) idx (.indc ind)) := by
  match Obs.«KernelCheck::build_flat_originals».obs ev with
  | .Muts (m2 := m2) (cs12 := cs1) (x_members := xmem) (cs92 := cs2) (ev14 := evld)
      (ev94 := evwalk) (hc134 := hc) .. =>
    obtain ⟨xm, _, _, _, _, hv, hms⟩ := load_verified_muts_of_record hS
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcbE hmuts rba evld
    injection hv with _ _ hl; injection hl with hm _; injection hm with _ _ hml
    injection hml with hx; subst hx
    have evwalk' : ObsFn W "KernelCheck::flat_originals_walk"
        [xmem, xmem, xba, .field (off : F), .field ((0 : Nat) : F)] m2 r h' cs2 := by
      simpa using evwalk
    exact flat_originals_walk_spec hS hH hbd hRagree hcl hoff hSb hcbE hmuts ms.toList 0
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) (by simp)
      (fun i m hm => by simpa [← Array.getElem?_toList] using hm)
      hms hms (Bytes.repAddressRef_heapMono₂ addrTy evld.heap_extends rba) evwalk'
  | .other_Induct (cs12 := cs1) (ev14 := evld) (hne135 := hne) (hc332 := hc) ..
  | .other_other (cs12 := cs1) (ev14 := evld) (hne135 := hne) (hc345 := hc) .. =>
    obtain ⟨xm, _, _, _, _, hv, -⟩ := load_verified_muts_of_record hS
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcbE hmuts rba evld
    injection hv with _ _ hl; injection hl with hm _
    exact (hne [xm] rfl hm).elim

/-! ## `occ_params_lower`, `aux_entry_in`, `add_block_members` -/

/-- **`KernelModeled::occ_params_lower`** computes `occParamsLower ds d` on `TmOExact` and
preserves `AddrIn S κ`. -/
theorem occ_params_lower_spec {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {d : Nat} (hd : d < 4611686018427387904) :
    ∀ (ds : List KExpr) {xds r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelModeled::occ_params_lower" [xds, .field (d : F)] h r h' cs →
      Bounded cs →
      RepList kexprListEnum (TmOExact κ) h ds xds →
      (∀ x ∈ ds, AddrIn S κ x) →
      ∃ sp : List KExpr,
        occParamsLower ds d = some sp ∧
        RepList kexprListEnum (TmOExact κ) h' sp r ∧
        (∀ x ∈ sp, AddrIn S κ x) := by
  intro ds
  induction ds with
  | nil =>
    intro xds r h h' cs ev _ hds _
    match Obs.«KernelModeled::occ_params_lower».obs ev with
    | .Nil (he24 := hr0) (hm23 := hm0) .. =>
      cases hr0; cases hm0
      exact ⟨[], rfl, Lib.rep_store_nil h, fun _ hm => nomatch hm⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hds ld
      cases hcons
  | cons x rest ih =>
    intro xds r h h' cs ev hbnd hds hIn
    match Obs.«KernelModeled::occ_params_lower».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hds ld
    | .Cons (x_x := xx) (x_rest := xrest) (m60 := m1) (cs68 := cs1) (v109 := vx')
        (v110 := vrest') (m112 := m2) (cs120 := cs2) (m147 := m3) (cs155 := cs3)
        (ld12 := ld) (ev70 := evhb) (heq100 := heq0) (he105 := hr0) (hm104 := hm0)
        (ev122 := evlow) (ev157 := evrec) (hc174 := hc) .. =>
      cases hr0; cases hm0
      obtain ⟨x', rest', h1, hx, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hds ld
      injection h1 with h1x h1r; subst h1x h1r
      have bnd1 : Bounded cs1 := RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
      have bnd2 : Bounded cs2 := RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
      have bnd3 : Bounded cs3 := RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
      have evhb' : ObsFn W "KernelSubst::has_bvar_in_range"
          [xx, .field ((0 : Nat) : F), .field (d : F)] h (.field 0) m1 cs1 := by
        simpa [heq0] using evhb
      obtain ⟨hm1, hn, hno⟩ := has_bvar_in_range_zero_tmOExact (by decide) hd bnd1 hx evhb'
      subst m1
      have evlow' : ObsFn W "KernelSubst::expr_lower"
          [xx, .field (d : F), .field ((0 : Nat) : F)] h vx' m2 cs2 := by simpa using evlow
      have hlow := expr_lower_tmOExact (cut := 0) hd (by decide) bnd2 hx (by simpa using hn) evlow'
      obtain ⟨sp, hsp, hrep_sp, hspIn⟩ := ih evrec bnd3
        (tmOExactList_mono (evhb.heap_extends.trans evlow.heap_extends) hrest)
        (fun y hy => hIn y (List.mem_cons_of_mem _ hy))
      refine ⟨x.lowerBVars d 0 :: sp, ?_, ?_, ?_⟩
      · simp [occParamsLower, hno, hsp]
      · exact Lib.rep_store_cons tmOExact_heapMono₂ (hlow.mono evrec.heap_extends) hrep_sp
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hm
        · exact addrIn_lowerBVars d (c := 0) (hIn x (List.mem_cons_self ..))
        · exact hspIn y hm

private theorem field_mul_bool_flat2 {b₁ b₂ : Bool} {v : SourceValue F}
    (op : evalBinOp .mul (.field (if b₁ then 1 else 0)) (.field (if b₂ then 1 else 0)) = .ok v) :
    v = .field (if (b₁ && b₂) then 1 else 0) := by
  cases b₁ <;> cases b₂ <;> (simp only [evalBinOp, Bool.and_false, Bool.and_true, Bool.false_and,
    Bool.true_and, ↓reduceIte] at op ⊢; injection op with hv; rw [← hv]; simp)

/-- **`KernelModeled::aux_entry_in`** decides `auxEntryIn acc (ixAddr a) sp us` on
`FlatEntryRepExact`. -/
theorem aux_entry_in_spec {κ : _root_.Address → KKey} (hinj : Function.Injective κ) :
    ∀ (acc : List FlatEntry) {a : Bytes.Address} {sp : List KExpr} {us : List KLevel}
      {xflat xa xsp xus r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelModeled::aux_entry_in" [xflat, xa, xsp, xus] h r h' cs →
      Bounded cs →
      RepList flatListEnum (FlatEntryRepExact κ) h acc xflat →
      Bytes.RepAddressRef addrTy h a xa →
      RepList kexprListEnum (TmOExact κ) h sp xsp →
      RepKLevelList h us xus →
      r = .field (if auxEntryIn acc (ixAddr a) sp us then 1 else 0) := by
  intro acc
  induction acc with
  | nil =>
    intro a sp us xflat xa xsp xus r h h' cs ev _ hacc _ _ _
    match Obs.«KernelModeled::aux_entry_in».obs ev with
    | .Nil (he20 := hr0) .. => cases hr0; rfl
    | .Cons_n1_n1 (ld12 := ld) .. | .Cons_n1_other (ld12 := ld) ..
    | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hacc ld
      cases hcons
  | cons e rest ih =>
    intro a sp us xflat xa xsp xus r h h' cs ev hbnd hacc ra hsp hus
    have bnd : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelModeled::aux_entry_in».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hacc ld
    | .Cons_n1_n1 (x_a := xea) (x_is_aux := xaux) (x_s := xes) (x_u := xeu)
        (ld12 := ld) (ev99 := evaeq) (op92 := op1) (ev_caflkvhk := evsp)
        (ev164 := evus) (op136 := op2) (he185 := hr0) (hc187 := hc) .. =>
      cases hr0
      obtain ⟨e', rest', h1, he', -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hacc ld
      injection h1 with h1e h1r; subst h1e h1r
      obtain ⟨xea', xes', xeu', ae, htup, rae, hae, hspe, huse⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4; subst h1 h2 h3 h4
      obtain ⟨hv1, rfl⟩ := Lib.address_eq_spec evaeq rae ra
      have haux_t : e.aux = true ∧ ae = a := by
        rw [hv1] at op1
        cases h1 : e.aux <;> by_cases h2 : ae = a <;>
          simp [auxVal, h1, h2, evalBinOp] at op1
        exact ⟨rfl, h2⟩
      obtain ⟨haux, rfl⟩ := haux_t
      have hsp_eq := spec_params_zeta_eq_exact hinj hspe hsp
        (bnd fun c hc' => by rw [hc]; simp [hc']) evsp
      obtain ⟨hus_eq, -⟩ := level_list_struct_eq_exact
        (huse.mono evsp.heap_extends) (hus.mono evsp.heap_extends) evus
      have hsu : e.params = sp ∧ e.levels = us := by
        by_cases h1 : e.params = sp <;> by_cases h2 : e.levels = us
        · exact ⟨h1, h2⟩
        all_goals
          rw [hsp_eq, hus_eq] at op2
          simp [h1, h2, evalBinOp] at op2
      simp [auxEntryIn, haux, hae, hsu.1, hsu.2]
    | .Cons_n1_other (x_a := xea) (x_is_aux := xaux) (x_s := xes) (x_u := xeu)
        (ld12 := ld) (ev99 := evaeq) (op92 := op1) (ev_caflkvhk := evsp)
        (ev164 := evus) (op136 := op2) (hne188 := hne) (ev197 := evrec) (hc230 := hc) .. =>
      obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hacc ld
      injection h1 with h1e h1r; subst h1e h1r
      obtain ⟨xea', xes', xeu', ae, htup, rae, hae, hspe, huse⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4; subst h1 h2 h3 h4
      obtain ⟨hv1, rfl⟩ := Lib.address_eq_spec evaeq rae ra
      have haux_t : e.aux = true ∧ ae = a := by
        rw [hv1] at op1
        cases h1 : e.aux <;> by_cases h2 : ae = a <;>
          simp [auxVal, h1, h2, evalBinOp] at op1
        exact ⟨rfl, h2⟩
      obtain ⟨haux, rfl⟩ := haux_t
      have hsp_eq := spec_params_zeta_eq_exact hinj hspe hsp
        (bnd fun c hc' => by rw [hc]; simp [hc']) evsp
      obtain ⟨hus_eq, rfl⟩ := level_list_struct_eq_exact
        (huse.mono evsp.heap_extends) (hus.mono evsp.heap_extends) evus
      have hne_su : (e.params == sp && e.levels == us) = false := by
        by_cases h1 : e.params = sp <;> by_cases h2 : e.levels = us
        · rw [hsp_eq, hus_eq] at op2; simp [h1, h2, evalBinOp] at op2; exact (hne op2.symm).elim
        · simp [beq_eq_false_iff_ne.mpr h2]
        · simp [beq_eq_false_iff_ne.mpr h1]
        · simp [beq_eq_false_iff_ne.mpr h1]
      have ext := evsp.heap_extends
      have hrec := ih evrec (bnd fun c hc' => by rw [hc]; simp [hc'])
        (flatList_mono ext hrest) (Bytes.repAddressRef_heapMono₂ addrTy ext ra)
        (tmOExactList_mono ext hsp) (hus.mono ext)
      rw [hrec]; simp [auxEntryIn, haux, hae, hne_su]
    | .Cons_other (x_a := xea) (x_is_aux := xaux) (x_s := xes) (x_u := xeu)
        (ld12 := ld) (ev99 := evaeq) (op92 := op1) (hne231 := hne) (ev240 := evrec)
        (hc273 := hc) .. =>
      obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hacc ld
      injection h1 with h1e h1r; subst h1e h1r
      obtain ⟨xea', xes', xeu', ae, htup, rae, hae, -, -⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4; subst h1 h2 h3 h4
      obtain ⟨hv1, rfl⟩ := Lib.address_eq_spec evaeq rae ra
      have hfail : (e.aux && e.addr == ixAddr a) = false := by
        cases h1 : e.aux
        · rfl
        · by_cases h2 : ae = a
          · subst h2; rw [hv1] at op1; simp [auxVal, h1, evalBinOp] at op1; exact (hne op1.symm).elim
          · have hne' : e.addr ≠ ixAddr a := by
              rw [← hae]; exact fun he => h2 (ixAddr_inj he)
            simp [beq_eq_false_iff_ne.mpr hne']
      have hrec := ih evrec (bnd fun c hc' => by rw [hc]; simp [hc']) hrest ra hsp hus
      rw [hrec]; simp [auxEntryIn, hfail]

/-- **`KernelModeled::add_block_members`** computes `addBlockMembers (ms.map (·.addr)) sp us acc`,
preserving length monotonicity, `Held R`, and `AddrIn (Held R)`. -/
theorem add_block_members_spec {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    (hinj : Function.Injective κ) :
    ∀ (ms acc : List FlatEntry) {sp : List KExpr} {us : List KLevel}
      {xm xsp xus xacc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelModeled::add_block_members" [xm, xsp, xus, xacc] h r h' cs →
      Bounded cs →
      RepList flatListEnum (FlatEntryRepExact κ) h ms xm →
      RepList kexprListEnum (TmOExact κ) h sp xsp →
      RepKLevelList h us xus →
      RepList flatListEnum (FlatEntryRepExact κ) h acc xacc →
      (∀ e ∈ ms, S e.addr) →
      (∀ p ∈ sp, AddrIn S κ p) →
      (∀ e ∈ acc, S e.addr ∧ ∀ p ∈ e.params, AddrIn S κ p) →
      RepList flatListEnum (FlatEntryRepExact κ) h'
        (addBlockMembers (ms.map (·.addr)) sp us acc) r ∧
      acc.length ≤ (addBlockMembers (ms.map (·.addr)) sp us acc).length ∧
      (∀ e ∈ addBlockMembers (ms.map (·.addr)) sp us acc,
        S e.addr ∧ ∀ p ∈ e.params, AddrIn S κ p) := by
  intro ms
  induction ms with
  | nil =>
    intro acc sp us xm xsp xus xacc r h h' cs ev _ hms _ _ hacc _ _ haccS
    match Obs.«KernelModeled::add_block_members».obs ev with
    | .Nil (he21 := hr0) (he22 := hh0) .. => cases hr0; cases hh0; exact ⟨hacc, Nat.le_refl _, haccS⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hms ld
      cases hcons
  | cons m rest ih =>
    intro acc sp us xm xsp xus xacc r h h' cs ev hbnd hms hsp hus hacc hmsS hspIn haccS
    have bnd : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelModeled::add_block_members».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hms ld
    | .Cons (x_rest := xrest) (x_maddr := xmaddr) (v194 := vacc') (m195 := m1)
        (cs197 := cs1) (cs206 := cs2) (ld12 := ld) (sg202 := sg) (ev208 := evrec)
        (hc241 := hc) .. =>
      obtain ⟨m', rest', h1, hm', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hms ld
      injection h1 with h1m h1r; subst h1m h1r
      obtain ⟨xmaddr', _, _, ma, htup, rma, hma, -, -⟩ := hm'
      injection htup with hl; injection hl with h1 _; subst h1
      have hstep : ∃ ext : Heap.Extends h m1,
          RepList flatListEnum (FlatEntryRepExact κ) m1
            (if auxEntryIn acc m.addr sp us then acc else acc ++ [⟨m.addr, true, sp, us⟩])
            vacc' := by
        cases sg with
        | n1 m81 cs92 evin hr hh hcs =>
          subst hr hh
          have hin := aux_entry_in_spec hinj acc evin
            (bnd fun c hc' => by rw [hc, hcs]; simp [hc']) hacc rma hsp hus
          rw [hma] at hin
          cases hcond : auxEntryIn acc m.addr sp us
          · rw [hcond] at hin; exact absurd (Value.field.inj hin) (by decide)
          · exact ⟨evin.heap_extends, flatList_mono evin.heap_extends hacc⟩
        | other v80 m81 cs92 cs142 evin hne evsn hcs =>
          have hin := aux_entry_in_spec hinj acc evin
            (bnd fun c hc' => by rw [hc, hcs]; simp [hc']) hacc rma hsp hus
          rw [hma] at hin
          cases hcond : auxEntryIn acc m.addr sp us
          · have ext1 := evin.heap_extends
            have hentry : FlatEntryRepExact κ m81 ⟨m.addr, true, sp, us⟩
                (.tuple [xmaddr, .field 1, xsp, xus]) :=
              ⟨xmaddr, xsp, xus, ma, rfl, Bytes.repAddressRef_heapMono₂ addrTy ext1 rma, hma,
                tmOExactList_mono ext1 hsp, hus.mono ext1⟩
            have hsn := flat_snoc_spec evsn (flatList_mono ext1 hacc) hentry
            exact ⟨ext1.trans evsn.heap_extends, hsn⟩
          · rw [hcond] at hin; exact (hne hin).elim
      obtain ⟨ext1, hacc'⟩ := hstep
      let acc1 := if auxEntryIn acc m.addr sp us then acc else acc ++ [⟨m.addr, true, sp, us⟩]
      have hlen1 : acc.length ≤ acc1.length := by
        dsimp only [acc1]; split <;> simp
      have hacc1S : ∀ e ∈ acc1, S e.addr ∧ ∀ p ∈ e.params, AddrIn S κ p := by
        intro e he; dsimp only [acc1] at he
        split at he
        · exact haccS e he
        · simp only [List.mem_append, List.mem_singleton] at he
          rcases he with hm | rfl
          · exact haccS e hm
          · exact ⟨hmsS m (List.mem_cons_self ..), hspIn⟩
      obtain ⟨hrep_f, hlen_f, hfS⟩ := ih acc1 evrec
        (bnd fun c hc' => by rw [hc]; simp [hc'])
        (flatList_mono ext1 hrest) (tmOExactList_mono ext1 hsp) (hus.mono ext1) hacc'
        (fun e he => hmsS e (List.mem_cons_of_mem _ he)) hspIn hacc1S
      exact ⟨hrep_f, hlen1.trans hlen_f, hfS⟩

/-! ## `occ_scan`, `occ_scan_list`, `inst_ctor_params`, `ctors_scan`, `nested_walk`, `check_nested_aux` -/

/-- Ancestor binder chain invariant for `KernelModeled::occ_scan`: each entry `(addr, sz)` records
a valid ROM address whose represented `TmOExact` term has `exprSize = sz`, strictly larger than
the current term's `exprSize`. Pairwise distinctness of `addr`s bounds binder depth `d ≤ 2^39`. -/
private def OccSeen (rom : ROM F) (κ : _root_.Address → KKey) (E : KExpr)
    (seen : List (F × Nat)) : Prop :=
  (seen.map Prod.fst).Nodup ∧
  (∀ p ∈ seen, ∃ v, (p.1, v) ∈ rom.entries) ∧
  (∀ p ∈ seen, ∀ (h_x : Heap F) (E_x : KExpr) (px : SourceValue F),
    Represents rom h_x px (.ptr (.enum kexprEnum) p.1) →
    TmOExact κ h_x E_x px → exprSize E_x = p.2) ∧
  (∀ p ∈ seen, exprSize E < p.2)

private theorem occSeen_lt {rom : ROM F} {κ : _root_.Address → KKey} {E E' : KExpr}
    {seen : List (F × Nat)} (hs : OccSeen rom κ E seen) (hlt : exprSize E' < exprSize E) :
    OccSeen rom κ E' seen :=
  ⟨hs.1, hs.2.1, hs.2.2.1, fun p hp => Nat.lt_trans hlt (hs.2.2.2 p hp)⟩

private theorem occSeen_cons {rom : ROM F} (hvalid : rom.Valid) {κ : _root_.Address → KKey}
    {h : Heap F} {E B : KExpr} {xe : SourceValue F} {w : Value F} {seen : List (F × Nat)}
    (hs : OccSeen rom κ E seen) (hE : TmOExact κ h E xe) (hrep : Represents rom h xe w)
    (hlt : exprSize B < exprSize E) :
    ∃ addr, OccSeen rom κ B ((addr, exprSize E) :: seen) := by
  obtain ⟨addr, enc, hmem, rfl⟩ := represents_ptr_of_tmOExact hE hrep
  refine ⟨addr, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hin => ?_, hs.1⟩
    obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hin
    have hsz := hs.2.2.1 p hp h E xe (by rw [hpeq]; exact hrep) hE
    have hlt' := hs.2.2.2 p hp
    omega
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨enc, hmem⟩
    · exact hs.2.1 p hp
  · intro p hp h_x E_x px hrx hEx
    rcases List.mem_cons.mp hp with rfl | hp
    · exact exprSize_eq_of_represents hvalid hrx hrep hEx hE
    · exact hs.2.2.1 p hp h_x E_x px hrx hEx
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hlt
    · exact Nat.lt_trans hlt (hs.2.2.2 p hp)

private theorem occSeen_length_le {rom : ROM F} {κ : _root_.Address → KKey} {E : KExpr}
    {seen : List (F × Nat)} (hbound : ROMAddressesAtMost rom (2 ^ 39))
    (hs : OccSeen rom κ E seen) : seen.length ≤ 2 ^ 39 := by
  have h1 := RomBound.length_le_of_nodup hbound hs.1 (fun a ha => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact hs.2.1 p hp)
  simpa using h1

mutual

/-- **`KernelModeled::occ_scan`** refines `occScanF (FlatView.ofStore t E₀) B fuel E d acc` for
every `fuel > exprSize E`, without any external depth premise (depth `d ≤ 2^39` is proved from
`rom.Valid` + `ROMAddressesAtMost rom (2^39)` via `OccSeen`). -/
private theorem occ_scan_aux {rootCalls : List (Call F)} {rom : ROM F}
    {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls) (hvalid : rom.Valid) (hbound : ROMAddressesAtMost rom (2 ^ 39))
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c') (hcl : UsedClosed R)
    {ba : Bytes.Address} {E : KExpr} {d : Nat} {acc : List FlatEntry}
    {seen : List (F × Nat)}
    {xblk xe xacc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls) (hcar : CallsInROM rom cs)
    (hrep : ∃ w, Represents rom h xe w) (hseen : OccSeen rom (Core.keyOf t) E seen)
    (hd_eq : seen.length = d)
    (rba : Bytes.RepAddressRef addrTy h ba xblk)
    (hE : TmOExact (Core.keyOf t) h E xe) (hEin : AddrIn (Held R) (Core.keyOf t) E)
    (hacc : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h acc xacc)
    (haccS : ∀ e ∈ acc, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p)
    (ev : ObsFn W "KernelModeled::occ_scan" [xblk, xe, .field (d : F), xacc] h r h' cs) :
    ∃ res : List FlatEntry,
      (∀ fuel, exprSize E < fuel →
        occScanF (FlatView.ofStore t E₀) (ixAddr ba) fuel E d acc = some res) ∧
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h' res r ∧
      acc.length ≤ res.length ∧
      (∀ e ∈ res, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) := by
  have hd_le : d ≤ 2 ^ 39 := hd_eq ▸ occSeen_length_le hbound hseen
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → ∀ c ∈ cs', c ∈ rootCalls :=
    fun hs c hc => hsub c (hs c hc)
  have car : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → CallsInROM rom cs' :=
    fun hs c hc => hcar c (hs c hc)
  have bnd_sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
    fun hs => RomBound.bounded_mono hbd (sub hs)
  have hinj : Function.Injective (Core.keyOf t) := fun _ _ he => Core.keyOf_inj hwf he
  have mkBlks : ∀ (m26 m2 : Heap F),
      m26 = h ++ [.construct addrListEnum "Nil" []] →
      m2 = m26 ++ [.construct addrListEnum "Cons" [xblk, .ptr (.enum addrListEnum) h.length]] →
      Heap.Extends h m2 ∧
      RepList addrListEnum (Bytes.RepAddressRef addrTy) m2 [ba]
        (.ptr (.enum addrListEnum) m26.length) := by
    intro m26 m2 hm26 hm2
    subst hm26 hm2
    have ext1 : Heap.Extends h (h ++ [.construct addrListEnum "Nil" []]) := Heap.Extends.snoc _ _
    have ext2 : Heap.Extends (h ++ [.construct addrListEnum "Nil" []])
        ((h ++ [.construct addrListEnum "Nil" []]) ++
          [.construct addrListEnum "Cons" [xblk, .ptr (.enum addrListEnum) h.length]]) :=
      Heap.Extends.snoc _ _
    have hnil : RepList addrListEnum (Bytes.RepAddressRef addrTy)
        (h ++ [.construct addrListEnum "Nil" []]) [] (.ptr (.enum addrListEnum) h.length) :=
      Lib.rep_store_nil h
    exact ⟨ext1.trans ext2,
      Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ addrTy)
        (Bytes.repAddressRef_heapMono₂ addrTy ext1 rba) hnil⟩
  match Obs.«KernelModeled::occ_scan».obs ev with
  | .n0 (m2 := m2) (m26 := m26) (cs_ejheattv := cs1) (hm12 := hm12) (hm34 := hm34)
      (ev_yanxknqt := evm) (he74 := hr0) (he75 := hh0) (hc76 := hc) .. =>
    cases hr0; cases hh0
    obtain ⟨ext02, rblks⟩ := mkBlks m26 m2 hm34 hm12
    obtain ⟨b, hb, hr⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) (hE.mono ext02) hEin rblks evm
    cases b with
    | true => exact absurd (Value.field.inj hr) (by decide)
    | false =>
      refine ⟨acc, fun fuel hfl => ?_, flatList_mono (ext02.trans evm.heap_extends) hacc,
        Nat.le_refl _, haccS⟩
      obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
      simp [occScanF, hb]
  | .other_App_Const_Induct_n1 (m2 := m2) (m26 := m26) (m39 := m3) (cs_ejheattv := cs1)
      (m113 := m4) (cs_lffdlqmw := cs2) (x_head := xhd) (x_args := xargs)
      (x_c := xc) (x_us := xus) (m177 := m5) (p185 := pci) (cs191 := cs3)
      (x_cnp := xcnp) (x_cblk := xcblk) (m396 := m6) (cs398 := cs4) (cs421 := cs8)
      (v424 := vorig) (v425 := vsp) (m429 := m7) (cs437 := cs5) (m456 := m9) (cs464 := cs7)
      (v467 := vtake) (m470 := m8) (cs478 := cs6)
      (hm12 := hm12) (hm34 := hm34) (ev_yanxknqt := evm) (hne77 := hne0)
      (ld92 := ldapp) (ev_catkzrqk := evsp) (ld158 := ldh) (ev193 := evci) (ld187 := ldci)
      (sg403 := sg) (ev439 := evorig) (ev480 := evtake) (ev466 := evlow) (ev423 := evadd)
      (hc518 := hc) .. =>
    obtain ⟨ext02, rblks⟩ := mkBlks m26 m2 hm34 hm12
    obtain ⟨bm, hbm, hrm⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) (hE.mono ext02) hEin rblks evm
    cases bm with
    | false => exact (hne0 hrm).elim
    | true =>
      have ext03 := ext02.trans evm.heap_extends
      obtain ⟨Ef, Ea, hE_app, -, -⟩ := TmOExact.app_of_load (hE.mono ext03) ldapp
      obtain ⟨hfn, -, hargs⟩ := collect_spine_zeta_spec (hE.mono ext03)
        (bnd_sub fun c hc' => by rw [hc]; simp [hc']) evsp
      obtain ⟨ca, us, hfn_eq, rca, rus⟩ := TmOExact.const_of_load hfn ldh
      have hfnIn : AddrIn (Held R) (Core.keyOf t) E.getAppFn := addrIn_getAppFn hEin
      rw [hfn_eq] at hfnIn
      have hSca : Held R (ixAddr ca) := hfnIn (ixAddr ca) rfl
      have hargsIn : ∀ x ∈ E.getAppArgs, AddrIn (Held R) (Core.keyOf t) x := addrIn_getAppArgs hEin
      obtain ⟨hInd, -⟩ := indInfo_of_get_ci hS hH hbd hRagree hcl
        (sub fun c hc' => by rw [hc]; simp [hc']) hSca rca evci ldci
      obtain ⟨info, cba, hinfo, -, hnp56, -, -, hSblk, -, hnpEq, -, hcba, rcba, -⟩ :=
        hInd _ _ _ _ _ _ _ _ rfl
      subst hnpEq
      have ext04 := ext03.trans evsp.heap_extends
      have ext05 := ext04.trans evci.heap_extends
      have rba5 := Bytes.repAddressRef_heapMono₂ addrTy ext05 rba
      have rblks5 := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
        (evm.heap_extends.trans (evsp.heap_extends.trans evci.heap_extends)) rblks
      have hargs5 := tmOExactList_mono evci.heap_extends hargs
      -- Analyze `sg : Seg1` returning `1`: must be `other_other` with `nestedAt = some true`!
      have hnest : nestedAt (FlatView.ofStore t E₀) (ixAddr ba) info E.getAppArgs = some true ∧
          Heap.Extends m5 m6 := by
        cases sg with
        | n1 _ _ _ hr _ _ => exact absurd (Value.field.inj hr) (by decide)
        | other_n1 _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ => exact absurd (Value.field.inj hr) (by decide)
        | other_other v254 m255 cs266 v296 m297 cs308 v311 m314 cs322 cs_am vq m360 cs368
            evaeq hne1 evlen evlt hne2 evtk evam hcs =>
          obtain ⟨hveq, rfl⟩ := Lib.address_eq_spec evaeq rcba rba5
          have hblk_ne : info.blk ≠ ixAddr ba := fun h => by
            have : cba = ba := ixAddr_inj (hcba.trans h)
            rw [ite_eq_left this] at hveq; exact hne1 hveq
          obtain ⟨rfl, rfl⟩ := kexpr_length_spec evlen hargs5
          have hlen_lt : E.getAppArgs.length < 2 ^ 39 :=
            repList_length_lt_of_obs hbd hsub evlen (by rw [hc, hcs]; simp) (by simp) hargs5
          obtain ⟨-, -, hlt_iff, -, rfl⟩ := Lib.less_than_fields_field evlt
          have hge : ¬ (E.getAppArgs.length < info.np) := fun h => by
            have h1 : ((E.getAppArgs.length : F)).val < ((info.np : F)).val := by
              rw [fval_natCast (by omega), fval_natCast (by omega)]; exact h
            exact hne2 (hlt_iff.mpr h1)
          obtain ⟨-, htk⟩ := kexpr_take_spec evtk hargs5
          rw [fval_natCast (by omega)] at htk
          have rblks_tk := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
            evtk.heap_extends rblks5
          obtain ⟨bam, hbam, hram⟩ := occ_any_mentions_block_spec hwf hS hH hbd hRagree hcl _
            (sub fun c hc' => by rw [hc, hcs]; simp [hc']) htk
            (fun x hx => hargsIn x (List.mem_of_mem_take hx)) rblks_tk evam
          cases bam with
          | false => exact absurd (Value.field.inj hram) (by decide)
          | true =>
            have hbf : (info.blk == ixAddr ba || decide (E.getAppArgs.length < info.np)) = false := by
              simp [beq_eq_false_iff_ne.mpr hblk_ne, hge]
            exact ⟨by simp [nestedAt, hbf, hbam], evtk.heap_extends.trans evam.heap_extends⟩
      obtain ⟨hnested, ext56⟩ := hnest
      -- `info.blk` is a `Muts` block from `indInfoAt E₀ (ixAddr ca) = some (some info)`
      have hblk_muts : ∃ cb ms, recordOf E₀ info.blk = some cb ∧ cb.info = .muts ms := by
        unfold indInfoAt at hinfo
        cases hrc : recordOf E₀ (ixAddr ca) with
        | none => simp [hrc] at hinfo
        | some c =>
          rw [hrc] at hinfo
          cases hci : c.info with
          | iPrj p =>
            simp only [hci] at hinfo
            cases hcb' : recordOf E₀ p.block with
            | none => simp [hcb'] at hinfo
            | some cb =>
              rw [hcb'] at hinfo
              cases hcbi : cb.info with
              | muts ms =>
                simp only [hcbi] at hinfo
                cases hms' : ms[p.idx.toNat]? with
                | none => simp [hms'] at hinfo
                | some mc =>
                  cases mc with
                  | indc ind =>
                    simp only [hms', Option.some.injEq] at hinfo
                    subst hinfo; exact ⟨cb, ms, hcb', hcbi⟩
                  | _ => simp [hms'] at hinfo
              | _ => simp [hcbi] at hinfo
          | _ => simp [hci] at hinfo
      obtain ⟨cb, ms, hcbE, hcbMuts⟩ := hblk_muts
      have evorig' : ObsFn W "KernelCheck::build_flat_originals"
          [xcblk, .field ((0 : Nat) : F)] m6 vorig m7 cs5 := by simpa using evorig
      obtain ⟨os, -, hrep_os, hos_addrs, hos_props⟩ := build_flat_originals_muts_spec hS hH hbd
        hRagree hcl (by decide) (sub fun c hc' => by rw [hc]; simp [hc'])
        (hcba.symm ▸ hSblk) (hcba.symm ▸ hcbE) hcbMuts
        (Bytes.repAddressRef_heapMono₂ addrTy ext56 rcba) evorig'
      have hargs7 := tmOExactList_mono (ext56.trans evorig.heap_extends) hargs5
      obtain ⟨-, htk⟩ := kexpr_take_spec evtake hargs7
      rw [fval_natCast (by omega)] at htk
      obtain ⟨sp, hsp, hrep_sp, hspIn⟩ := occ_params_lower_spec (by omega)
        (E.getAppArgs.take info.np) evlow (bnd_sub fun c hc' => by rw [hc]; simp [hc']) htk
        (fun x hx => hargsIn x (List.mem_of_mem_take hx))
      have ext_o_l := evorig.heap_extends.trans (evtake.heap_extends.trans evlow.heap_extends)
      have ext_5_l := ext56.trans ext_o_l
      obtain ⟨hrep_res, hlen_res, hresS⟩ := add_block_members_spec hinj os acc evadd
        (bnd_sub fun c hc' => by rw [hc]; simp [hc'])
        (flatList_mono (evtake.heap_extends.trans evlow.heap_extends) hrep_os)
        hrep_sp (rus.mono (evci.heap_extends.trans ext_5_l))
        (flatList_mono (ext05.trans ext_5_l) hacc)
        (fun e he => (hos_props e he).2.2.1) hspIn haccS
      have hmemAt : membersAt E₀ info.blk = some (indcAddrs info.blk 0 ms.toList) := by
        simp [membersAt, hcbE, hcbMuts]
      have hka : keyAddr t (Core.keyOf t (ixAddr ca)) = some (ixAddr ca) :=
        addrOf_ofStore (E₀ := E₀) hwf (ixAddr ca)
      rw [hos_addrs, hcba] at hrep_res hlen_res hresS
      refine ⟨addBlockMembers (indcAddrs info.blk 0 ms.toList) sp us acc,
        fun fuel hfl => ?_, hrep_res, hlen_res, hresS⟩
      obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
      simp only [occScanF, hbm]
      rw [hE_app]
      simp only [← hE_app, appCase, constOf, hfn_eq]
      change (match keyAddr t (Core.keyOf t (ixAddr ca)) with
        | none => none
        | some a => match indInfoAt E₀ a with
          | none => none
          | some none => scanList (fun x a => occScanF (FlatView.ofStore t E₀) (ixAddr ba) n x d a)
              E.getAppArgs acc
          | some (some info) => match nestedAt (FlatView.ofStore t E₀) (ixAddr ba) info E.getAppArgs with
            | none => none
            | some false => scanList (fun x a => occScanF (FlatView.ofStore t E₀) (ixAddr ba) n x d a)
                E.getAppArgs acc
            | some true => match membersAt E₀ info.blk with
              | none => none
              | some ms => match occParamsLower (E.getAppArgs.take info.np) d with
                | none => none
                | some sp => some (addBlockMembers ms sp us acc)) = some _
      rw [hka]; dsimp only
      rw [hinfo]; dsimp only
      rw [hnested]; dsimp only
      rw [hmemAt]; dsimp only
      rw [hsp]
  | .other_App_Const_Induct_other (m2 := m2) (m26 := m26) (m39 := m3) (cs_ejheattv := cs1)
      (m113 := m4) (cs_lffdlqmw := cs2) (x_head := xhd) (x_args := xargs)
      (x_c := xc) (x_us := xus) (m177 := m5) (p185 := pci) (cs191 := cs3)
      (x_cnp := xcnp) (x_cblk := xcblk) (m396 := m6) (cs398 := cs4) (cs526 := cs5)
      (hm12 := hm12) (hm34 := hm34) (ev_yanxknqt := evm) (hne77 := hne0)
      (ld92 := ldapp) (ev_catkzrqk := evsp) (ld158 := ldh) (ev193 := evci) (ld187 := ldci)
      (sg403 := sg) (hne519 := hne1) (ev528 := evlist) (hc561 := hc) .. =>
    obtain ⟨ext02, rblks⟩ := mkBlks m26 m2 hm34 hm12
    obtain ⟨bm, hbm, hrm⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) (hE.mono ext02) hEin rblks evm
    cases bm with
    | false => exact (hne0 hrm).elim
    | true =>
      have ext03 := ext02.trans evm.heap_extends
      obtain ⟨Ef, Ea, hE_app, -, -⟩ := TmOExact.app_of_load (hE.mono ext03) ldapp
      obtain ⟨hfn, -, hargs⟩ := collect_spine_zeta_spec (hE.mono ext03)
        (bnd_sub fun c hc' => by rw [hc]; simp [hc']) evsp
      obtain ⟨ca, us, hfn_eq, rca, -⟩ := TmOExact.const_of_load hfn ldh
      have hfnIn : AddrIn (Held R) (Core.keyOf t) E.getAppFn := addrIn_getAppFn hEin
      rw [hfn_eq] at hfnIn
      have hSca : Held R (ixAddr ca) := hfnIn (ixAddr ca) rfl
      have hargsIn : ∀ x ∈ E.getAppArgs, AddrIn (Held R) (Core.keyOf t) x := addrIn_getAppArgs hEin
      obtain ⟨hInd, -⟩ := indInfo_of_get_ci hS hH hbd hRagree hcl
        (sub fun c hc' => by rw [hc]; simp [hc']) hSca rca evci ldci
      obtain ⟨info, cba, hinfo, -, hnp56, -, -, -, -, hnpEq, -, hcba, rcba, -⟩ :=
        hInd _ _ _ _ _ _ _ _ rfl
      subst hnpEq
      have ext04 := ext03.trans evsp.heap_extends
      have ext05 := ext04.trans evci.heap_extends
      have rba5 := Bytes.repAddressRef_heapMono₂ addrTy ext05 rba
      have rblks5 := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
        (evm.heap_extends.trans (evsp.heap_extends.trans evci.heap_extends)) rblks
      have hargs5 := tmOExactList_mono evci.heap_extends hargs
      have hnotnest : nestedAt (FlatView.ofStore t E₀) (ixAddr ba) info E.getAppArgs = some false ∧
          Heap.Extends m5 m6 := by
        cases sg with
        | n1 m255 cs266 evaeq hr hh _ =>
          subst hh
          obtain ⟨hveq, rfl⟩ := Lib.address_eq_spec evaeq rcba rba5
          have hblk_eq : info.blk = ixAddr ba := by
            by_contra hne'
            have : cba ≠ ba := fun h => hne' (hcba.symm.trans (congrArg ixAddr h))
            rw [ite_eq_right this] at hveq; exact absurd (Value.field.inj hveq) (by decide)
          exact ⟨by simp [nestedAt, hblk_eq], Heap.Extends.refl _⟩
        | other_n1 v254 m255 cs266 m297 cs308 v311 m314 cs322 evaeq hne' evlen evlt hr hh hcs =>
          subst hh
          obtain ⟨-, rfl⟩ := Lib.address_eq_spec evaeq rcba rba5
          obtain ⟨rfl, rfl⟩ := kexpr_length_spec evlen hargs5
          have hlen_lt : E.getAppArgs.length < 2 ^ 39 :=
            repList_length_lt_of_obs hbd hsub evlen (by rw [hc, hcs]; simp) (by simp) hargs5
          obtain ⟨-, -, hlt_iff, -, rfl⟩ := Lib.less_than_fields_field evlt
          have hlt_np : E.getAppArgs.length < info.np := by
            have h1 := hlt_iff.mp rfl
            rwa [fval_natCast (by omega), fval_natCast (by omega)] at h1
          exact ⟨by simp [nestedAt, hlt_np], Heap.Extends.refl _⟩
        | other_other v254 m255 cs266 v296 m297 cs308 v311 m314 cs322 cs_am vq m360 cs368
            evaeq hne' evlen evlt hne2 evtk evam hcs =>
          obtain ⟨hveq, rfl⟩ := Lib.address_eq_spec evaeq rcba rba5
          have hblk_ne : info.blk ≠ ixAddr ba := fun h => by
            have : cba = ba := ixAddr_inj (hcba.trans h)
            rw [ite_eq_left this] at hveq; exact hne' hveq
          obtain ⟨rfl, rfl⟩ := kexpr_length_spec evlen hargs5
          have hlen_lt : E.getAppArgs.length < 2 ^ 39 :=
            repList_length_lt_of_obs hbd hsub evlen (by rw [hc, hcs]; simp) (by simp) hargs5
          obtain ⟨-, -, hlt_iff, -, rfl⟩ := Lib.less_than_fields_field evlt
          have hge : ¬ (E.getAppArgs.length < info.np) := fun h => by
            have h1 : ((E.getAppArgs.length : F)).val < ((info.np : F)).val := by
              rw [fval_natCast (by omega), fval_natCast (by omega)]; exact h
            exact hne2 (hlt_iff.mpr h1)
          obtain ⟨-, htk⟩ := kexpr_take_spec evtk hargs5
          rw [fval_natCast (by omega)] at htk
          have rblks_tk := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
            evtk.heap_extends rblks5
          obtain ⟨bam, hbam, hram⟩ := occ_any_mentions_block_spec hwf hS hH hbd hRagree hcl _
            (sub fun c hc' => by rw [hc, hcs]; simp [hc']) htk
            (fun x hx => hargsIn x (List.mem_of_mem_take hx)) rblks_tk evam
          cases bam with
          | true => exact (hne1 hram).elim
          | false =>
            have hbf : (info.blk == ixAddr ba || decide (E.getAppArgs.length < info.np)) = false := by
              simp [beq_eq_false_iff_ne.mpr hblk_ne, hge]
            exact ⟨by simp [nestedAt, hbf, hbam], evtk.heap_extends.trans evam.heap_extends⟩
      obtain ⟨hnn, ext56⟩ := hnotnest
      have ext06 := ext05.trans ext56
      have hlt : cs5.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      obtain ⟨res, hres, hrep_res, hlen_res, hresS⟩ := occ_scan_list_aux hwf hS hH hbd hvalid
        hbound hRagree hcl (sub fun c hc' => by rw [hc]; simp [hc'])
        (car fun c hc' => by rw [hc]; simp [hc'])
        (fun x hx => occSeen_lt hseen (exprSize_getAppArgs_lt E x hx)) hd_eq
        (Bytes.repAddressRef_heapMono₂ addrTy ext06 rba)
        (tmOExactList_mono ext56 hargs5) hargsIn (flatList_mono ext06 hacc) haccS evlist
      have hka : keyAddr t (Core.keyOf t (ixAddr ca)) = some (ixAddr ca) :=
        addrOf_ofStore (E₀ := E₀) hwf (ixAddr ca)
      refine ⟨res, fun fuel hfl => ?_, hrep_res, hlen_res, hresS⟩
      obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
      simp only [occScanF, hbm]
      rw [hE_app]
      simp only [← hE_app, appCase, constOf, hfn_eq]
      change (match keyAddr t (Core.keyOf t (ixAddr ca)) with
        | none => none
        | some a => match indInfoAt E₀ a with
          | none => none
          | some none => scanList (fun x a => occScanF (FlatView.ofStore t E₀) (ixAddr ba) n x d a)
              E.getAppArgs acc
          | some (some info) => match nestedAt (FlatView.ofStore t E₀) (ixAddr ba) info E.getAppArgs with
            | none => none
            | some false => scanList (fun x a => occScanF (FlatView.ofStore t E₀) (ixAddr ba) n x d a)
                E.getAppArgs acc
            | some true => match membersAt E₀ info.blk with
              | none => none
              | some ms => match occParamsLower (E.getAppArgs.take info.np) d with
                | none => none
                | some sp => some (addBlockMembers ms sp us acc)) = some res
      rw [hka]; dsimp only
      rw [hinfo]; dsimp only
      rw [hnn]; dsimp only
      exact hres n (fun x hx => Nat.lt_of_lt_of_le (exprSize_getAppArgs_lt E x hx) (by omega))
  | .other_App_Const_other (m2 := m2) (m26 := m26) (m39 := m3) (cs_ejheattv := cs1)
      (m113 := m4) (cs_lffdlqmw := cs2) (x_head := xhd) (x_args := xargs)
      (x_c := xc) (x_us := xus) (m177 := m5) (p185 := pci) (cs191 := cs3) (cs569 := cs4)
      (hm12 := hm12) (hm34 := hm34) (ev_yanxknqt := evm) (hne77 := hne0)
      (ld92 := ldapp) (ev_catkzrqk := evsp) (ld158 := ldh) (ev193 := evci) (ld187 := ldci)
      (hne562 := hneI) (ev571 := evlist) (hc604 := hc) .. =>
    obtain ⟨ext02, rblks⟩ := mkBlks m26 m2 hm34 hm12
    obtain ⟨bm, hbm, hrm⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) (hE.mono ext02) hEin rblks evm
    cases bm with
    | false => exact (hne0 hrm).elim
    | true =>
      have ext03 := ext02.trans evm.heap_extends
      obtain ⟨Ef, Ea, hE_app, -, -⟩ := TmOExact.app_of_load (hE.mono ext03) ldapp
      obtain ⟨hfn, -, hargs⟩ := collect_spine_zeta_spec (hE.mono ext03)
        (bnd_sub fun c hc' => by rw [hc]; simp [hc']) evsp
      obtain ⟨ca, us, hfn_eq, rca, -⟩ := TmOExact.const_of_load hfn ldh
      have hfnIn : AddrIn (Held R) (Core.keyOf t) E.getAppFn := addrIn_getAppFn hEin
      rw [hfn_eq] at hfnIn
      have hSca : Held R (ixAddr ca) := hfnIn (ixAddr ca) rfl
      have hargsIn : ∀ x ∈ E.getAppArgs, AddrIn (Held R) (Core.keyOf t) x := addrIn_getAppArgs hEin
      obtain ⟨-, hOther⟩ := indInfo_of_get_ci hS hH hbd hRagree hcl
        (sub fun c hc' => by rw [hc]; simp [hc']) hSca rca evci ldci
      have hinfo := hOther hneI
      have ext05 := ext03.trans (evsp.heap_extends.trans evci.heap_extends)
      have hlt : cs4.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      obtain ⟨res, hres, hrep_res, hlen_res, hresS⟩ := occ_scan_list_aux hwf hS hH hbd hvalid
        hbound hRagree hcl (sub fun c hc' => by rw [hc]; simp [hc'])
        (car fun c hc' => by rw [hc]; simp [hc'])
        (fun x hx => occSeen_lt hseen (exprSize_getAppArgs_lt E x hx)) hd_eq
        (Bytes.repAddressRef_heapMono₂ addrTy ext05 rba)
        (tmOExactList_mono evci.heap_extends hargs) hargsIn
        (flatList_mono ext05 hacc) haccS evlist
      have hka : keyAddr t (Core.keyOf t (ixAddr ca)) = some (ixAddr ca) :=
        addrOf_ofStore (E₀ := E₀) hwf (ixAddr ca)
      refine ⟨res, fun fuel hfl => ?_, hrep_res, hlen_res, hresS⟩
      obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
      simp only [occScanF, hbm]
      rw [hE_app]
      simp only [← hE_app, appCase, constOf, hfn_eq, FlatView.ofStore, hka, hinfo]
      exact hres n (fun x hx => Nat.lt_of_lt_of_le (exprSize_getAppArgs_lt E x hx) (by omega))
  | .other_App_other (m2 := m2) (m26 := m26) (m39 := m3) (cs_ejheattv := cs1)
      (m113 := m4) (cs_lffdlqmw := cs2) (x_head := xhd) (x_args := xargs) (cs612 := cs4)
      (v618 := vac1) (m641 := m5) (cs649 := cs3)
      (hm12 := hm12) (hm34 := hm34) (ev_yanxknqt := evm) (hne77 := hne0)
      (ld92 := ldapp) (ev_catkzrqk := evsp) (ld158 := ldh) (hne605 := hneC)
      (ev651 := evhd) (ev614 := evlist) (hc684 := hc) .. =>
    obtain ⟨ext02, rblks⟩ := mkBlks m26 m2 hm34 hm12
    obtain ⟨bm, hbm, hrm⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) (hE.mono ext02) hEin rblks evm
    cases bm with
    | false => exact (hne0 hrm).elim
    | true =>
      have ext03 := ext02.trans evm.heap_extends
      obtain ⟨Ef, Ea, hE_app, -, -⟩ := TmOExact.app_of_load (hE.mono ext03) ldapp
      obtain ⟨hfn, hnlh, hargs⟩ := collect_spine_zeta_spec (hE.mono ext03)
        (bnd_sub fun c hc' => by rw [hc]; simp [hc']) evsp
      have hfn_nc : constOf E.getAppFn = none := by
        cases h : E.getAppFn with
        | const ck cus => exact (tmOExact_not_const hfn hnlh ldh hneC ck cus h).elim
        | _ => rfl
      have ext04 := ext03.trans evsp.heap_extends
      have hfn_lt : exprSize E.getAppFn < exprSize E := by
        rw [hE_app]; exact exprSize_getAppFn_lt Ef Ea
      have hrep_hd : ∃ w, Represents rom m4 xhd w :=
        call_arg_rep_of_obs hcar evhd (by rw [hc]; simp) (by simp)
      have hlt1 : cs3.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      have hlt2 : cs4.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      obtain ⟨a1, ha1, hrep1, hlen1, ha1S⟩ := occ_scan_aux hwf hS hH hbd hvalid hbound hRagree hcl
        (sub fun c hc' => by rw [hc]; simp [hc']) (car fun c hc' => by rw [hc]; simp [hc'])
        hrep_hd (occSeen_lt hseen hfn_lt) hd_eq
        (Bytes.repAddressRef_heapMono₂ addrTy ext04 rba) hfn (addrIn_getAppFn hEin)
        (flatList_mono ext04 hacc) haccS evhd
      obtain ⟨res, hres, hrep_res, hlen_res, hresS⟩ := occ_scan_list_aux hwf hS hH hbd hvalid
        hbound hRagree hcl (sub fun c hc' => by rw [hc]; simp [hc'])
        (car fun c hc' => by rw [hc]; simp [hc'])
        (fun x hx => occSeen_lt hseen (exprSize_getAppArgs_lt E x hx)) hd_eq
        (Bytes.repAddressRef_heapMono₂ addrTy (ext04.trans evhd.heap_extends) rba)
        (tmOExactList_mono evhd.heap_extends hargs) (addrIn_getAppArgs hEin) hrep1 ha1S evlist
      refine ⟨res, fun fuel hfl => ?_, hrep_res, hlen1.trans hlen_res, hresS⟩
      obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
      simp only [occScanF, hbm]
      rw [hE_app]
      simp only [← hE_app, appCase, hfn_nc, ha1 n (by omega)]
      exact hres n (fun x hx => Nat.lt_of_lt_of_le (exprSize_getAppArgs_lt E x hx) (by omega))
  | .other_Lam (m2 := m2) (m26 := m26) (m39 := m3) (cs_ejheattv := cs1)
      (x_t := xt) (x_b := xb) (cs711 := cs3) (v716 := vd1) (v717 := vac1) (m748 := m4)
      (cs756 := cs2) (hm12 := hm12) (hm34 := hm34) (ev_yanxknqt := evm) (hne77 := hne0)
      (ld92 := ld) (op745 := op1) (ev758 := evt) (ev713 := evb) (hc791 := hc) .. =>
    obtain ⟨ext02, rblks⟩ := mkBlks m26 m2 hm34 hm12
    obtain ⟨bm, hbm, hrm⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) (hE.mono ext02) hEin rblks evm
    cases bm with
    | false => exact (hne0 hrm).elim
    | true =>
      have ext03 := ext02.trans evm.heap_extends
      obtain ⟨T, B, ℓ, hE_lam, hT, hB, -⟩ := TmOExact.lam_of_load (hE.mono ext03) ld
      subst hE_lam
      obtain rfl := binop_add_one_nat op1
      have hrep_t : ∃ w, Represents rom m3 xt w :=
        call_arg_rep_of_obs hcar evt (by rw [hc]; simp) (by simp)
      have hrep_b : ∃ w, Represents rom m4 xb w :=
        call_arg_rep_of_obs hcar evb (by rw [hc]; simp) (by simp)
      have hlt_t : exprSize T < exprSize (.lam T B (bmeta ℓ)) := by simp [exprSize]
      have hlt_b : exprSize B < exprSize (.lam T B (bmeta ℓ)) := by simp [exprSize]
      obtain ⟨w0, hr0⟩ := hrep
      obtain ⟨addr, hseen_b⟩ := occSeen_cons hvalid hseen hE hr0 hlt_b
      have hlt1 : cs2.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      have hlt2 : cs3.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      obtain ⟨a1, ha1, hrep1, hlen1, ha1S⟩ := occ_scan_aux hwf hS hH hbd hvalid hbound hRagree hcl
        (sub fun c hc' => by rw [hc]; simp [hc']) (car fun c hc' => by rw [hc]; simp [hc'])
        hrep_t (occSeen_lt hseen hlt_t) hd_eq
        (Bytes.repAddressRef_heapMono₂ addrTy ext03 rba) hT hEin.1
        (flatList_mono ext03 hacc) haccS evt
      obtain ⟨res, hres, hrep_res, hlen_res, hresS⟩ := occ_scan_aux hwf hS hH hbd hvalid hbound
        hRagree hcl (sub fun c hc' => by rw [hc]; simp [hc'])
        (car fun c hc' => by rw [hc]; simp [hc'])
        hrep_b hseen_b (by simp [hd_eq])
        (Bytes.repAddressRef_heapMono₂ addrTy (ext03.trans evt.heap_extends) rba)
        (hB.mono evt.heap_extends) hEin.2 hrep1 ha1S evb
      refine ⟨res, fun fuel hfl => ?_, hrep_res, hlen1.trans hlen_res, hresS⟩
      obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
      simp only [occScanF, hbm, ha1 n (by omega), hres n (by omega)]
  | .other_Forall (m2 := m2) (m26 := m26) (m39 := m3) (cs_ejheattv := cs1)
      (x_t := xt) (x_b := xb) (cs818 := cs3) (v823 := vd1) (v824 := vac1) (m855 := m4)
      (cs863 := cs2) (hm12 := hm12) (hm34 := hm34) (ev_yanxknqt := evm) (hne77 := hne0)
      (ld92 := ld) (op852 := op1) (ev865 := evt) (ev820 := evb) (hc898 := hc) .. =>
    obtain ⟨ext02, rblks⟩ := mkBlks m26 m2 hm34 hm12
    obtain ⟨bm, hbm, hrm⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) (hE.mono ext02) hEin rblks evm
    cases bm with
    | false => exact (hne0 hrm).elim
    | true =>
      have ext03 := ext02.trans evm.heap_extends
      obtain ⟨T, B, ℓ, hE_all, hT, hB, -⟩ := TmOExact.forallE_of_load (hE.mono ext03) ld
      subst hE_all
      obtain rfl := binop_add_one_nat op1
      have hrep_t : ∃ w, Represents rom m3 xt w :=
        call_arg_rep_of_obs hcar evt (by rw [hc]; simp) (by simp)
      have hrep_b : ∃ w, Represents rom m4 xb w :=
        call_arg_rep_of_obs hcar evb (by rw [hc]; simp) (by simp)
      have hlt_t : exprSize T < exprSize (.forallE T B (bmeta ℓ)) := by simp [exprSize]
      have hlt_b : exprSize B < exprSize (.forallE T B (bmeta ℓ)) := by simp [exprSize]
      obtain ⟨w0, hr0⟩ := hrep
      obtain ⟨addr, hseen_b⟩ := occSeen_cons hvalid hseen hE hr0 hlt_b
      have hlt1 : cs2.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      have hlt2 : cs3.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      obtain ⟨a1, ha1, hrep1, hlen1, ha1S⟩ := occ_scan_aux hwf hS hH hbd hvalid hbound hRagree hcl
        (sub fun c hc' => by rw [hc]; simp [hc']) (car fun c hc' => by rw [hc]; simp [hc'])
        hrep_t (occSeen_lt hseen hlt_t) hd_eq
        (Bytes.repAddressRef_heapMono₂ addrTy ext03 rba) hT hEin.1
        (flatList_mono ext03 hacc) haccS evt
      obtain ⟨res, hres, hrep_res, hlen_res, hresS⟩ := occ_scan_aux hwf hS hH hbd hvalid hbound
        hRagree hcl (sub fun c hc' => by rw [hc]; simp [hc'])
        (car fun c hc' => by rw [hc]; simp [hc'])
        hrep_b hseen_b (by simp [hd_eq])
        (Bytes.repAddressRef_heapMono₂ addrTy (ext03.trans evt.heap_extends) rba)
        (hB.mono evt.heap_extends) hEin.2 hrep1 ha1S evb
      refine ⟨res, fun fuel hfl => ?_, hrep_res, hlen1.trans hlen_res, hresS⟩
      obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
      simp only [occScanF, hbm, ha1 n (by omega), hres n (by omega)]
  | .other_Let (m2 := m2) (m26 := m26) (m39 := m3) (cs_ejheattv := cs1)
      (cs924 := cs3) (v_bscvpeug := v') (m_zpsiogvj := m4) (cs_kvpezkmc := cs2)
      (hm12 := hm12) (hm34 := hm34) (ev_yanxknqt := evm) (hne77 := hne0)
      (ld92 := ld) (ev_kgfsfvov := evi) (ev926 := evrec) (hc1041 := hc) .. =>
    obtain ⟨ext02, -⟩ := mkBlks m26 m2 hm34 hm12
    have ext03 := ext02.trans evm.heap_extends
    obtain ⟨T, V0, B, rfl, -, hV, hB⟩ := TmOExact.letE_of_load (hE.mono ext03) ld
    have hv' := expr_inst1_tmOExact (bnd_sub fun c hc' => by rw [hc]; simp [hc']) hB hV evi
    have hrep' : ∃ w, Represents rom m4 v' w :=
      call_arg_rep_of_obs hcar evrec (by rw [hc]; simp) (by simp)
    have hlt : cs3.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    exact occ_scan_aux hwf hS hH hbd hvalid hbound hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) (car fun c hc' => by rw [hc]; simp [hc'])
      hrep' hseen hd_eq
      (Bytes.repAddressRef_heapMono₂ addrTy (ext03.trans evi.heap_extends) rba) hv' hEin
      (flatList_mono (ext03.trans evi.heap_extends) hacc) haccS evrec
  | .other_Proj (m2 := m2) (m26 := m26) (m39 := m3) (cs_ejheattv := cs1)
      (x_x := xx) (cs1069 := cs2) (hm12 := hm12) (hm34 := hm34) (ev_yanxknqt := evm)
      (hne77 := hne0) (ld92 := ld) (ev1071 := evrec) (hc1104 := hc) .. =>
    obtain ⟨ext02, rblks⟩ := mkBlks m26 m2 hm34 hm12
    obtain ⟨bm, hbm, hrm⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) (hE.mono ext02) hEin rblks evm
    cases bm with
    | false => exact (hne0 hrm).elim
    | true =>
      have ext03 := ext02.trans evm.heap_extends
      obtain ⟨pa, idx, E1, -, hE_p, -, hE1⟩ := TmOExact.proj_of_load (hE.mono ext03) ld
      subst hE_p
      have hrep1 : ∃ w, Represents rom m3 xx w :=
        call_arg_rep_of_obs hcar evrec (by rw [hc]; simp) (by simp)
      have hlt_p : exprSize E1 < exprSize (.proj (Core.keyOf t (ixAddr pa)) idx.val E1) := by
        simp [exprSize]
      have hlt : cs2.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      obtain ⟨res, hres, hrep_res, hlen_res, hresS⟩ := occ_scan_aux hwf hS hH hbd hvalid hbound
        hRagree hcl (sub fun c hc' => by rw [hc]; simp [hc'])
        (car fun c hc' => by rw [hc]; simp [hc'])
        hrep1 (occSeen_lt hseen hlt_p) hd_eq
        (Bytes.repAddressRef_heapMono₂ addrTy ext03 rba) hE1 hEin.2
        (flatList_mono ext03 hacc) haccS evrec
      refine ⟨res, fun fuel hfl => ?_, hrep_res, hlen_res, hresS⟩
      obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
      simp only [occScanF, hbm, hres n (by omega)]
  | .other_other (m2 := m2) (m26 := m26) (m39 := m3) (cs_ejheattv := cs1)
      (hm12 := hm12) (hm34 := hm34) (ev_yanxknqt := evm) (hne77 := hne0) (ld92 := ld)
      (hne685 := hnA) (hne792 := hnL) (hne899 := hnF) (hne1042 := hnLet) (hne1105 := hnP)
      (he1110 := hr0) (he1111 := hh0) (hc1112 := hc) .. =>
    cases hr0; cases hh0
    obtain ⟨ext02, rblks⟩ := mkBlks m26 m2 hm34 hm12
    obtain ⟨bm, hbm, hrm⟩ := occ_mentions_block_spec hwf hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) (hE.mono ext02) hEin rblks evm
    cases bm with
    | false => exact (hne0 hrm).elim
    | true =>
      have ext03 := ext02.trans evm.heap_extends
      obtain ⟨k, rep⟩ := hE.mono ext03
      refine ⟨acc, fun fuel hfl => ?_, flatList_mono ext03 hacc, Nat.le_refl _, haccS⟩
      obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
      cases rep with
      | bvarLocal _ _ _ | sort _ _ | const _ _ _ | litNat _ _ _ | litStr _ _ _ =>
        simp [occScanF, hbm]
      | bvarFree _ _ _ hd => omega
      | app cell _ _ => simp [loadValue, cell] at ld; exact (hnA _ rfl ld.symm).elim
      | lam cell _ _ _ => simp [loadValue, cell] at ld; exact (hnL _ rfl ld.symm).elim
      | forallE cell _ _ _ => simp [loadValue, cell] at ld; exact (hnF _ rfl ld.symm).elim
      | letE cell _ _ _ => simp [loadValue, cell] at ld; exact (hnLet _ rfl ld.symm).elim
      | proj cell _ _ => simp [loadValue, cell] at ld; exact (hnP _ rfl ld.symm).elim
termination_by cs.length

/-- **`KernelModeled::occ_scan_list`** refines `scanList (fun x acc => occScanF V B n x d acc)`. -/
private theorem occ_scan_list_aux {rootCalls : List (Call F)} {rom : ROM F}
    {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls) (hvalid : rom.Valid) (hbound : ROMAddressesAtMost rom (2 ^ 39))
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c') (hcl : UsedClosed R)
    {ba : Bytes.Address} {es : List KExpr} {d : Nat} {acc : List FlatEntry}
    {seen : List (F × Nat)}
    {xblk xes xacc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls) (hcar : CallsInROM rom cs)
    (hseen : ∀ x ∈ es, OccSeen rom (Core.keyOf t) x seen) (hd_eq : seen.length = d)
    (rba : Bytes.RepAddressRef addrTy h ba xblk)
    (hes : RepList kexprListEnum (TmOExact (Core.keyOf t)) h es xes)
    (hIn : ∀ x ∈ es, AddrIn (Held R) (Core.keyOf t) x)
    (hacc : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h acc xacc)
    (haccS : ∀ e ∈ acc, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p)
    (ev : ObsFn W "KernelModeled::occ_scan_list" [xblk, xes, .field (d : F), xacc] h r h' cs) :
    ∃ res : List FlatEntry,
      (∀ fuel, (∀ x ∈ es, exprSize x < fuel) →
        scanList (fun x a => occScanF (FlatView.ofStore t E₀) (ixAddr ba) fuel x d a) es acc =
          some res) ∧
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h' res r ∧
      acc.length ≤ res.length ∧
      (∀ e ∈ res, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) := by
  match Obs.«KernelModeled::occ_scan_list».obs ev with
  | .Nil (ld12 := ld) (he21 := hr0) (he22 := hh0) .. =>
    cases hr0; cases hh0
    obtain rfl := IxVM.Refinement.Core.RepList.nil_of_load hes ld
    exact ⟨acc, fun _ _ => rfl, hacc, Nat.le_refl _, haccS⟩
  | .Cons (x_x := xx) (x_rest := xrest) (cs44 := cs2) (v50 := vac1) (m73 := m1)
      (cs81 := cs1) (ld12 := ld) (ev83 := ev1) (ev46 := ev2) (hc116 := hc) .. =>
    obtain ⟨x, rest, rfl, hx, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
    have hrep_x : ∃ w, Represents rom h xx w :=
      call_arg_rep_of_obs hcar ev1 (by rw [hc]; simp) (by simp)
    have hlt1 : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    have hlt2 : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨a1, ha1, hrep1, hlen1, ha1S⟩ := occ_scan_aux hwf hS hH hbd hvalid hbound hRagree hcl
      (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      (fun c hc' => hcar c (by rw [hc]; simp [hc']))
      hrep_x (hseen x (List.mem_cons_self ..)) hd_eq rba hx
      (hIn x (List.mem_cons_self ..)) hacc haccS ev1
    obtain ⟨res, hres, hrep_res, hlen_res, hresS⟩ := occ_scan_list_aux hwf hS hH hbd hvalid
      hbound hRagree hcl (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      (fun c hc' => hcar c (by rw [hc]; simp [hc']))
      (fun y hy => hseen y (List.mem_cons_of_mem _ hy)) hd_eq
      (Bytes.repAddressRef_heapMono₂ addrTy ev1.heap_extends rba)
      (tmOExactList_mono ev1.heap_extends hrest)
      (fun y hy => hIn y (List.mem_cons_of_mem _ hy)) hrep1 ha1S ev2
    refine ⟨res, fun fuel hfl => ?_, hrep_res, hlen1.trans hlen_res, hresS⟩
    simp only [scanList, ha1 fuel (hfl x (List.mem_cons_self ..)),
      hres fuel (fun y hy => hfl y (List.mem_cons_of_mem _ hy))]
termination_by cs.length

end

/-- **`KernelModeled::inst_ctor_params`** computes `instCtorParams E sp` on `TmOExact` (stepping
through any `Let` nodes). -/
theorem inst_ctor_params_spec {κ : _root_.Address → KKey} {E : KExpr} {sp : List KExpr}
    {xt xsp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelModeled::inst_ctor_params" [xt, xsp] h r h' cs)
    (hbnd : Bounded cs)
    (hE : TmOExact κ h E xt) (hsp : RepList kexprListEnum (TmOExact κ) h sp xsp) :
    ∃ E', instCtorParams E sp = some E' ∧ TmOExact κ h' E' r := by
  have bnd : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  match Obs.«KernelModeled::inst_ctor_params».obs ev with
  | .Nil (ld12 := ld) (he21 := hr0) (he22 := hh0) .. =>
    cases hr0; cases hh0
    obtain rfl := IxVM.Refinement.Core.RepList.nil_of_load hsp ld
    exact ⟨E, rfl, hE⟩
  | .Cons_Forall (cs_mfoyspyn := cs2) (cs_wqqnejsp := cs1) (ld12 := ld1) (ld_txwzgqvr := ld2)
      (ev_moovuzip := evi) (ev_bvxpnrar := evrec) (hc_ufdvkrjv := hc) .. =>
    obtain ⟨v, vs, rfl, hv, hvs⟩ := IxVM.Refinement.Core.RepList.cons_of_load hsp ld1
    obtain ⟨D, B, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load hE ld2
    have hinst := expr_inst1_tmOExact (bnd fun c hc' => by rw [hc]; simp [hc']) hB hv evi
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨E', h1, h2⟩ := inst_ctor_params_spec evrec (bnd fun c hc' => by rw [hc]; simp [hc'])
      hinst (tmOExactList_mono evi.heap_extends hvs)
    exact ⟨E', h1, h2⟩
  | .Cons_Let (cs_jrhgsmcn := cs2) (cs_pshylesg := cs1) (ld12 := ld1) (ld_txwzgqvr := ld2)
      (ev_cnnmbauo := evi) (ev_ttnheqnu := evrec) (hc_qxidxcae := hc) .. =>
    obtain ⟨T, V0, B, rfl, -, hV, hB⟩ := TmOExact.letE_of_load hE ld2
    have hinst := expr_inst1_tmOExact (bnd fun c hc' => by rw [hc]; simp [hc']) hB hV evi
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨E', h1, h2⟩ := inst_ctor_params_spec evrec (bnd fun c hc' => by rw [hc]; simp [hc'])
      hinst (tmOExactList_mono evi.heap_extends hsp)
    exact ⟨E', h1, h2⟩
termination_by cs.length

/-- **`KernelModeled::ctors_scan`** refines `ctorsLoop (FlatView.ofStore t E₀) B info aux sp us
((List.range info.nctors).drop c) acc`. -/
theorem ctors_scan_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c') (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {ba mba : Bytes.Address} {info : IndInfo} {aux : Bool} {sp : List KExpr} {us : List KLevel}
    (hmba : ixAddr mba = info.blk) (hSmblk : Held R info.blk)
    (hnp : info.np < 72057594037927936) (hnct : info.nctors < 72057594037927936)
    (hidx : info.idx < 72057594037927936) (hspIn : ∀ p ∈ sp, AddrIn (Held R) (Core.keyOf t) p) :
    ∀ (k c : Nat) {acc : List FlatEntry}
      {xblk xmblk xsp xus xacc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      c + k = info.nctors →
      (∀ c' ∈ cs, c' ∈ rootCalls) →
      Bytes.RepAddressRef addrTy h ba xblk →
      Bytes.RepAddressRef addrTy h mba xmblk →
      RepList kexprListEnum (TmOExact (Core.keyOf t)) h sp xsp →
      RepKLevelList h us xus →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h acc xacc →
      (∀ e ∈ acc, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) →
      ObsFn W "KernelModeled::ctors_scan"
        [xblk, xmblk, .field (info.idx : F), .field (info.nctors : F), .field (c : F),
          .field (info.np : F), auxVal aux, xsp, xus, xacc] h r h' cs →
      ∃ res : List FlatEntry,
        ctorsLoop (FlatView.ofStore t E₀) (ixAddr ba) info aux sp us
          ((List.range info.nctors).drop c) acc = some res ∧
        RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h' res r ∧
        acc.length ≤ res.length ∧
        (∀ e ∈ res, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) := by
  intro k
  induction k with
  | zero =>
    intro c acc xblk xmblk xsp xus xacc r h h' cs hck _ _ _ _ _ hacc haccS ev
    have hc : c = info.nctors := by omega
    subst hc
    match Obs.«KernelModeled::ctors_scan».obs ev with
    | .n0 (he25 := hr0) (he26 := hh0) .. =>
      cases hr0; cases hh0
      simp only [List.drop_eq_nil_of_le (by simp : (List.range info.nctors).length ≤ info.nctors)]
      exact ⟨acc, rfl, hacc, Nat.le_refl _, haccS⟩
    | .other (op17 := op) (hne28 := hne) .. =>
      simp only [evalBinOp, sub_self, Except.ok.injEq] at op
      exact (hne op.symm).elim
  | succ k ih =>
    intro c acc xblk xmblk xsp xus xacc r h h' cs hck hsub rba rmba hsp hus hacc haccS ev
    match Obs.«KernelModeled::ctors_scan».obs ev with
    | .n0 (op17 := op) .. =>
      have h0 : ((info.nctors : F) - (c : F)) = 0 := by
        simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op; exact op
      have h1 : (info.nctors : F) = (c : F) := sub_eq_zero.mp h0
      have h2 : info.nctors = c := by
        rw [← fval_natCast (n := info.nctors) (by omega), ← fval_natCast (n := c) (by omega), h1]
      omega
    | .other (m33 := m1) (p41 := pci) (cs47 := cs1) (x_cty := xcty)
        (v127 := vinst) (m128 := m2) (cs138 := cs2) (v221 := vbody) (m222 := m3) (cs224 := cs3)
        (cs233 := cs5) (v240 := vc1) (v245 := vacc1) (m318 := m4) (cs326 := cs4)
        (ev49 := evct) (ld43 := ldct) (ev140 := evinst) (sg229 := sg)
        (op287 := opc1) (ev328 := evocc) (ev235 := evrec) (hc360 := hc) .. =>
      have sub : ∀ {cs' : List (Call F)}, (∀ c' ∈ cs', c' ∈ cs) → ∀ c' ∈ cs', c' ∈ rootCalls :=
        fun hs c' hc' => hsub c' (hs c' hc')
      obtain ⟨cty, nl, np, nf, xty', _, _, _, _, hshape, -, hctyAt, -, -, -, hcty, hctyIn, -, -⟩ :=
        ctorLoad_ofStore ht hwf hS hH hbd hRagree hcl hlv (by omega) (by omega)
          (sub fun c' hc' => by rw [hc]; simp [hc']) (hmba.symm ▸ hSmblk) rmba evct ldct
      injection hshape with _ _ hl; injection hl with _ hl; injection hl with hty_eq _
      subst hty_eq
      rw [hmba] at hctyAt
      have hinst := expr_inst_levels_tmOExact
        (RomBound.bounded_mono hbd (sub fun c' hc' => by rw [hc]; simp [hc']))
        hcty (hus.mono evct.heap_extends) evinst
      have hinstIn : AddrIn (Held R) (Core.keyOf t) (exprInstLevels us cty) :=
        addrIn_exprInstLevels hctyIn
      have hbody : ∃ body,
          ctorBody aux info.np sp (exprInstLevels us cty) = some body ∧
          TmOExact (Core.keyOf t) m3 body vbody ∧
          AddrIn (Held R) (Core.keyOf t) body ∧
          Heap.Extends m2 m3 := by
        cases sg with
        | n0 cs_p hv0 evpeel hcs =>
          have haux : aux = false := auxVal_eq_zero.mp hv0
          obtain ⟨body, hpeel, hbtm⟩ := peel_n_foralls_zeta_spec info.np (by omega) hinst
            (RomBound.bounded_mono hbd (sub fun c' hc' => by rw [hc, hcs]; simp [hc'])) evpeel
          exact ⟨body, by simp [ctorBody, haux, hpeel], hbtm,
            addrIn_peelForalls hinstIn hpeel, evpeel.heap_extends⟩
        | other cs_i hne0 evip hcs =>
          have haux : aux = true := by
            cases h : aux
            · exact (hne0 (auxVal_eq_zero.mpr h)).elim
            · rfl
          have ext02 := evct.heap_extends.trans evinst.heap_extends
          obtain ⟨body, hip, hbtm⟩ := inst_ctor_params_spec evip
            (RomBound.bounded_mono hbd (sub fun c' hc' => by rw [hc, hcs]; simp [hc']))
            hinst (tmOExactList_mono ext02 hsp)
          exact ⟨body, by simp [ctorBody, haux, hip], hbtm,
            addrIn_instCtorParams hinstIn hspIn hip, evip.heap_extends⟩
      obtain ⟨body, hctorB, hbtm, hbodyIn, ext23⟩ := hbody
      have ext03 := evct.heap_extends.trans (evinst.heap_extends.trans ext23)
      obtain ⟨rom, hvalid, hbound, hcarried⟩ := hbd
      have hrep_body : ∃ w, Represents rom m3 vbody w :=
        call_arg_rep_of_obs (fun c' hc' => hcarried c' (hsub c' hc')) evocc
          (by rw [hc]; simp) (by simp)
      have evocc' : ObsFn W "KernelModeled::occ_scan"
          [xblk, vbody, .field ((0 : Nat) : F), xacc] m3 vacc1 m4 cs4 := by simpa using evocc
      obtain ⟨acc1, hocc, hrep1, hlen1, hacc1S⟩ := occ_scan_aux (seen := []) hwf hS hH
        ⟨rom, hvalid, hbound, hcarried⟩ hvalid hbound hRagree hcl
        (sub fun c' hc' => by rw [hc]; simp [hc'])
        (fun c' hc' => hcarried c' (hsub c' (by rw [hc]; simp [hc'])))
        hrep_body (by simp [OccSeen])
        rfl (Bytes.repAddressRef_heapMono₂ addrTy ext03 rba) hbtm hbodyIn
        (flatList_mono ext03 hacc) haccS evocc'
      obtain rfl := binop_add_one_nat opc1
      have ext04 := ext03.trans evocc.heap_extends
      obtain ⟨res, hres, hrep_res, hlen_res, hresS⟩ := ih (c + 1) (by omega)
        (sub fun c' hc' => by rw [hc]; simp [hc'])
        (Bytes.repAddressRef_heapMono₂ addrTy ext04 rba)
        (Bytes.repAddressRef_heapMono₂ addrTy ext04 rmba)
        (tmOExactList_mono ext04 hsp) (hus.mono ext04) hrep1 hacc1S evrec
      have hdrop : (List.range info.nctors).drop c = c :: (List.range info.nctors).drop (c + 1) := by
        have hlt : c < (List.range info.nctors).length := by simp; omega
        rw [List.drop_eq_getElem_cons hlt]; simp
      refine ⟨res, ?_, hrep_res, hlen1.trans hlen_res, hresS⟩
      rw [hdrop]
      simp only [ctorsLoop, ctorScan]
      change (match (match ctorTypeAt t E₀ info.blk info.idx c with
        | none => none
        | some cty => match ctorBody aux info.np sp (exprInstLevels us cty) with
          | none => none
          | some body => occScanF (FlatView.ofStore t E₀) (ixAddr ba) (exprSize body + 1) body 0 acc) with
        | none => none
        | some a => ctorsLoop (FlatView.ofStore t E₀) (ixAddr ba) info aux sp us
            ((List.range info.nctors).drop (c + 1)) a) = some res
      rw [hctyAt]; dsimp only
      rw [hctorB]; dsimp only
      have hocc' := hocc (exprSize body + 1) (Nat.lt_succ_self _)
      simp only [List.length_nil] at hocc'
      rw [hocc']; exact hres

/-- **`KernelModeled::nested_walk`** refines `nestedWalk (FlatView.ofStore t E₀) B n i acc` at
some fuel `n`. -/
theorem nested_walk_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c') (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {ba : Bytes.Address} {acc : List FlatEntry} {i : Nat}
    {xblk xacc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hi_le : i ≤ acc.length) (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (rba : Bytes.RepAddressRef addrTy h ba xblk)
    (hacc : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h acc xacc)
    (haccS : ∀ e ∈ acc, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p)
    (ev : ObsFn W "KernelModeled::nested_walk" [xblk, xacc, .field (i : F)] h r h' cs) :
    ∃ (n : Nat) (res : List FlatEntry),
      nestedWalk (FlatView.ofStore t E₀) (ixAddr ba) n i acc = some res ∧
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h' res r := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → ∀ c ∈ cs', c ∈ rootCalls :=
    fun hs c hc => hsub c (hs c hc)
  match Obs.«KernelModeled::nested_walk».obs ev with
  | .n0 (ev23 := evlen) (op17 := op) (he38 := hr0) (he39 := hh0) (hc40 := hc) .. =>
    cases hr0; cases hh0
    obtain ⟨rfl, rfl⟩ := flat_length_spec evlen hacc
    have hlen_lt : acc.length < 2 ^ 39 :=
      repList_length_lt_of_obs hbd hsub evlen (by rw [hc]; simp) (by simp) hacc
    have h0 : ((acc.length : F) - (i : F)) = 0 := by
      simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op; exact op
    have h1 : (acc.length : F) = (i : F) := sub_eq_zero.mp h0
    have heq : acc.length = i := by
      rw [← fval_natCast (n := acc.length) (by omega), ← fval_natCast (n := i) (by omega), h1]
    refine ⟨1, acc, ?_, hacc⟩
    have hnone : acc[i]? = none := List.getElem?_eq_none (by omega)
    simp [nestedWalk, hnone]
  | .other (m12 := m1) (m46 := m2) (x_addr := xaddr) (x_is_aux := xaux)
      (x_sp := xsp) (x_us := xus) (m99 := m3) (p107 := pci) (cs113 := cs3)
      (x_np := xnp) (x_nctors := xnct) (x_mblk := xmblk) (x_midx := xmidx)
      (cs177 := cs5) (v181 := vacc1) (v182 := vi1) (m191 := m4) (cs199 := cs4)
      (ev23 := evlen) (op17 := op) (hne41 := hne) (ev58 := evlk) (ev115 := evci)
      (ld109 := ldci) (ev201 := evct) (op294 := opi1) (ev179 := evrec) (hc296 := hc) .. =>
    obtain ⟨rfl, rfl⟩ := flat_length_spec evlen hacc
    have hlen_lt : acc.length < 2 ^ 39 :=
      repList_length_lt_of_obs hbd hsub evlen (by rw [hc]; simp) (by simp) hacc
    have hi_lt : i < acc.length := by
      by_contra hge
      have heq : acc.length = i := by omega
      subst heq
      simp only [evalBinOp, sub_self, Except.ok.injEq] at op
      exact hne op.symm
    obtain ⟨⟨e, he_at, he_rep⟩, rfl⟩ := flat_lookup_spec evlk hacc
    rw [fval_natCast (by omega)] at he_at
    obtain ⟨xa', xsp', xus', ea, htup, rea, hea, hsp, hus⟩ := he_rep
    injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
    injection hl with h3 hl; injection hl with h4; subst h1 h2 h3 h4
    have he_mem : e ∈ acc := List.mem_of_getElem? he_at
    have hSe := haccS e he_mem
    obtain ⟨hInd, -⟩ := indInfo_of_get_ci hS hH hbd hRagree hcl
      (sub fun c hc' => by rw [hc]; simp [hc']) (hea.symm ▸ hSe.1) rea evci ldci
    obtain ⟨info, mba, hinfo, -, hnp56, hnct56, hidx56, hSblk, -, rfl, rfl, hmba, rmba, rfl⟩ :=
      hInd _ _ _ _ _ _ _ _ rfl
    rw [hea] at hinfo
    have evct' : ObsFn W "KernelModeled::ctors_scan"
        [xblk, xmblk, .field (info.idx : F), .field (info.nctors : F), .field ((0 : Nat) : F),
          .field (info.np : F), auxVal e.aux, xsp, xus, xacc] m3 vacc1 m4 cs4 := by
      simpa using evct
    have ext03 := evci.heap_extends
    obtain ⟨acc1, hct, hrep1, hlen1, hacc1S⟩ := ctors_scan_spec ht hwf hS hH hbd hRagree hcl hlv
      hmba hSblk hnp56 hnct56 hidx56 hSe.2 info.nctors 0 (by omega)
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (Bytes.repAddressRef_heapMono₂ addrTy ext03 rba) rmba
      (tmOExactList_mono ext03 hsp) (hus.mono ext03) (flatList_mono ext03 hacc) haccS evct'
    simp only [List.drop_zero] at hct
    obtain rfl := binop_add_one_nat opi1
    have hlt_cs : cs5.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨n, res, hnw, hrep_res⟩ := nested_walk_spec ht hwf hS hH hbd hRagree hcl hlv
      (by omega : i + 1 ≤ acc1.length) (sub fun c hc' => by rw [hc]; simp [hc'])
      (Bytes.repAddressRef_heapMono₂ addrTy (ext03.trans evct.heap_extends) rba)
      hrep1 hacc1S evrec
    refine ⟨n + 1, res, ?_, hrep_res⟩
    simp only [nestedWalk, he_at]
    change (match indInfoAt E₀ e.addr with
      | some (some info) =>
        match ctorsScan (FlatView.ofStore t E₀) (ixAddr ba) info e.aux e.params e.levels acc with
        | none => none
        | some a => nestedWalk (FlatView.ofStore t E₀) (ixAddr ba) n (i + 1) a
      | _ => none) = some res
    rw [hinfo]; dsimp only
    unfold ctorsScan; rw [hct]; exact hnw
termination_by cs.length

/-- **`KernelModeled::flat_reals`** computes `es.filter (fun e => !e.aux)` on
`FlatEntryRepExact`. -/
theorem flat_reals_spec {κ : _root_.Address → KKey} :
    ∀ (es : List FlatEntry) {xflat r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelModeled::flat_reals" [xflat] h r h' cs →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      RepList flatListEnum (FlatEntryRepExact κ) h' (es.filter fun e => !e.aux) r := by
  intro es
  induction es with
  | nil =>
    intro xflat r h h' cs ev hes
    match Obs.«KernelModeled::flat_reals».obs ev with
    | .Nil (he24 := hr0) (hm23 := hm0) .. => cases hr0; cases hm0; exact Lib.rep_store_nil h
    | .Cons_n0 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e rest ih =>
    intro xflat r h h' cs ev hes
    match Obs.«KernelModeled::flat_reals».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_n0 (ld12 := ld) (he103 := hr0) (hm102 := hm0) (ev127 := evrec) .. =>
      cases hr0; cases hm0
      obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with h1e h1r; subst h1e h1r
      have hcopy := he'
      obtain ⟨_, _, _, _, htup, -, -, -, -⟩ := hcopy
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
      have hf : e.aux = false := auxVal_eq_zero.mp htup.2.1.symm
      have hrec := ih evrec hrest
      simp only [List.filter_cons, hf, Bool.not_false, ↓reduceIte]
      exact Lib.rep_store_cons flatEntryRepExact_heapMono₂
        (flatEntryRepExact_heapMono₂ evrec.heap_extends he') hrec
    | .Cons_other (x_is_aux := xaux) (ld12 := ld) (hne137 := hne) (ev146 := evrec) .. =>
      obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with h1e h1r; subst h1e h1r
      have hcopy := he'
      obtain ⟨_, _, _, _, htup, -, -, -, -⟩ := hcopy
      injection htup with hl0; injection hl0 with _ hl1; injection hl1 with haux _
      have ht' : e.aux = true := by
        cases h : e.aux
        · exact (hne (haux.trans (auxVal_eq_zero.mpr h))).elim
        · rfl
      simp only [List.filter_cons, ht', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ih evrec hrest

/-- **`KernelModeled::aux_all_in(derived, flat) = 1`** forces exact list equality `derived = flat`
on `FlatEntryRepExact` when `κ` is injective. -/
theorem aux_all_in_eq_one {κ : _root_.Address → KKey} (hinj : Function.Injective κ) :
    ∀ (derived flat : List FlatEntry) {xd xf : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelModeled::aux_all_in" [xd, xf] h (.field 1) h' cs →
      Bounded cs →
      RepList flatListEnum (FlatEntryRepExact κ) h derived xd →
      RepList flatListEnum (FlatEntryRepExact κ) h flat xf →
      derived = flat := by
  intro derived
  induction derived with
  | nil =>
    intro flat xd xf h h' cs ev _ hd hf
    match Obs.«KernelModeled::aux_all_in».obs ev with
    | .Nil_Nil (ld_neljdsge := ld2) .. =>
      exact (IxVM.Refinement.Core.RepList.nil_of_load hf ld2).symm
    | .Nil_other (he_bwthzoys := hr) .. => exact absurd (Value.field.inj hr) (by decide)
    | .Cons_Nil (ld12 := ld1) .. | .Cons_Cons_n1 (ld12 := ld1) ..
    | .Cons_Cons_other (ld12 := ld1) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hd ld1
      cases hcons
  | cons d dr ih =>
    intro flat xd xf h h' cs ev hbnd hd hf
    have bnd : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelModeled::aux_all_in».obs ev with
    | .Nil_Nil (ld12 := ld1) .. | .Nil_other (ld12 := ld1) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hd ld1
    | .Cons_Nil (he_igwiafed := hr) .. => exact absurd (Value.field.inj hr) (by decide)
    | .Cons_Cons_other (he_cjmqmowm := hr) .. => exact absurd (Value.field.inj hr) (by decide)
    | .Cons_Cons_n1 (ld12 := ld1) (ld_uplwbryy := ld2) (sg_ifmfdpfc := sg)
        (ev_woqiuyxz := evaeq) (op_wetvvjfd := op1) (ev_dfliojir := evsp) (op_yjodglud := op2)
        (ev_wxxbloog := evus) (op_hcqhjrdx := op3) (ev_zzxrtlvt := evrec)
        (hc_llamfqbn := hc) .. =>
      obtain ⟨d', dr', h1, hd', hdr⟩ := IxVM.Refinement.Core.RepList.cons_of_load hd ld1
      injection h1 with h1d h1r; subst h1d h1r
      obtain ⟨f, fr, rfl, hf', hfr⟩ := IxVM.Refinement.Core.RepList.cons_of_load hf ld2
      obtain ⟨xa1, xs1, xu1, a1, ht1, ra1, ha1, hsp1, hus1⟩ := hd'
      obtain ⟨xa2, xs2, xu2, a2, ht2, ra2, ha2, hsp2, hus2⟩ := hf'
      injection ht1 with hl1; injection hl1 with h11 hl1; injection hl1 with h12 hl1
      injection hl1 with h13 hl1; injection hl1 with h14; subst h11 h12 h13 h14
      injection ht2 with hl2; injection hl2 with h21 hl2; injection hl2 with h22 hl2
      injection hl2 with h23 hl2; injection hl2 with h24; subst h21 h22 h23 h24
      cases sg with
      | n0 ops hr hh _ =>
        subst hr hh
        have haux_eq : d.aux = f.aux := by
          cases h1 : d.aux <;> cases h2 : f.aux <;> simp [auxVal, h1, h2, evalBinOp] at ops <;> rfl
        obtain ⟨hva, rfl⟩ := Lib.address_eq_spec evaeq ra1 ra2
        have hsp_eq := spec_params_zeta_eq_exact hinj hsp1 hsp2
          (bnd fun c hc' => by rw [hc]; simp [hc']) evsp
        obtain ⟨hus_eq, rfl⟩ := level_list_struct_eq_exact
          (hus1.mono evsp.heap_extends) (hus2.mono evsp.heap_extends) evus
        rw [hva] at op1
        have hall : a1 = a2 ∧ d.params = f.params ∧ d.levels = f.levels := by
          by_cases ha : a1 = a2 <;> by_cases hs : d.params = f.params <;>
            by_cases hu : d.levels = f.levels
          · exact ⟨ha, hs, hu⟩
          all_goals
            simp [ha, hs, hu] at hsp_eq hus_eq op1
            try rw [hsp_eq] at op2
            try rw [hus_eq] at op3
            simp [evalBinOp] at op1 op2 op3
            try rw [← op1] at op2; simp [evalBinOp] at op2
            try rw [← op2] at op3; simp [evalBinOp] at op3
        obtain ⟨rfl, hsp_e, hus_e⟩ := hall
        have hd_eq : d = f := by
          cases d; cases f; simp only at ha1 ha2 haux_eq hsp_e hus_e
          subst haux_eq hsp_e hus_e; rw [← ha1, ha2]
        have hrest_eq := ih fr evrec (bnd fun c hc' => by rw [hc]; simp [hc'])
          (flatList_mono evsp.heap_extends hdr) (flatList_mono evsp.heap_extends hfr)
        rw [hd_eq, hrest_eq]
      | other _ _ _ hr hh _ =>
        subst hr hh
        obtain ⟨hva, rfl⟩ := Lib.address_eq_spec evaeq ra1 ra2
        have hsp_eq := spec_params_zeta_eq_exact hinj hsp1 hsp2
          (bnd fun c hc' => by rw [hc]; simp [hc']) evsp
        obtain ⟨hus_eq, rfl⟩ := level_list_struct_eq_exact
          (hus1.mono evsp.heap_extends) (hus2.mono evsp.heap_extends) evus
        rw [hva] at op1
        by_cases ha : a1 = a2 <;> by_cases hs : d.params = f.params <;>
          by_cases hu : d.levels = f.levels
        all_goals
          simp [ha, hs, hu] at hsp_eq hus_eq op1
          try rw [hsp_eq] at op2
          try rw [hus_eq] at op3
          simp [evalBinOp] at op1 op2 op3
          try rw [← op1] at op2; simp [evalBinOp] at op2
          try rw [← op2] at op3; simp [evalBinOp] at op3

/-- **`KernelModeled::check_nested_aux`** proves `∃ n, derivedFlatAt (FlatView.ofStore t E₀)
(ixAddr ba) off n = some flat` whenever `flat`'s non-auxiliary entries match `originals`. -/
theorem check_nested_aux_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c') (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {ba : Bytes.Address} {flat os : List FlatEntry} {ms : List _root_.Address} {off : Nat}
    {xblk xflat r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (hmemAt : membersAt E₀ (ixAddr ba) = some ms)
    (horig : originals (FlatView.ofStore t E₀) off ms = some os)
    (hfilt : flat.filter (fun e => !e.aux) = os)
    (rba : Bytes.RepAddressRef addrTy h ba xblk)
    (hflat : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h flat xflat)
    (hflatS : ∀ e ∈ flat, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p)
    (ev : ObsFn W "KernelModeled::check_nested_aux" [xblk, xflat] h r h' cs) :
    ∃ n, derivedFlatAt (FlatView.ofStore t E₀) (ixAddr ba) off n = some flat := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → ∀ c ∈ cs', c ∈ rootCalls :=
    fun hs c hc => hsub c (hs c hc)
  have hinj : Function.Injective (Core.keyOf t) := fun _ _ he => Core.keyOf_inj hwf he
  match Obs.«KernelModeled::check_nested_aux».obs ev with
  | .run (v1 := vder) (m2 := m2) (cs12 := cs2) (v16 := vreals) (m26 := m1) (m65 := m3)
      (m85 := m4) (m119 := m5) (cs127 := cs5) (ev36 := evreals) (ev14 := evnw) (ev75 := evc1)
      (ev95 := evc2) (ev129 := evall) (heq152 := heq1) (hc157 := hc) .. =>
    have hreals := flat_reals_spec flat evreals hflat
    rw [hfilt] at hreals
    have hosS : ∀ e ∈ os, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p := by
      intro e he; rw [← hfilt] at he
      exact hflatS e (List.mem_of_mem_filter he)
    have evnw' : ObsFn W "KernelModeled::nested_walk"
        [xblk, vreals, .field ((0 : Nat) : F)] m1 vder m2 cs2 := by simpa using evnw
    obtain ⟨n, derived, hnw, hrep_der⟩ := nested_walk_spec ht hwf hS hH hbd hRagree hcl hlv
      (Nat.zero_le _) (sub fun c hc' => by rw [hc]; simp [hc'])
      (Bytes.repAddressRef_heapMono₂ addrTy evreals.heap_extends rba) hreals hosS evnw'
    have ext_m2_m4 := evc1.heap_extends.trans evc2.heap_extends
    have ext_0_m4 := evreals.heap_extends.trans (evnw.heap_extends.trans ext_m2_m4)
    have evall' : ObsFn W "KernelModeled::aux_all_in" [vder, xflat] m4 (.field 1) m5 cs5 := by
      rwa [heq1] at evall
    have heq := aux_all_in_eq_one hinj derived flat evall'
      (RomBound.bounded_mono hbd (sub fun c hc' => by rw [hc]; simp [hc']))
      (flatList_mono ext_m2_m4 hrep_der) (flatList_mono ext_0_m4 hflat)
    subst heq
    refine ⟨n, ?_⟩
    unfold derivedFlatAt
    change (match membersAt E₀ (ixAddr ba) with
      | none => none
      | some ms => match originals (FlatView.ofStore t E₀) off ms with
        | none => none
        | some os => nestedWalk (FlatView.ofStore t E₀) (ixAddr ba) n 0 os) = some derived
    rw [hmemAt]; dsimp only; rw [horig]; dsimp only; exact hnw

/-! ## `is_muts_block`, `rec_to_parent_addr`, `extract_aux_*`, `aux_already_in`, `build_flat_block` -/

/-- Witness in heap `h` that `xty` has `n` leading `Forall` cells whose next domain's
`collect_spine` head loads `Const` in `h`. Produced by `rec_to_parent_addr` and transported
across heap extensions to pin `extract_aux_spec_params` and `extract_aux_occ_us`. -/
def MajorSpineIsConst (h : Heap F) (xty : SourceValue F) (n : Nat) : Prop :=
  ∃ (v xm xhd xargs xa xu w1 w2 : SourceValue F) (h₀ : Heap F) (cs1 cs2 : List (Call F)),
    Heap.Extends h₀ h ∧
    ObsFn W "KernelCheck::peel_n_foralls" [xty, .field (n : F)] h₀ v h₀ cs1 ∧
    loadValue h₀ v = .ok (.construct kexprEnum "Forall" [xm, w1, w2]) ∧
    ObsFn W "KernelTypes::collect_spine" [xm] h₀ (.tuple [xhd, xargs]) h cs2 ∧
    loadValue h xhd = .ok (.construct kexprEnum "Const" [xa, xu])

/-- **`KernelCheck::is_muts_block`** returns `1` on a `Muts` record in `E₀`, `0` otherwise. -/
theorem is_muts_block_spec {rootCalls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀)
    {ba : Bytes.Address} {cb : Ixon.Constant} {xba r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls) (hcbE : recordOf E₀ (ixAddr ba) = some cb)
    (rba : Bytes.RepAddressRef addrTy h ba xba)
    (ev : ObsFn W "KernelCheck::is_muts_block" [xba] h r h' cs) :
    r = .field (match cb.info with | .muts _ => 1 | _ => 0) := by
  match Obs.«KernelCheck::is_muts_block».obs ev with
  | .Muts (cs12 := cs1) (ev14 := evld) (he90 := hr0) (hc92 := hc) .. =>
    cases hr0
    obtain ⟨-, bytes, c, hh, ha, hex, -, -, -, -, -, -, rep⟩ :=
      L1.load_verified_constant_decode rba evld
    have hcEq := record_eq_of_hashed_flat hS (fun c' hc' => hsub c' (by rw [hc]; simp [hc']))
      hcbE hh ha hex
    subst hcEq
    obtain ⟨iv, _, _, _, _, hv, hinfo⟩ := rep.toConstShapeRep
    injection hv with _ _ hl; injection hl with hm _
    cases hci : c.info with
    | muts _ => rfl
    | defn _ | recr _ | axio _ | quot _ | cPrj _ | rPrj _ | iPrj _ | dPrj _ =>
      rw [hci] at hinfo
      obtain ⟨_, hshape⟩ := hinfo
      rw [hshape] at hm
      simp [Core.Specs.Callees.ixInfoEnum, Core.Specs.Callees.infoCtor] at hm
  | .other (cs12 := cs1) (ev14 := evld) (hne93 := hne) (he97 := hr0) (hc99 := hc) .. =>
    cases hr0
    obtain ⟨-, bytes, c, hh, ha, hex, -, -, -, -, -, -, rep⟩ :=
      L1.load_verified_constant_decode rba evld
    have hcEq := record_eq_of_hashed_flat hS (fun c' hc' => hsub c' (by rw [hc]; simp [hc']))
      hcbE hh ha hex
    subst hcEq
    obtain ⟨iv, _, _, _, _, hv, hinfo⟩ := rep.toConstShapeRep
    injection hv with _ _ hl; injection hl with hm _
    cases hci : c.info with
    | muts _ =>
      rw [hci] at hinfo
      obtain ⟨xm, hshape, -⟩ := hinfo
      rw [hshape] at hm
      exact (hne [xm] rfl hm).elim
    | defn _ | recr _ | axio _ | quot _ | cPrj _ | rPrj _ | iPrj _ | dPrj _ => rfl

/-- **`KernelCheck::rec_to_parent_addr`** extracts the major premise's `Const` head address on
`TmOExact` and records `MajorSpineIsConst h'`. -/
theorem rec_to_parent_addr_spec {κ : _root_.Address → KKey}
    {ty : KExpr} {np nmot nmin ni : Nat} {xty r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hsum : np + nmot + nmin + ni < 9223372036854775808)
    (hTy : TmOExact κ h ty xty)
    (ev : ObsFn W "KernelCheck::rec_to_parent_addr"
      [xty, .field (np : F), .field (nmot : F), .field (nmin : F), .field (ni : F)] h r h' cs) :
    ∃ (d : KExpr) (pa : Bytes.Address) (us : List KLevel),
      binderDomAfter (np + nmot + nmin + ni) ty = some d ∧
      d.getAppFn = .const (κ (ixAddr pa)) us ∧
      Bytes.RepAddressRef addrTy h' pa r ∧
      MajorSpineIsConst h' xty (np + nmot + nmin + ni) := by
  match Obs.«KernelCheck::rec_to_parent_addr».obs ev with
  | .run (v1 := vsum) (x9 := x9) (x17 := x17) (v37 := vpeel) (m38 := m1)
      (x_major_ty := xmaj) (m104 := m2) (x_head := xhd)
      (op32 := op1) (op24 := op2) (op16 := op3) (ev50 := evp) (ld78 := ldall)
      (ev117 := evsp) (ld154 := ldh) (he174 := hr0) (he175 := hh0) .. =>
    cases hr0; cases hh0
    obtain rfl := binop_add_nat op1
    obtain rfl := binop_add_nat op2
    obtain rfl := binop_add_nat op3
    obtain ⟨rfl, E', hpeel, hE'⟩ := peel_n_foralls_tmOExact (np + nmot + nmin + ni) (by omega)
      evp hTy
    obtain ⟨D, B, ℓ, rfl, hD, -, -⟩ := TmOExact.forallE_of_load hE' ldall
    obtain ⟨xhd', xargs', hd, args, htup, hhd, -, hmk, -⟩ := collect_spine_tmOExact evsp hD
    injection htup with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    obtain ⟨pa, us, rfl, rpa, -⟩ := TmOExact.const_of_load hhd ldh
    refine ⟨D, pa, us, by simp [binderDomAfter, hpeel], ?_, rpa,
      vpeel, xmaj, xhd, _, _, _, _, _, m1, _, _, evsp.heap_extends, evp, ldall, evsp, ldh⟩
    rw [← hmk, getAppFn_mkAppN_const]

/-- **`KernelCheck::spec_params_lower`** lowers each expression in `sps` by `d` on `TmOExact`
and preserves `AddrIn S κ`. -/
theorem spec_params_lower_spec {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {d : Nat} (hd : d < 4611686018427387904) :
    ∀ (sps : List KExpr) {xsps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelCheck::spec_params_lower" [xsps, .field (d : F)] h r h' cs →
      Bounded cs →
      RepList kexprListEnum (TmOExact κ) h sps xsps →
      (∀ x ∈ sps, AddrIn S κ x) →
      RepList kexprListEnum (TmOExact κ) h' (sps.map (Ix.Kernel.Expr.lowerBVars d 0)) r ∧
      (∀ x ∈ sps.map (Ix.Kernel.Expr.lowerBVars d 0), AddrIn S κ x) := by
  intro sps
  induction sps with
  | nil =>
    intro xsps r h h' cs ev _ hsps _
    match Obs.«KernelCheck::spec_params_lower».obs ev with
    | .Nil (he24 := hr0) (hm23 := hm0) .. =>
      cases hr0; cases hm0
      exact ⟨Lib.rep_store_nil h, fun _ hm => nomatch hm⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hsps ld
      cases hcons
  | cons x rest ih =>
    intro xsps r h h' cs ev hbnd hsps hIn
    match Obs.«KernelCheck::spec_params_lower».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hsps ld
    | .Cons (x_sp := xsp) (x_rest := xrest) (m60 := m1) (cs68 := cs1) (v109 := vx')
        (v110 := vrest') (m112 := m2) (cs120 := cs2) (m147 := m3) (cs155 := cs3)
        (ld12 := ld) (ev70 := evhb) (heq100 := heq0) (he105 := hr0) (hm104 := hm0)
        (ev122 := evlow) (ev157 := evrec) (hc174 := hc) .. =>
      cases hr0; cases hm0
      obtain ⟨x', rest', h1, hx, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hsps ld
      injection h1 with h1x h1r; subst h1x h1r
      have bnd1 : Bounded cs1 := RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
      have bnd2 : Bounded cs2 := RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
      have bnd3 : Bounded cs3 := RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
      have evhb' : ObsFn W "KernelSubst::has_bvar_in_range"
          [xsp, .field ((0 : Nat) : F), .field (d : F)] h (.field 0) m1 cs1 := by
        simpa [heq0] using evhb
      obtain ⟨hm1, hn, -⟩ := has_bvar_in_range_zero_tmOExact (by decide) hd bnd1 hx evhb'
      subst m1
      have evlow' : ObsFn W "KernelSubst::expr_lower"
          [xsp, .field (d : F), .field ((0 : Nat) : F)] h vx' m2 cs2 := by simpa using evlow
      have hlow := expr_lower_tmOExact (cut := 0) hd (by decide) bnd2 hx (by simpa using hn) evlow'
      obtain ⟨hrep_rest, hrestIn⟩ := ih evrec bnd3
        (tmOExactList_mono (evhb.heap_extends.trans evlow.heap_extends) hrest)
        (fun y hy => hIn y (List.mem_cons_of_mem _ hy))
      refine ⟨Lib.rep_store_cons tmOExact_heapMono₂ (hlow.mono evrec.heap_extends) hrep_rest, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hm
      · exact addrIn_lowerBVars d (c := 0) (hIn x (List.mem_cons_self ..))
      · exact hrestIn y hm

/-- **`KernelCheck::extract_aux_spec_params`** extracts `((d.getAppArgs).take extNp).map
(lowerBVars (nmot + nmin + ni) 0)` on `TmOExact`, using `MajorSpineIsConst` from an earlier
`rec_to_parent_addr` call on the same `xty`. -/
theorem extract_aux_spec_params_spec {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {ty : KExpr} {np nmot nmin ni extNp : Nat} {xty r : SourceValue F}
    {h₁ h h' : Heap F} {cs : List (Call F)}
    (hsum : np + nmot + nmin + ni < 4611686018427387904)
    (hextNp : extNp < 72057594037927936)
    (hext1 : Heap.Extends h₁ h) (hmaj : MajorSpineIsConst h₁ xty (np + nmot + nmin + ni))
    (hbnd : Bounded cs) (hTy : TmOExact κ h ty xty) (hTyIn : AddrIn S κ ty)
    (ev : ObsFn W "KernelCheck::extract_aux_spec_params"
      [xty, .field (np : F), .field (nmot : F), .field (nmin : F), .field (ni : F),
        .field (extNp : F)] h r h' cs) :
    ∃ d : KExpr,
      binderDomAfter (np + nmot + nmin + ni) ty = some d ∧
      extNp ≤ d.getAppArgs.length ∧
      RepList kexprListEnum (TmOExact κ) h'
        ((d.getAppArgs.take extNp).map (Ix.Kernel.Expr.lowerBVars (nmot + nmin + ni) 0)) r ∧
      (∀ x ∈ (d.getAppArgs.take extNp).map (Ix.Kernel.Expr.lowerBVars (nmot + nmin + ni) 0),
        AddrIn S κ x) := by
  obtain ⟨v0, xm0, xhd0, xargs0, xa0, xu0, w10, w20, h₀, cs10, cs20,
    ext01, evp0, ldall0, evsp0, ldh0⟩ := hmaj
  match Obs.«KernelCheck::extract_aux_spec_params».obs ev with
  | .run (v1 := vsum) (x9 := x9) (x17 := x17) (v37 := vpeel) (m38 := m1)
      (x_major_ty := xmaj) (m104 := m2) (x__head := xhd) (x_args := xargs)
      (cs145 := cs4) (v148 := vtake) (v149 := vlowd) (m151 := m3) (x184 := x184)
      (op32 := op1) (op24 := op2) (op16 := op3) (ev50 := evp) (ld78 := ldall)
      (ev117 := evsp) (ev161 := evtk) (op199 := op4) (op191 := op5) (ev147 := evlow)
      (hc203 := hc) .. =>
    obtain rfl := binop_add_nat op1
    obtain rfl := binop_add_nat op2
    obtain rfl := binop_add_nat op3
    obtain rfl := binop_add_nat op4
    obtain rfl := binop_add_nat op5
    obtain ⟨rfl, E', hpeel, hE'⟩ := peel_n_foralls_tmOExact (np + nmot + nmin + ni) (by omega)
      evp hTy
    obtain ⟨D, B, ℓ, rfl, hD, -, -⟩ := TmOExact.forallE_of_load hE' ldall
    obtain ⟨xhd', xargs', hd, args, htup, hhd, hargs, hmk, -⟩ := collect_spine_tmOExact evsp hD
    injection htup with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    have ext0h := ext01.trans hext1
    have hv_eq : v0 = vpeel := peel_n_foralls_det (by omega) ext0h evp0 evp
    subst hv_eq
    have hxm_eq : xm0 = xmaj := by
      have hld := (loadValue_mono ext0h ldall0).symm.trans ldall
      simp only [Except.ok.injEq, Value.construct.injEq, List.cons.injEq] at hld
      exact hld.2.2.1
    subst hxm_eq
    have hhd_eq : xhd0 = xhd := collect_spine_det_head ext0h evsp0 evsp
    subst hhd_eq
    have ldh' := loadValue_mono (hext1.trans evsp.heap_extends) ldh0
    obtain ⟨pa, us, rfl, -, -⟩ := TmOExact.const_of_load hhd ldh'
    have hargs_eq : args = D.getAppArgs := by
      rw [← hmk, getAppArgs_mkAppN_const]
    subst hargs_eq
    obtain ⟨hle, htk⟩ := kexpr_take_spec evtk hargs
    rw [fval_natCast (by omega)] at hle htk
    have hD_at : binderDomAfter (np + nmot + nmin + ni) ty = some D := by
      simp [binderDomAfter, hpeel]
    have hDIn : AddrIn S κ D := addrIn_binderDomAfter hTyIn hD_at
    have htkIn : ∀ x ∈ D.getAppArgs.take extNp, AddrIn S κ x :=
      fun x hx => addrIn_getAppArgs hDIn x (List.mem_of_mem_take hx)
    obtain ⟨hrep, hlowIn⟩ := spec_params_lower_spec (by omega) (D.getAppArgs.take extNp) evlow
      (RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])) htk htkIn
    exact ⟨D, hD_at, hle, hrep, hlowIn⟩

/-- **`KernelCheck::extract_aux_spec_params_from_rec`** unpacks a `KConstantInfo::Rec` value and
calls `extract_aux_spec_params`. -/
theorem extract_aux_spec_params_from_rec_spec {S : _root_.Address → Prop}
    {κ : _root_.Address → KKey}
    {ty : KExpr} {np nmot nmin ni extNp : Nat} {xty w1 w2 w3 w4 w5 w6 r : SourceValue F}
    {h₁ h h' : Heap F} {cs : List (Call F)}
    (hsum : np + nmot + nmin + ni < 4611686018427387904)
    (hextNp : extNp < 72057594037927936)
    (hext1 : Heap.Extends h₁ h) (hmaj : MajorSpineIsConst h₁ xty (np + nmot + nmin + ni))
    (hbnd : Bounded cs) (hTy : TmOExact κ h ty xty) (hTyIn : AddrIn S κ ty)
    (ev : ObsFn W "KernelCheck::extract_aux_spec_params_from_rec"
      [.construct kciEnum "Rec"
        [w1, xty, .field (np : F), .field (ni : F), .field (nmot : F), .field (nmin : F),
          w2, w3, w4, w5, w6],
        .field (extNp : F)] h r h' cs) :
    ∃ d : KExpr,
      binderDomAfter (np + nmot + nmin + ni) ty = some d ∧
      extNp ≤ d.getAppArgs.length ∧
      RepList kexprListEnum (TmOExact κ) h'
        ((d.getAppArgs.take extNp).map (Ix.Kernel.Expr.lowerBVars (nmot + nmin + ni) 0)) r ∧
      (∀ x ∈ (d.getAppArgs.take extNp).map (Ix.Kernel.Expr.lowerBVars (nmot + nmin + ni) 0),
        AddrIn S κ x) := by
  match Obs.«KernelCheck::extract_aux_spec_params_from_rec».obs ev with
  | .Rec (hv15 := hv) (ev83 := evsp) (hc132 := hc) .. =>
    injection hv with _ _ hl
    injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
    injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
    subst h1 h2 h3 h4 h5
    exact extract_aux_spec_params_spec hsum hextNp hext1 hmaj
      (RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])) hTy hTyIn evsp
  | .other (hne133 := hne) .. => exact (hne _ rfl rfl).elim

/-- **`KernelCheck::extract_aux_occ_us`** extracts the major premise head's level list `us` on
`TmOExact`, using `MajorSpineIsConst` from an earlier `rec_to_parent_addr` call on the same
`xty`. -/
theorem extract_aux_occ_us_spec {κ : _root_.Address → KKey}
    {ty : KExpr} {np nmot nmin ni : Nat} {xty w1 w2 w3 w4 w5 w6 r : SourceValue F}
    {h₁ h h' : Heap F} {cs : List (Call F)}
    (hsum : np + nmot + nmin + ni < 9223372036854775808)
    (hext1 : Heap.Extends h₁ h) (hmaj : MajorSpineIsConst h₁ xty (np + nmot + nmin + ni))
    (hTy : TmOExact κ h ty xty)
    (ev : ObsFn W "KernelCheck::extract_aux_occ_us"
      [.construct kciEnum "Rec"
        [w1, xty, .field (np : F), .field (ni : F), .field (nmot : F), .field (nmin : F),
          w2, w3, w4, w5, w6]] h r h' cs) :
    ∃ (d : KExpr) (pa : Bytes.Address) (us : List KLevel),
      binderDomAfter (np + nmot + nmin + ni) ty = some d ∧
      d.getAppFn = .const (κ (ixAddr pa)) us ∧
      RepKLevelList h' us r := by
  obtain ⟨v0, xm0, xhd0, xargs0, xa0, xu0, w10, w20, h₀, cs10, cs20,
    ext01, evp0, ldall0, evsp0, ldh0⟩ := hmaj
  have ext0h := ext01.trans hext1
  match Obs.«KernelCheck::extract_aux_occ_us».obs ev with
  | .Rec_Forall_Const (hv15 := hv) (op109 := op1) (op101 := op2) (op93 := op3)
      (ev131 := evp) (ld125 := ldall) (ev185 := evsp) (ld222 := ldh)
      (he242 := hr0) (he243 := hh0) .. =>
    cases hr0; cases hh0
    injection hv with _ _ hl
    injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
    injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
    subst h1 h2 h3 h4 h5
    obtain rfl := binop_add_nat op1
    obtain rfl := binop_add_nat op2
    obtain rfl := binop_add_nat op3
    obtain ⟨rfl, E', hpeel, hE'⟩ := peel_n_foralls_tmOExact (np + nmot + nmin + ni) (by omega)
      evp hTy
    obtain ⟨D, B, ℓ, rfl, hD, -, -⟩ := TmOExact.forallE_of_load hE' ldall
    obtain ⟨xhd', xargs', hd, args, htup, hhd, -, hmk, -⟩ := collect_spine_tmOExact evsp hD
    injection htup with hl'; injection hl' with h1' hl'; injection hl' with h2'; subst h1' h2'
    obtain ⟨pa, us, rfl, -, rus⟩ := TmOExact.const_of_load hhd ldh
    exact ⟨D, pa, us, by simp [binderDomAfter, hpeel], by rw [← hmk, getAppFn_mkAppN_const], rus⟩
  | .Rec_Forall_other (x_major_ty := xmaj) (hv15 := hv) (op109 := op1) (op101 := op2) (op93 := op3)
      (ev131 := evp) (ld125 := ldall) (ev185 := evsp) (ld222 := ldh) (hne245 := hne) .. =>
    injection hv with _ _ hl
    injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
    injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
    subst h1 h2 h3 h4 h5
    obtain rfl := binop_add_nat op1
    obtain rfl := binop_add_nat op2
    obtain rfl := binop_add_nat op3
    obtain ⟨rfl, -, -, -⟩ := peel_n_foralls_tmOExact (np + nmot + nmin + ni) (by omega) evp hTy
    have hv_eq := peel_n_foralls_det (by omega) ext0h evp0 evp
    subst hv_eq
    have hxm_eq : xm0 = xmaj := by
      have hld := (loadValue_mono ext0h ldall0).symm.trans ldall
      simp only [Except.ok.injEq, Value.construct.injEq, List.cons.injEq] at hld
      exact hld.2.2.1
    subst hxm_eq
    have hhd_eq := collect_spine_det_head ext0h evsp0 evsp
    subst hhd_eq
    have ldh' := (loadValue_mono (hext1.trans evsp.heap_extends) ldh0).symm.trans ldh
    injection ldh' with hc'
    exact (hne _ rfl hc'.symm).elim
  | .Rec_other (hv15 := hv) (op109 := op1) (op101 := op2) (op93 := op3)
      (ev131 := evp) (ld125 := ldall) (hne259 := hne) .. =>
    injection hv with _ _ hl
    injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
    injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
    subst h1 h2 h3 h4 h5
    obtain rfl := binop_add_nat op1
    obtain rfl := binop_add_nat op2
    obtain rfl := binop_add_nat op3
    obtain ⟨rfl, -, -, -⟩ := peel_n_foralls_tmOExact (np + nmot + nmin + ni) (by omega) evp hTy
    have hv_eq := peel_n_foralls_det (by omega) ext0h evp0 evp
    subst hv_eq
    have hld := (loadValue_mono ext0h ldall0).symm.trans ldall
    injection hld with hc'
    exact (hne _ rfl hc'.symm).elim
  | .other (hne272 := hne) .. => exact (hne _ rfl rfl).elim

/-- **`KernelCheck::aux_already_in`** decides `auxEntryIn acc (ixAddr a) sp us` on
`FlatEntryRepExact`. -/
theorem aux_already_in_spec {κ : _root_.Address → KKey} (hinj : Function.Injective κ) :
    ∀ (acc : List FlatEntry) {a : Bytes.Address} {sp : List KExpr} {us : List KLevel}
      {xflat xa xsp xus r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelCheck::aux_already_in" [xflat, xa, xsp, xus] h r h' cs →
      Bounded cs →
      RepList flatListEnum (FlatEntryRepExact κ) h acc xflat →
      Bytes.RepAddressRef addrTy h a xa →
      RepList kexprListEnum (TmOExact κ) h sp xsp →
      RepKLevelList h us xus →
      r = .field (if auxEntryIn acc (ixAddr a) sp us then 1 else 0) := by
  intro acc
  induction acc with
  | nil =>
    intro a sp us xflat xa xsp xus r h h' cs ev _ hacc _ _ _
    match Obs.«KernelCheck::aux_already_in».obs ev with
    | .Nil (he20 := hr0) .. => cases hr0; rfl
    | .Cons_n1_n1_n1 (ld12 := ld) .. | .Cons_n1_n1_other (ld12 := ld) ..
    | .Cons_n1_other (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hacc ld
      cases hcons
  | cons e rest ih =>
    intro a sp us xflat xa xsp xus r h h' cs ev hbnd hacc ra hsp hus
    have bnd : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelCheck::aux_already_in».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hacc ld
    | .Cons_n1_n1_n1 (ld12 := ld) (ev104 := evaeq) (ev_bdqzbgud := evsp) (ev_purmzcuq := evus)
        (op_irtiosum := op2) (he160 := hr0) (hc162 := hc) .. =>
      cases hr0
      obtain ⟨e', rest', h1, he', -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hacc ld
      injection h1 with h1e h1r; subst h1e h1r
      obtain ⟨xea', xes', xeu', ae, htup, rae, hae, hspe, huse⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4; subst h1 h3 h4
      have haux : e.aux = true := auxVal_eq_one.mp h2.symm
      obtain ⟨hva, rfl⟩ := Lib.address_eq_spec evaeq rae ra
      have haeq : ae = a := by
        by_contra hne; rw [ite_eq_right hne] at hva; exact absurd (Value.field.inj hva) (by decide)
      subst haeq
      have hsp_eq := spec_params_zeta_eq_exact hinj hspe hsp
        (bnd fun c hc' => by rw [hc]; simp [hc']) evsp
      obtain ⟨hus_eq, -⟩ := level_list_struct_eq_exact
        (huse.mono evsp.heap_extends) (hus.mono evsp.heap_extends) evus
      have hsu : e.params = sp ∧ e.levels = us := by
        by_cases h1 : e.params = sp <;> by_cases h2 : e.levels = us
        · exact ⟨h1, h2⟩
        all_goals
          rw [hsp_eq, hus_eq] at op2
          simp [h1, h2, evalBinOp] at op2
      simp [auxEntryIn, haux, hae, hsu.1, hsu.2]
    | .Cons_n1_n1_other (ld12 := ld) (ev104 := evaeq) (ev_bdqzbgud := evsp) (ev_purmzcuq := evus)
        (op_irtiosum := op2) (hne163 := hne) (ev172 := evrec) (hc197 := hc) .. =>
      obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hacc ld
      injection h1 with h1e h1r; subst h1e h1r
      obtain ⟨xea', xes', xeu', ae, htup, rae, hae, hspe, huse⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4; subst h1 h3 h4
      have haux : e.aux = true := auxVal_eq_one.mp h2.symm
      obtain ⟨hva, rfl⟩ := Lib.address_eq_spec evaeq rae ra
      have haeq : ae = a := by
        by_contra hne'; rw [ite_eq_right hne'] at hva
        exact absurd (Value.field.inj hva) (by decide)
      subst haeq
      have hsp_eq := spec_params_zeta_eq_exact hinj hspe hsp
        (bnd fun c hc' => by rw [hc]; simp [hc']) evsp
      obtain ⟨hus_eq, rfl⟩ := level_list_struct_eq_exact
        (huse.mono evsp.heap_extends) (hus.mono evsp.heap_extends) evus
      have hne_su : (e.params == sp && e.levels == us) = false := by
        by_cases h1 : e.params = sp <;> by_cases h2 : e.levels = us
        · rw [hsp_eq, hus_eq] at op2; simp [h1, h2, evalBinOp] at op2; exact (hne op2.symm).elim
        · simp [beq_eq_false_iff_ne.mpr h2]
        · simp [beq_eq_false_iff_ne.mpr h1]
        · simp [beq_eq_false_iff_ne.mpr h1]
      have ext := evsp.heap_extends
      have hrec := ih evrec (bnd fun c hc' => by rw [hc]; simp [hc'])
        (flatList_mono ext hrest) (Bytes.repAddressRef_heapMono₂ addrTy ext ra)
        (tmOExactList_mono ext hsp) (hus.mono ext)
      rw [hrec]; simp [auxEntryIn, haux, hae, hne_su]
    | .Cons_n1_other (ld12 := ld) (ev104 := evaeq) (hne198 := hne) (ev207 := evrec)
        (hc232 := hc) .. =>
      obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hacc ld
      injection h1 with h1e h1r; subst h1e h1r
      obtain ⟨xea', xes', xeu', ae, htup, rae, hae, -, -⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 _
      subst h1
      obtain ⟨hva, rfl⟩ := Lib.address_eq_spec evaeq rae ra
      have hdiff : e.addr ≠ ixAddr a := by
        rw [← hae]; intro he; have hsame := ixAddr_inj he
        rw [ite_eq_left hsame] at hva; exact hne hva
      have hrec := ih evrec (bnd fun c hc' => by rw [hc]; simp [hc']) hrest ra hsp hus
      rw [hrec]; simp [auxEntryIn, beq_eq_false_iff_ne.mpr hdiff]
    | .Cons_other (x_is_aux := xaux) (ld12 := ld) (hne233 := hne) (ev242 := evrec)
        (hc267 := hc) .. =>
      obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hacc ld
      injection h1 with h1e h1r; subst h1e h1r
      have hcopy := he'
      obtain ⟨_, _, _, _, htup, -, -, -, -⟩ := hcopy
      injection htup with hl; injection hl with _ hl; injection hl with h2 _
      have hf : e.aux = false := by
        cases h : e.aux
        · rfl
        · exact (hne (h2.trans (auxVal_eq_one.mpr h))).elim
      have hrec := ih evrec (bnd fun c hc' => by rw [hc]; simp [hc']) hrest ra hsp hus
      rw [hrec]; simp [auxEntryIn, hf]

/-! ## Pure models for `primary_parent_block_of` and `build_flat_block` -/

/-- Pure model of `KernelCheck::first_recr_parent_block`: finds the first `Recr` member in
`cur`, extracts its major-premise head constant's parent block, or returns `fallback`. -/
noncomputable def firstRecrParentBlock (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (rb : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst)
    (fallback : _root_.Address) : Nat → List Ixon.MutConst → Option _root_.Address
  | _, [] => some fallback
  | pos, .recr r :: _ =>
    match loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
        (mutsRoot rs pos) r.typ with
    | none => none
    | some ty =>
      match binderDomAfter (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat) ty with
      | none => none
      | some d =>
        match d.getAppFn with
        | .const k _ =>
          match keyAddr t k with
          | none => none
          | some paddr =>
            match indInfoAt E₀ paddr with
            | none => none
            | some none => some fallback
            | some (some info) => some info.blk
        | _ => none
  | pos, _ :: rest => firstRecrParentBlock t E₀ rb crb rs fallback (pos + 1) rest

/-- When `rs[0]` is a `Recr` whose major premise is headed by an `Induct`, `firstRecrParentBlock`
returns that inductive's block regardless of `fallback`. -/
theorem firstRecrParentBlock_indep_fallback {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {fb₁ fb₂ prim : _root_.Address} {r₀ : Ixon.Recursor} {ty₀ d₀ : KExpr} {k : KKey}
    {us : List KLevel} {paddr : _root_.Address} {info : IndInfo}
    (h0 : rs[0]? = some (.recr r₀))
    (hty : loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r₀.lvls.toNat
      (mutsRoot rs 0) r₀.typ = some ty₀)
    (hd : binderDomAfter (r₀.params.toNat + r₀.motives.toNat + r₀.minors.toNat + r₀.indices.toNat)
      ty₀ = some d₀)
    (hfn : d₀.getAppFn = .const k us) (hka : keyAddr t k = some paddr)
    (hinfo : indInfoAt E₀ paddr = some (some info)) :
    firstRecrParentBlock t E₀ rb crb rs fb₁ 0 rs.toList = some info.blk ∧
    firstRecrParentBlock t E₀ rb crb rs fb₂ 0 rs.toList = some info.blk := by
  have hcons : ∃ rest, rs.toList = .recr r₀ :: rest := by
    cases h : rs.toList with
    | nil =>
      have : rs[0]? = none := by rw [← Array.getElem?_toList, h]; rfl
      rw [this] at h0; cases h0
    | cons m rest =>
      have : rs[0]? = some m := by rw [← Array.getElem?_toList, h]; rfl
      rw [this] at h0; injection h0 with hm; subst hm; exact ⟨rest, rfl⟩
  obtain ⟨rest, hlist⟩ := hcons
  simp only [hlist, firstRecrParentBlock, hty, hd, hfn, hka, hinfo, and_self]

/-- Pure model of `KernelCheck::aux_from_recrs_walk_ex`: appends auxiliary entries `(paddr, true,
sp, us)` for each `Recr` member whose major-premise head inductive belongs to a block other than
`prim`. -/
noncomputable def buildFlatAuxStep (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (rb : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst)
    (prim : _root_.Address) : Nat → List Ixon.MutConst → List FlatEntry → Option (List FlatEntry)
  | _, [], acc => some acc
  | pos, .recr r :: rest, acc =>
    match loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
        (mutsRoot rs pos) r.typ with
    | none => none
    | some ty =>
      match binderDomAfter (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat) ty with
      | none => none
      | some d =>
        match d.getAppFn with
        | .const k us =>
          match keyAddr t k with
          | none => none
          | some paddr =>
            match indInfoAt E₀ paddr with
            | none => none
            | some none => buildFlatAuxStep t E₀ rb crb rs prim (pos + 1) rest acc
            | some (some info) =>
              if info.blk == prim then
                buildFlatAuxStep t E₀ rb crb rs prim (pos + 1) rest acc
              else
                let sp := ((d.getAppArgs).take info.np).map
                  (Ix.Kernel.Expr.lowerBVars (r.motives.toNat + r.minors.toNat + r.indices.toNat) 0)
                let acc' := if auxEntryIn acc paddr sp us then acc
                            else acc ++ [⟨paddr, true, sp, us⟩]
                buildFlatAuxStep t E₀ rb crb rs prim (pos + 1) rest acc'
        | _ => none
  | pos, _ :: rest, acc => buildFlatAuxStep t E₀ rb crb rs prim (pos + 1) rest acc

theorem buildFlatAuxStep_append_aux {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {prim : _root_.Address} :
    ∀ (cur : List Ixon.MutConst) (pos : Nat) (acc res : List FlatEntry),
      buildFlatAuxStep t E₀ rb crb rs prim pos cur acc = some res →
      ∃ auxs : List FlatEntry, res = acc ++ auxs ∧ ∀ e ∈ auxs, e.aux = true := by
  intro cur
  induction cur with
  | nil =>
    intro pos acc res h
    simp only [buildFlatAuxStep, Option.some.injEq] at h
    exact ⟨[], by simp [h], fun _ hm => nomatch hm⟩
  | cons m rest ih =>
    intro pos acc res h
    cases m with
    | defn _ | indc _ => exact ih (pos + 1) acc res h
    | recr r =>
      unfold buildFlatAuxStep at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · split at h
            · cases h
            · split at h
              · cases h
              · exact ih (pos + 1) acc res h
              · split at h
                · exact ih (pos + 1) acc res h
                · dsimp only at h
                  split at h
                  · exact ih (pos + 1) acc res h
                  · obtain ⟨auxs, hres, hall⟩ := ih (pos + 1) _ res h
                    rw [List.append_assoc] at hres
                    refine ⟨_ :: auxs, hres, ?_⟩
                    intro e he
                    rcases List.mem_cons.mp he with rfl | hm
                    · rfl
                    · exact hall e hm
          · cases h

theorem buildFlatAuxStep_filter_nonAux {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {prim : _root_.Address} {cur : List Ixon.MutConst} {pos : Nat} {acc res : List FlatEntry}
    (h : buildFlatAuxStep t E₀ rb crb rs prim pos cur acc = some res) :
    res.filter (fun e => !e.aux) = acc.filter (fun e => !e.aux) := by
  obtain ⟨auxs, rfl, hall⟩ := buildFlatAuxStep_append_aux cur pos acc res h
  rw [List.filter_append]
  have hemp : auxs.filter (fun e => !e.aux) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he; simp [hall e he]
  rw [hemp, List.append_nil]

theorem buildFlatAuxStep_aux_mem {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {prim : _root_.Address} :
    ∀ (cur : List Ixon.MutConst) (pos : Nat) (acc res : List FlatEntry),
      buildFlatAuxStep t E₀ rb crb rs prim pos cur acc = some res →
      ∀ (j : Nat) (r : Ixon.Recursor) (ty d : KExpr) (k : KKey) (us : List KLevel)
        (paddr : _root_.Address) (info : IndInfo),
        cur[j]? = some (.recr r) →
        loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
          (mutsRoot rs (pos + j)) r.typ = some ty →
        binderDomAfter (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat)
          ty = some d →
        d.getAppFn = .const k us → keyAddr t k = some paddr →
        indInfoAt E₀ paddr = some (some info) → info.blk ≠ prim →
        ⟨paddr, true, ((d.getAppArgs).take info.np).map
          (Ix.Kernel.Expr.lowerBVars (r.motives.toNat + r.minors.toNat + r.indices.toNat) 0),
          us⟩ ∈ res := by
  intro cur
  induction cur with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ h; simp at h
  | cons m rest ih =>
    intro pos acc res hstep j r ty d k us paddr info hj hty hd hfn hka hinfo hne
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
      simp only [Nat.add_zero] at hty
      simp only [buildFlatAuxStep, hty, hd, hfn, hka, hinfo,
        beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte] at hstep
      set sp := ((d.getAppArgs).take info.np).map
        (Ix.Kernel.Expr.lowerBVars (r.motives.toNat + r.minors.toNat + r.indices.toNat) 0)
      by_cases hin : auxEntryIn acc paddr sp us = true
      · simp only [hin, ↓reduceIte] at hstep
        obtain ⟨auxs, rfl, -⟩ := buildFlatAuxStep_append_aux rest (pos + 1) acc res hstep
        obtain ⟨e, he, hpred⟩ := List.any_eq_true.mp hin
        simp only [Bool.and_eq_true, beq_iff_eq] at hpred
        have heq : e = ⟨paddr, true, sp, us⟩ := by
          cases e; simp only at hpred
          rcases hpred with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; subst h1 h2 h3 h4; rfl
        rw [← heq]; exact List.mem_append_left _ he
      · simp only [hin, ↓reduceIte] at hstep
        obtain ⟨auxs, rfl, -⟩ := buildFlatAuxStep_append_aux rest (pos + 1) _ res hstep
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hty' : loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
          (mutsRoot rs ((pos + 1) + j')) r.typ = some ty := by
        rwa [show (pos + 1) + j' = pos + (j' + 1) by omega]
      cases m with
      | defn _ | indc _ =>
        exact ih (pos + 1) acc res hstep j' r ty d k us paddr info hj hty' hd hfn hka hinfo hne
      | recr r₀ =>
        unfold buildFlatAuxStep at hstep
        split at hstep
        · cases hstep
        · split at hstep
          · cases hstep
          · split at hstep
            · split at hstep
              · cases hstep
              · split at hstep
                · cases hstep
                · exact ih (pos + 1) acc res hstep j' r ty d k us paddr info hj hty' hd hfn hka hinfo hne
                · split at hstep
                  · exact ih (pos + 1) acc res hstep j' r ty d k us paddr info hj hty' hd hfn hka hinfo hne
                  · exact ih (pos + 1) _ res hstep j' r ty d k us paddr info hj hty' hd hfn hka hinfo hne
            · cases hstep

private theorem first_recr_parent_block_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c') (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {rba fba : Bytes.Address} {crb cbF : Ixon.Constant} {rs msF : Array Ixon.MutConst}
    (hSrb : Held R (ixAddr rba)) (hcrbE : recordOf E₀ (ixAddr rba) = some crb)
    (hmuts : crb.info = .muts rs)
    (hSfb : Held R (ixAddr fba)) (hfbE : recordOf E₀ (ixAddr fba) = some cbF)
    (hfbMuts : cbF.info = .muts msF) :
    ∀ (cur : List Ixon.MutConst) (pos : Nat)
      {xall xcur xrba xfba r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ c ∈ cs, c ∈ rootCalls) →
      pos + cur.length = rs.size →
      (∀ i m, cur[i]? = some m → rs[pos + i]? = some m) →
      Core.Specs.Callees.MembersRep h rs.toList xall →
      Core.Specs.Callees.MembersRep h cur xcur →
      Bytes.RepAddressRef addrTy h rba xrba →
      Bytes.RepAddressRef addrTy h fba xfba →
      ObsFn W "KernelCheck::first_recr_parent_block"
        [xall, xcur, xrba, .field (pos : F), xfba] h r h' cs →
      ∃ (pba : Bytes.Address) (cprim : Ixon.Constant) (msp : Array Ixon.MutConst),
        firstRecrParentBlock t E₀ (ixAddr rba) crb rs (ixAddr fba) pos cur = some (ixAddr pba) ∧
        Bytes.RepAddressRef addrTy h' pba r ∧
        Held R (ixAddr pba) ∧
        recordOf E₀ (ixAddr pba) = some cprim ∧ cprim.info = .muts msp := by
  intro cur
  induction cur with
  | nil =>
    intro pos xall xcur xrba xfba r h h' cs _ _ _ _ hcur _ rfba ev
    match Obs.«KernelCheck::first_recr_parent_block».obs ev with
    | .Nil (he21 := hr0) (he22 := hh0) .. =>
      cases hr0; cases hh0
      exact ⟨fba, cbF, msF, rfl, rfba, hSfb, hfbE, hfbMuts⟩
    | .Cons_Recr_Rec_Induct (ld12 := ld) .. | .Cons_Recr_Rec_other (ld12 := ld) ..
    | .Cons_Recr_other (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      cases hcons
  | cons m rest ih =>
    intro pos xall xcur xrba xfba r h h' cs hsub hlen hidx hall hcur rrba rfba ev
    have hm_at : rs[pos]? = some m := by simpa using hidx 0 m rfl
    have hidx' : ∀ i m', rest[i]? = some m' → rs[(pos + 1) + i]? = some m' := fun i m' hi => by
      have h1 := hidx (i + 1) m' (by simpa using hi)
      rwa [show pos + (i + 1) = (pos + 1) + i by omega] at h1
    have hsub' : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → ∀ c ∈ cs', c ∈ rootCalls :=
      fun hs c hc => hsub c (hs c hc)
    match Obs.«KernelCheck::first_recr_parent_block».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hcur ld
    | .Cons_Recr_Rec_Induct (v63 := vp) (m64 := m1) (cs74 := cs1) (m102 := m2) (p109 := pci1)
        (cs115 := cs2) (x_ty := xty) (x_np := xnp) (x_ni := xni) (x_nmot := xnmot)
        (x_nmin := xnmin) (v203 := xpaddr) (m204 := m3) (cs214 := cs3)
        (m258 := m4) (p265 := pci2) (cs271 := cs4) (x_pb := xpb)
        (ld12 := ld) (ev76 := evpa) (ev117 := evci1) (ld111 := ldci1)
        (ev216 := evpar) (ev273 := evci2) (ld267 := ldci2) (he346 := hr0) (he347 := hh0)
        (hc348 := hc) .. =>
      cases hr0; cases hh0
      obtain ⟨m', rest', h1, hm', -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      injection h1 with h1m h1r; subst h1m h1r
      cases m with
      | defn _ | indc _ => obtain ⟨_, hshape⟩ := hm'; simp [Core.Specs.Callees.mutCtor] at hshape
      | recr rc =>
        have hrs_lt : rs.size < 2 ^ 39 := by
          have hlt := repList_length_lt_of_obs hbd hsub evpa (by rw [hc]; simp) (by simp) hall
          simpa using hlt
        have hpos_lt : pos < 2 ^ 39 := by
          have := (Array.getElem?_eq_some_iff.mp hm_at).1; omega
        obtain ⟨ext1, -, -, mc, ma, hmc, rma, hma⟩ := L1.projection_addr_spec hall rrba evpa
        rw [fval_natCast (by omega)] at hmc hma
        have hmc' : rs[pos]? = some mc := by rw [← Array.getElem?_toList]; exact hmc
        have hmc_eq : mc = .recr rc := Option.some.inj (hmc'.symm.trans hm_at)
        subst hmc_eq
        have hma_eq : ixAddr ma = memberAddr (ixAddr rba) pos (.recr rc) := hma
        obtain ⟨ty, tyPtr, rulesPtr, blkPtr, ba', hshape, -, hnp, hni, hnm, hnmi, -,
          hloaded, htm, htyIn, -, -, -⟩ :=
          recrLoad_ofStore ht hwf hS hH hbd hRagree hcl hlv
            (hsub' fun c hc' => by rw [hc]; simp [hc']) hSrb hcrbE hmuts hm_at hma_eq rma
            evci1 ldci1
        injection hshape with _ _ hl
        injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
        injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
        subst h1 h2 h3 h4 h5
        obtain ⟨d, pa, us, hd_at, hfn, rpa, -⟩ := rec_to_parent_addr_spec (by omega) htm evpar
        have hdIn := addrIn_binderDomAfter htyIn hd_at
        have hfnIn := addrIn_getAppFn hdIn
        rw [hfn] at hfnIn
        have hSpa : Held R (ixAddr pa) := hfnIn (ixAddr pa) rfl
        obtain ⟨hInd, -⟩ := indInfo_of_get_ci hS hH hbd hRagree hcl
          (hsub' fun c hc' => by rw [hc]; simp [hc']) hSpa rpa evci2 ldci2
        obtain ⟨info, pba, hinfo, -, -, -, -, hSblk, -, -, -, hpba, rpba, -⟩ :=
          hInd _ _ _ _ _ _ _ _ rfl
        have hblk_muts : ∃ cprim msp, recordOf E₀ info.blk = some cprim ∧ cprim.info = .muts msp := by
          unfold indInfoAt at hinfo
          cases hrc : recordOf E₀ (ixAddr pa) with
          | none => simp [hrc] at hinfo
          | some c =>
            rw [hrc] at hinfo
            cases hci : c.info with
            | iPrj p =>
              simp only [hci] at hinfo
              cases hcb' : recordOf E₀ p.block with
              | none => simp [hcb'] at hinfo
              | some cb =>
                rw [hcb'] at hinfo
                cases hcbi : cb.info with
                | muts ms =>
                  simp only [hcbi] at hinfo
                  cases hms' : ms[p.idx.toNat]? with
                  | none => simp [hms'] at hinfo
                  | some mc' =>
                    cases mc' with
                    | indc _ =>
                      simp only [hms', Option.some.injEq] at hinfo
                      subst hinfo; exact ⟨cb, ms, hcb', hcbi⟩
                    | _ => simp [hms'] at hinfo
                | _ => simp [hcbi] at hinfo
            | _ => simp [hci] at hinfo
        obtain ⟨cprim, msp, hcprim, hmsp⟩ := hblk_muts
        have hka : keyAddr t (Core.keyOf t (ixAddr pa)) = some (ixAddr pa) :=
          addrOf_ofStore (E₀ := E₀) hwf (ixAddr pa)
        exact ⟨pba, cprim, msp,
          by simp only [firstRecrParentBlock, hloaded, hd_at, hfn, hka, hinfo, hpba],
          rpba, hpba.symm ▸ hSblk, hpba.symm ▸ hcprim, hmsp⟩
    | .Cons_Recr_Rec_other (v63 := vp) (m64 := m1) (cs74 := cs1) (m102 := m2) (p109 := pci1)
        (cs115 := cs2) (x_ty := xty) (x_np := xnp) (x_ni := xni) (x_nmot := xnmot)
        (x_nmin := xnmin) (v203 := xpaddr) (m204 := m3) (cs214 := cs3)
        (m258 := m4) (p265 := pci2) (cs271 := cs4)
        (ld12 := ld) (ev76 := evpa) (ev117 := evci1) (ld111 := ldci1)
        (ev216 := evpar) (ev273 := evci2) (ld267 := ldci2) (hne349 := hneI)
        (he354 := hr0) (he355 := hh0) (hc356 := hc) .. =>
      cases hr0; cases hh0
      obtain ⟨m', rest', h1, hm', -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      injection h1 with h1m h1r; subst h1m h1r
      cases m with
      | defn _ | indc _ => obtain ⟨_, hshape⟩ := hm'; simp [Core.Specs.Callees.mutCtor] at hshape
      | recr rc =>
        have hrs_lt : rs.size < 2 ^ 39 := by
          have hlt := repList_length_lt_of_obs hbd hsub evpa (by rw [hc]; simp) (by simp) hall
          simpa using hlt
        have hpos_lt : pos < 2 ^ 39 := by
          have := (Array.getElem?_eq_some_iff.mp hm_at).1; omega
        obtain ⟨ext1, -, -, mc, ma, hmc, rma, hma⟩ := L1.projection_addr_spec hall rrba evpa
        rw [fval_natCast (by omega)] at hmc hma
        have hmc' : rs[pos]? = some mc := by rw [← Array.getElem?_toList]; exact hmc
        have hmc_eq : mc = .recr rc := Option.some.inj (hmc'.symm.trans hm_at)
        subst hmc_eq
        have hma_eq : ixAddr ma = memberAddr (ixAddr rba) pos (.recr rc) := hma
        obtain ⟨ty, tyPtr, rulesPtr, blkPtr, ba', hshape, -, hnp, hni, hnm, hnmi, -,
          hloaded, htm, htyIn, -, -, -⟩ :=
          recrLoad_ofStore ht hwf hS hH hbd hRagree hcl hlv
            (hsub' fun c hc' => by rw [hc]; simp [hc']) hSrb hcrbE hmuts hm_at hma_eq rma
            evci1 ldci1
        injection hshape with _ _ hl
        injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
        injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
        subst h1 h2 h3 h4 h5
        obtain ⟨d, pa, us, hd_at, hfn, rpa, -⟩ := rec_to_parent_addr_spec (by omega) htm evpar
        have hdIn := addrIn_binderDomAfter htyIn hd_at
        have hfnIn := addrIn_getAppFn hdIn
        rw [hfn] at hfnIn
        have hSpa : Held R (ixAddr pa) := hfnIn (ixAddr pa) rfl
        obtain ⟨-, hOther⟩ := indInfo_of_get_ci hS hH hbd hRagree hcl
          (hsub' fun c hc' => by rw [hc]; simp [hc']) hSpa rpa evci2 ldci2
        have hinfo := hOther hneI
        have hka : keyAddr t (Core.keyOf t (ixAddr pa)) = some (ixAddr pa) :=
          addrOf_ofStore (E₀ := E₀) hwf (ixAddr pa)
        have ext := ext1.trans (evci1.heap_extends.trans (evpar.heap_extends.trans evci2.heap_extends))
        exact ⟨fba, cbF, msF,
          by simp only [firstRecrParentBlock, hloaded, hd_at, hfn, hka, hinfo],
          Bytes.repAddressRef_heapMono₂ addrTy ext rfba, hSfb, hfbE, hfbMuts⟩
    | .Cons_Recr_other (v63 := vp) (m64 := m1) (cs74 := cs1) (m102 := m2) (p109 := pci1)
        (cs115 := cs2) (ld12 := ld) (ev76 := evpa) (ev117 := evci1) (ld111 := ldci1)
        (hne357 := hneR) (hc364 := hc) .. =>
      obtain ⟨m', rest', h1, hm', -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      injection h1 with h1m h1r; subst h1m h1r
      cases m with
      | defn _ | indc _ => obtain ⟨_, hshape⟩ := hm'; simp [Core.Specs.Callees.mutCtor] at hshape
      | recr rc =>
        have hrs_lt : rs.size < 2 ^ 39 := by
          have hlt := repList_length_lt_of_obs hbd hsub evpa (by rw [hc]; simp) (by simp) hall
          simpa using hlt
        have hpos_lt : pos < 2 ^ 39 := by
          have := (Array.getElem?_eq_some_iff.mp hm_at).1; omega
        obtain ⟨-, -, -, mc, ma, hmc, rma, hma⟩ := L1.projection_addr_spec hall rrba evpa
        rw [fval_natCast (by omega)] at hmc hma
        have hmc' : rs[pos]? = some mc := by rw [← Array.getElem?_toList]; exact hmc
        have hmc_eq : mc = .recr rc := Option.some.inj (hmc'.symm.trans hm_at)
        subst hmc_eq
        have hma_eq : ixAddr ma = memberAddr (ixAddr rba) pos (.recr rc) := hma
        obtain ⟨_, _, _, _, _, hshape, -⟩ := recrLoad_ofStore ht hwf hS hH hbd hRagree hcl hlv
          (hsub' fun c hc' => by rw [hc]; simp [hc']) hSrb hcrbE hmuts hm_at hma_eq rma
          evci1 ldci1
        exact (hneR _ rfl hshape).elim
    | .Cons_other (x_m := xm) (x_rest := xrest) (cs372 := cs1) (v378 := vpos1) (ld12 := ld)
        (hne365 := hne) (op414 := op1) (ev374 := evrec) (hc423 := hc) .. =>
      obtain ⟨m', rest', h1, hm', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      injection h1 with h1m h1r; subst h1m h1r
      cases m with
      | recr _ => obtain ⟨_, hshape⟩ := hm'; exact (hne _ rfl hshape).elim
      | defn _ | indc _ =>
        obtain rfl := binop_add_one_nat op1
        obtain ⟨pba, cprim, msp, hfrp, rpba, hSp, hcprim, hmsp⟩ := ih (pos + 1)
          (hsub' fun c hc' => by rw [hc]; simp [hc']) (by simp at hlen; omega) hidx'
          hall hrest rrba rfba evrec
        exact ⟨pba, cprim, msp, by simpa [firstRecrParentBlock] using hfrp,
          rpba, hSp, hcprim, hmsp⟩

/-- **`KernelCheck::primary_parent_block_of`** on a `Muts` recursor block `rb` and `Muts`
fallback block `fb` computes `firstRecrParentBlock t E₀ rb crb rs fb 0 rs.toList` and returns a
`Muts` block held in `R`. -/
theorem primary_parent_block_of_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c') (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {rba fba : Bytes.Address} {crb cbF : Ixon.Constant} {rs msF : Array Ixon.MutConst}
    {xrba xfba r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (hSrb : Held R (ixAddr rba)) (hcrbE : recordOf E₀ (ixAddr rba) = some crb)
    (hmuts : crb.info = .muts rs)
    (hSfb : Held R (ixAddr fba)) (hfbE : recordOf E₀ (ixAddr fba) = some cbF)
    (hfbMuts : cbF.info = .muts msF)
    (rrba : Bytes.RepAddressRef addrTy h rba xrba)
    (rfba : Bytes.RepAddressRef addrTy h fba xfba)
    (ev : ObsFn W "KernelCheck::primary_parent_block_of" [xrba, xfba] h r h' cs) :
    ∃ (pba : Bytes.Address) (cprim : Ixon.Constant) (msp : Array Ixon.MutConst),
      firstRecrParentBlock t E₀ (ixAddr rba) crb rs (ixAddr fba) 0 rs.toList = some (ixAddr pba) ∧
      Bytes.RepAddressRef addrTy h' pba r ∧
      Held R (ixAddr pba) ∧
      recordOf E₀ (ixAddr pba) = some cprim ∧ cprim.info = .muts msp := by
  match Obs.«KernelCheck::primary_parent_block_of».obs ev with
  | .Muts (m2 := m2) (cs12 := cs1) (x_members := xmem) (cs92 := cs2)
      (ev14 := evld) (ev94 := evfirst) (hc134 := hc) .. =>
    obtain ⟨xm, _, _, _, _, hv, hms⟩ := load_verified_muts_of_record hS
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcrbE hmuts rrba evld
    injection hv with _ _ hl; injection hl with hm _; injection hm with _ _ hml
    injection hml with hx; subst hx
    have evfirst' : ObsFn W "KernelCheck::first_recr_parent_block"
        [xmem, xmem, xrba, .field ((0 : Nat) : F), xfba] m2 r h' cs2 := by simpa using evfirst
    exact first_recr_parent_block_spec ht hwf hS hH hbd hRagree hcl hlv
      hSrb hcrbE hmuts hSfb hfbE hfbMuts rs.toList 0
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) (by simp)
      (fun i m hm => by simpa [← Array.getElem?_toList] using hm)
      hms hms (Bytes.repAddressRef_heapMono₂ addrTy evld.heap_extends rrba)
      (Bytes.repAddressRef_heapMono₂ addrTy evld.heap_extends rfba) evfirst'
  | .other (cs12 := cs1) (ev14 := evld) (hne135 := hne) (hc142 := hc) .. =>
    obtain ⟨xm, _, _, _, _, hv, -⟩ := load_verified_muts_of_record hS
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcrbE hmuts rrba evld
    injection hv with _ _ hl; injection hl with hm _
    exact (hne [xm] rfl hm).elim

private theorem aux_from_recrs_walk_ex_spec {rootCalls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c') (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {rba pba : Bytes.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst} {off : Nat}
    (hSrb : Held R (ixAddr rba)) (hcrbE : recordOf E₀ (ixAddr rba) = some crb)
    (hmuts : crb.info = .muts rs) :
    ∀ (cur : List Ixon.MutConst) (pos : Nat) (acc : List FlatEntry)
      {xall xcur xrba xpba xacc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ c ∈ cs, c ∈ rootCalls) →
      pos + cur.length = rs.size →
      (∀ i m, cur[i]? = some m → rs[pos + i]? = some m) →
      Core.Specs.Callees.MembersRep h rs.toList xall →
      Core.Specs.Callees.MembersRep h cur xcur →
      Bytes.RepAddressRef addrTy h rba xrba →
      Bytes.RepAddressRef addrTy h pba xpba →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h acc xacc →
      (∀ e ∈ acc, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) →
      ObsFn W "KernelCheck::aux_from_recrs_walk_ex"
        [xall, xcur, xrba, xpba, .field (off : F), xacc, .field (pos : F)] h r h' cs →
      ∃ res : List FlatEntry,
        buildFlatAuxStep t E₀ (ixAddr rba) crb rs (ixAddr pba) pos cur acc = some res ∧
        RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h' res r ∧
        (∀ e ∈ res, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) := by
  intro cur
  induction cur with
  | nil =>
    intro pos acc xall xcur xrba xpba xacc r h h' cs _ _ _ _ hcur _ _ hacc haccS ev
    match Obs.«KernelCheck::aux_from_recrs_walk_ex».obsx ev with
    | .Nil (he21 := hr0) (he22 := hh0) .. => cases hr0; cases hh0; exact ⟨acc, rfl, hacc, haccS⟩
    | .Cons_Recr_n0_other_other_other_other (ld12 := ld) ..
    | .Cons_Recr_other_bind_other_bind_bind_n1 (ld12 := ld) ..
    | .Cons_Recr_other_bind_other_bind_bind_other (ld12 := ld) ..
    | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      cases hcons
  | cons m rest ih =>
    intro pos acc xall xcur xrba xpba xacc r h h' cs hsub hlen hidx hall hcur rrba rpba hacc haccS ev
    have hm_at : rs[pos]? = some m := by simpa using hidx 0 m rfl
    have hidx' : ∀ i m', rest[i]? = some m' → rs[(pos + 1) + i]? = some m' := fun i m' hi => by
      have h1 := hidx (i + 1) m' (by simpa using hi)
      rwa [show pos + (i + 1) = (pos + 1) + i by omega] at h1
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → ∀ c ∈ cs', c ∈ rootCalls :=
      fun hs c hc => hsub c (hs c hc)
    have hinj : Function.Injective (Core.keyOf t) := fun _ _ he => Core.keyOf_inj hwf he
    match Obs.«KernelCheck::aux_from_recrs_walk_ex».obsx ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hcur ld
    | .Cons_Recr_n0_other_other_other_other (x_rest := xrest) (v63 := vp) (m64 := m1)
        (cs74 := cs1) (v101 := vci) (m102 := m2) (p109 := pci) (cs115 := cs2)
        (m559 := m3) (cs561 := cs3) (cs617 := cs4) (v626 := vpos1)
        (ld12 := ld) (ev76 := evpa) (ev117 := evci) (ld111 := ldci) (sg566 := sg)
        (op682 := op1) (ev619 := evrec) (hc684 := hc) .. =>
      obtain ⟨m', rest', h1, hm', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      injection h1 with h1m h1r; subst h1m h1r
      cases m with
      | defn _ | indc _ => obtain ⟨_, hshape⟩ := hm'; simp [Core.Specs.Callees.mutCtor] at hshape
      | recr rc =>
        have hrs_lt : rs.size < 2 ^ 39 := by
          have hlt := repList_length_lt_of_obs hbd hsub evpa (by rw [hc]; simp) (by simp) hall
          simpa using hlt
        have hpos_lt : pos < 2 ^ 39 := by
          have := (Array.getElem?_eq_some_iff.mp hm_at).1; omega
        obtain ⟨ext1, -, -, mc, ma, hmc, rma, hma⟩ := L1.projection_addr_spec hall rrba evpa
        rw [fval_natCast (by omega)] at hmc hma
        have hmc' : rs[pos]? = some mc := by rw [← Array.getElem?_toList]; exact hmc
        have hmc_eq : mc = .recr rc := Option.some.inj (hmc'.symm.trans hm_at)
        subst hmc_eq
        have hma_eq : ixAddr ma = memberAddr (ixAddr rba) pos (.recr rc) := hma
        obtain ⟨ty, tyPtr, rulesPtr, blkPtr, ba', hshape, -, hnp, hni, hnm, hnmi, -,
          hloaded, htm, htyIn, -, -, -⟩ :=
          recrLoad_ofStore ht hwf hS hH hbd hRagree hcl hlv
            (sub fun c hc' => by rw [hc]; simp [hc']) hSrb hcrbE hmuts hm_at hma_eq rma evci ldci
        have ext02 := ext1.trans evci.heap_extends
        have hskip : Heap.Extends m2 m3 ∧
            ∃ d pa us, binderDomAfter
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) ty = some d ∧
              d.getAppFn = .const (Core.keyOf t (ixAddr pa)) us ∧
              (indInfoAt E₀ (ixAddr pa) = some none ∨
                ∃ info, indInfoAt E₀ (ixAddr pa) = some (some info) ∧ info.blk = ixAddr pba) := by
          cases sg with
          | Rec_Induct_n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              hv evpar evci2 ldci2 evaeq _ hh hcs =>
            subst hh
            rw [hshape] at hv; injection hv with _ _ hl
            injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
            injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
            subst h1 h2 h3 h4 h5
            obtain ⟨d, pa, us, hd_at, hfn, rpa, -⟩ := rec_to_parent_addr_spec (by omega) htm evpar
            have hSpa : Held R (ixAddr pa) := by
              have hfnIn := addrIn_getAppFn (addrIn_binderDomAfter htyIn hd_at)
              rw [hfn] at hfnIn; exact hfnIn (ixAddr pa) rfl
            obtain ⟨hInd, -⟩ := indInfo_of_get_ci hS hH hbd hRagree hcl
              (sub fun c hc' => by rw [hc, hcs]; simp [hc']) hSpa rpa evci2 ldci2
            obtain ⟨info, iba, hinfo, -, -, -, -, -, -, -, -, hiba, riba, -⟩ :=
              hInd _ _ _ _ _ _ _ _ rfl
            have ext23 := evpar.heap_extends.trans evci2.heap_extends
            obtain ⟨hveq, rfl⟩ := Lib.address_eq_spec evaeq riba
              (Bytes.repAddressRef_heapMono₂ addrTy (ext02.trans ext23) rpba)
            have hbeq : iba = pba := by
              by_contra hne; rw [ite_eq_right hne] at hveq
              exact absurd (Value.field.inj hveq) (by decide)
            exact ⟨ext23, d, pa, us, hd_at, hfn, .inr ⟨info, hinfo, hiba.symm.trans (congrArg ixAddr hbeq)⟩⟩
          | Rec_Induct_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ _ _ _ _ _ hr _ _ =>
            injection hr with hl; injection hl with h0 _
            exact absurd (Value.field.inj h0) (by decide)
          | Rec_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv evpar evci2 ldci2 hneI _ hh hcs =>
            subst hh
            rw [hshape] at hv; injection hv with _ _ hl
            injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
            injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
            subst h1 h2 h3 h4 h5
            obtain ⟨d, pa, us, hd_at, hfn, rpa, -⟩ := rec_to_parent_addr_spec (by omega) htm evpar
            have hSpa : Held R (ixAddr pa) := by
              have hfnIn := addrIn_getAppFn (addrIn_binderDomAfter htyIn hd_at)
              rw [hfn] at hfnIn; exact hfnIn (ixAddr pa) rfl
            obtain ⟨-, hOther⟩ := indInfo_of_get_ci hS hH hbd hRagree hcl
              (sub fun c hc' => by rw [hc, hcs]; simp [hc']) hSpa rpa evci2 ldci2
            exact ⟨evpar.heap_extends.trans evci2.heap_extends, d, pa, us, hd_at, hfn,
              .inl (hOther hneI)⟩
          | other hneR _ _ _ => exact (hneR _ rfl hshape).elim
        obtain ⟨ext23, d, pa, us, hd_at, hfn, hcase⟩ := hskip
        obtain rfl := binop_add_one_nat op1
        have ext03 := ext02.trans ext23
        obtain ⟨res, hres, hrep_res, hresS⟩ := ih (pos + 1) acc
          (sub fun c hc' => by rw [hc]; simp [hc']) (by simp at hlen; omega) hidx'
          (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext03 hall)
          (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext03 hrest)
          (Bytes.repAddressRef_heapMono₂ addrTy ext03 rrba)
          (Bytes.repAddressRef_heapMono₂ addrTy ext03 rpba)
          (flatList_mono ext03 hacc) haccS evrec
        have hka : keyAddr t (Core.keyOf t (ixAddr pa)) = some (ixAddr pa) :=
          addrOf_ofStore (E₀ := E₀) hwf (ixAddr pa)
        refine ⟨res, ?_, hrep_res, hresS⟩
        rcases hcase with hnone | ⟨info, hinfo, hblk⟩
        · simp only [buildFlatAuxStep, hloaded, hd_at, hfn, hka, hnone, hres]
        · simp only [buildFlatAuxStep, hloaded, hd_at, hfn, hka, hinfo, hblk, beq_self_eq_true,
            ↓reduceIte, hres]
    | .Cons_Recr_other_bind_other_bind_bind_n1 (x_rest := xrest) (v63 := vp) (m64 := m1)
        (cs74 := cs1) (v101 := vci) (m102 := m2) (p109 := pci) (cs115 := cs2)
        (m559 := m3) (cs561 := cs3) (x_parent_addr := xpa) (x_pnp := xpnp) (v718 := vsp)
        (m719 := m4) (cs729 := cs4) (v748 := vus) (m749 := m5) (cs759 := cs5)
        (m771 := m6) (cs782 := cs6) (cs816 := cs7) (v825 := vpos1)
        (ld12 := ld) (ev76 := evpa) (ev117 := evci) (ld111 := ldci) (sg566 := sg)
        (ev731 := evsp) (ev761 := evus) (ev784 := evin) (op881 := op1) (ev818 := evrec)
        (hc883 := hc) (hnt0 := hnt) .. =>
      obtain ⟨m', rest', h1, hm', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      injection h1 with h1m h1r; subst h1m h1r
      cases m with
      | defn _ | indc _ => obtain ⟨_, hshape⟩ := hm'; simp [Core.Specs.Callees.mutCtor] at hshape
      | recr rc =>
        have hrs_lt : rs.size < 2 ^ 39 := by
          have hlt := repList_length_lt_of_obs hbd hsub evpa (by rw [hc]; simp) (by simp) hall
          simpa using hlt
        have hpos_lt : pos < 2 ^ 39 := by
          have := (Array.getElem?_eq_some_iff.mp hm_at).1; omega
        obtain ⟨ext1, -, -, mc, ma, hmc, rma, hma⟩ := L1.projection_addr_spec hall rrba evpa
        rw [fval_natCast (by omega)] at hmc hma
        have hmc' : rs[pos]? = some mc := by rw [← Array.getElem?_toList]; exact hmc
        have hmc_eq : mc = .recr rc := Option.some.inj (hmc'.symm.trans hm_at)
        subst hmc_eq
        have hma_eq : ixAddr ma = memberAddr (ixAddr rba) pos (.recr rc) := hma
        obtain ⟨ty, tyPtr, rulesPtr, blkPtr, ba', hshape, -, hnp, hni, hnm, hnmi, -,
          hloaded, htm, htyIn, -, -, -⟩ :=
          recrLoad_ofStore ht hwf hS hH hbd hRagree hcl hlv
            (sub fun c hc' => by rw [hc]; simp [hc']) hSrb hcrbE hmuts hm_at hma_eq rma evci ldci
        have ext02 := ext1.trans evci.heap_extends
        -- Analyze `sg`: must be `Rec_Induct_other` since `hnt` rules out `0`!
        have haux_arm : ∃ (d : KExpr) (pa : Bytes.Address) (us : List KLevel) (info : IndInfo)
            (h_par : Heap F),
            Heap.Extends m2 h_par ∧ Heap.Extends h_par m3 ∧
            binderDomAfter (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
              ty = some d ∧
            d.getAppFn = .const (Core.keyOf t (ixAddr pa)) us ∧
            Bytes.RepAddressRef addrTy m3 pa xpa ∧ Held R (ixAddr pa) ∧
            indInfoAt E₀ (ixAddr pa) = some (some info) ∧ info.blk ≠ ixAddr pba ∧
            info.np < 72057594037927936 ∧ xpnp = .field (info.np : F) ∧
            MajorSpineIsConst h_par tyPtr
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) := by
          cases sg with
          | Rec_Induct_n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ _ _ _ _ hr _ _ => exact (hnt _ _ _ _ hr).elim
          | Rec_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ =>
            exact (hnt _ _ _ _ hr).elim
          | other _ hr _ _ => exact (hnt _ _ _ _ hr).elim
          | Rec_Induct_other _ _ _ _ _ _ _ _ _ _ _ _ m_par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              hv evpar evci2 ldci2 evaeq hne1 hr hh hcs =>
            subst hh
            rw [hshape] at hv; injection hv with _ _ hl
            injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
            injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
            subst h1 h2 h3 h4 h5
            injection hr with hrl; injection hrl with _ hrl; injection hrl with hxpa hrl
            injection hrl with _ hrl; injection hrl with hxpnp _; subst hxpa hxpnp
            obtain ⟨d, pa, us, hd_at, hfn, rpa, hmaj⟩ := rec_to_parent_addr_spec (by omega) htm evpar
            have hSpa : Held R (ixAddr pa) := by
              have hfnIn := addrIn_getAppFn (addrIn_binderDomAfter htyIn hd_at)
              rw [hfn] at hfnIn; exact hfnIn (ixAddr pa) rfl
            obtain ⟨hInd, -⟩ := indInfo_of_get_ci hS hH hbd hRagree hcl
              (sub fun c hc' => by rw [hc, hcs]; simp [hc']) hSpa rpa evci2 ldci2
            obtain ⟨info, iba, hinfo, -, hnp56, -, -, -, -, hnpEq, -, hiba, riba, -⟩ :=
              hInd _ _ _ _ _ _ _ _ rfl
            have ext23 := evpar.heap_extends.trans evci2.heap_extends
            obtain ⟨hveq, rfl⟩ := Lib.address_eq_spec evaeq riba
              (Bytes.repAddressRef_heapMono₂ addrTy (ext02.trans ext23) rpba)
            have hne_blk : info.blk ≠ ixAddr pba := fun h => by
              have : iba = pba := ixAddr_inj (hiba.trans h)
              rw [ite_eq_left this] at hveq; exact hne1 hveq
            exact ⟨d, pa, us, info, m_par, evpar.heap_extends, evci2.heap_extends,
              hd_at, hfn, Bytes.repAddressRef_heapMono₂ addrTy evci2.heap_extends rpa,
              hSpa, hinfo, hne_blk, hnp56, hnpEq, hmaj⟩
        obtain ⟨d, pa, us, info, h_par, ext2p, extp3, hd_at, hfn, rpa3, hSpa, hinfo, hne_blk,
          hnp56, rfl, hmaj⟩ := haux_arm
        subst hshape
        obtain ⟨d', hd_at', -, hrep_sp, hspIn⟩ := extract_aux_spec_params_from_rec_spec
          (by omega) hnp56 extp3 hmaj
          (RomBound.bounded_mono hbd (sub fun c hc' => by rw [hc]; simp [hc']))
          (htm.mono (ext2p.trans extp3)) htyIn evsp
        have hd_eq : d' = d := Option.some.inj (hd_at'.symm.trans hd_at)
        subst d'
        obtain ⟨d'', pa', us', hd_at'', hfn', hrep_us⟩ := extract_aux_occ_us_spec (by omega)
          (extp3.trans evsp.heap_extends) hmaj
          (htm.mono (ext2p.trans (extp3.trans evsp.heap_extends))) evus
        have hd_eq2 : d'' = d := Option.some.inj (hd_at''.symm.trans hd_at)
        subst d''
        have hfn_eq := hfn'.symm.trans hfn
        injection hfn_eq with _ hus_eq; subst us'
        have ext05 := ext02.trans (ext2p.trans (extp3.trans (evsp.heap_extends.trans evus.heap_extends)))
        have hin := aux_already_in_spec hinj acc evin
          (RomBound.bounded_mono hbd (sub fun c hc' => by rw [hc]; simp [hc']))
          (flatList_mono ext05 hacc)
          (Bytes.repAddressRef_heapMono₂ addrTy (evsp.heap_extends.trans evus.heap_extends) rpa3)
          (tmOExactList_mono evus.heap_extends hrep_sp) hrep_us
        set sp := (d.getAppArgs.take info.np).map
          (Ix.Kernel.Expr.lowerBVars (rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) 0)
        have hcond : auxEntryIn acc (ixAddr pa) sp us = true := by
          cases hcnd : auxEntryIn acc (ixAddr pa) sp us
          · rw [hcnd] at hin; exact absurd (Value.field.inj hin) (by decide)
          · rfl
        obtain rfl := binop_add_one_nat op1
        have ext06 := ext05.trans evin.heap_extends
        obtain ⟨res, hres, hrep_res, hresS⟩ := ih (pos + 1) acc
          (sub fun c hc' => by rw [hc]; simp [hc']) (by simp at hlen; omega) hidx'
          (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext06 hall)
          (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext06 hrest)
          (Bytes.repAddressRef_heapMono₂ addrTy ext06 rrba)
          (Bytes.repAddressRef_heapMono₂ addrTy ext06 rpba)
          (flatList_mono ext06 hacc) haccS evrec
        have hka : keyAddr t (Core.keyOf t (ixAddr pa)) = some (ixAddr pa) :=
          addrOf_ofStore (E₀ := E₀) hwf (ixAddr pa)
        refine ⟨res, ?_, hrep_res, hresS⟩
        simp only [buildFlatAuxStep, hloaded, hd_at, hfn, hka, hinfo,
          beq_eq_false_iff_ne.mpr hne_blk, Bool.false_eq_true, ↓reduceIte]
        change buildFlatAuxStep t E₀ (ixAddr rba) crb rs (ixAddr pba) (pos + 1) rest
          (if auxEntryIn acc (ixAddr pa) sp us = true then acc
            else acc ++ [⟨ixAddr pa, true, sp, us⟩]) = some res
        simp only [hcond, Bool.false_eq_true, ↓reduceIte, hres]
    | .Cons_Recr_other_bind_other_bind_bind_other (x_rest := xrest) (v63 := vp) (m64 := m1)
        (cs74 := cs1) (v101 := vci) (m102 := m2) (p109 := pci) (cs115 := cs2)
        (m559 := m3) (cs561 := cs3) (x_parent_addr := xpa) (x_pnp := xpnp) (v718 := vsp)
        (m719 := m4) (cs729 := cs4) (v748 := vus) (m749 := m5) (cs759 := cs5)
        (m771 := m6) (cs782 := cs6) (v888 := vacc') (m889 := m7) (cs899 := cs7)
        (cs953 := cs8) (v962 := vpos1)
        (ld12 := ld) (ev76 := evpa) (ev117 := evci) (ld111 := ldci) (sg566 := sg)
        (ev731 := evsp) (ev761 := evus) (ev784 := evin) (hne884 := hneIn)
        (ev901 := evsn) (op1018 := op1) (ev955 := evrec) (hc1020 := hc) (hnt0 := hnt) .. =>
      obtain ⟨m', rest', h1, hm', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      injection h1 with h1m h1r; subst h1m h1r
      cases m with
      | defn _ | indc _ => obtain ⟨_, hshape⟩ := hm'; simp [Core.Specs.Callees.mutCtor] at hshape
      | recr rc =>
        have hrs_lt : rs.size < 2 ^ 39 := by
          have hlt := repList_length_lt_of_obs hbd hsub evpa (by rw [hc]; simp) (by simp) hall
          simpa using hlt
        have hpos_lt : pos < 2 ^ 39 := by
          have := (Array.getElem?_eq_some_iff.mp hm_at).1; omega
        obtain ⟨ext1, -, -, mc, ma, hmc, rma, hma⟩ := L1.projection_addr_spec hall rrba evpa
        rw [fval_natCast (by omega)] at hmc hma
        have hmc' : rs[pos]? = some mc := by rw [← Array.getElem?_toList]; exact hmc
        have hmc_eq : mc = .recr rc := Option.some.inj (hmc'.symm.trans hm_at)
        subst hmc_eq
        have hma_eq : ixAddr ma = memberAddr (ixAddr rba) pos (.recr rc) := hma
        obtain ⟨ty, tyPtr, rulesPtr, blkPtr, ba', hshape, -, hnp, hni, hnm, hnmi, -,
          hloaded, htm, htyIn, -, -, -⟩ :=
          recrLoad_ofStore ht hwf hS hH hbd hRagree hcl hlv
            (sub fun c hc' => by rw [hc]; simp [hc']) hSrb hcrbE hmuts hm_at hma_eq rma evci ldci
        have ext02 := ext1.trans evci.heap_extends
        have haux_arm : ∃ (d : KExpr) (pa : Bytes.Address) (us : List KLevel) (info : IndInfo)
            (h_par : Heap F),
            Heap.Extends m2 h_par ∧ Heap.Extends h_par m3 ∧
            binderDomAfter (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
              ty = some d ∧
            d.getAppFn = .const (Core.keyOf t (ixAddr pa)) us ∧
            Bytes.RepAddressRef addrTy m3 pa xpa ∧ Held R (ixAddr pa) ∧
            indInfoAt E₀ (ixAddr pa) = some (some info) ∧ info.blk ≠ ixAddr pba ∧
            info.np < 72057594037927936 ∧ xpnp = .field (info.np : F) ∧
            MajorSpineIsConst h_par tyPtr
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) := by
          cases sg with
          | Rec_Induct_n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ _ _ _ _ hr _ _ => exact (hnt _ _ _ _ hr).elim
          | Rec_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ =>
            exact (hnt _ _ _ _ hr).elim
          | other _ hr _ _ => exact (hnt _ _ _ _ hr).elim
          | Rec_Induct_other _ _ _ _ _ _ _ _ _ _ _ _ m_par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              hv evpar evci2 ldci2 evaeq hne1 hr hh hcs =>
            subst hh
            rw [hshape] at hv; injection hv with _ _ hl
            injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
            injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
            subst h1 h2 h3 h4 h5
            injection hr with hrl; injection hrl with _ hrl; injection hrl with hxpa hrl
            injection hrl with _ hrl; injection hrl with hxpnp _; subst hxpa hxpnp
            obtain ⟨d, pa, us, hd_at, hfn, rpa, hmaj⟩ := rec_to_parent_addr_spec (by omega) htm evpar
            have hSpa : Held R (ixAddr pa) := by
              have hfnIn := addrIn_getAppFn (addrIn_binderDomAfter htyIn hd_at)
              rw [hfn] at hfnIn; exact hfnIn (ixAddr pa) rfl
            obtain ⟨hInd, -⟩ := indInfo_of_get_ci hS hH hbd hRagree hcl
              (sub fun c hc' => by rw [hc, hcs]; simp [hc']) hSpa rpa evci2 ldci2
            obtain ⟨info, iba, hinfo, -, hnp56, -, -, -, -, hnpEq, -, hiba, riba, -⟩ :=
              hInd _ _ _ _ _ _ _ _ rfl
            have ext23 := evpar.heap_extends.trans evci2.heap_extends
            obtain ⟨hveq, rfl⟩ := Lib.address_eq_spec evaeq riba
              (Bytes.repAddressRef_heapMono₂ addrTy (ext02.trans ext23) rpba)
            have hne_blk : info.blk ≠ ixAddr pba := fun h => by
              have : iba = pba := ixAddr_inj (hiba.trans h)
              rw [ite_eq_left this] at hveq; exact hne1 hveq
            exact ⟨d, pa, us, info, m_par, evpar.heap_extends, evci2.heap_extends,
              hd_at, hfn, Bytes.repAddressRef_heapMono₂ addrTy evci2.heap_extends rpa,
              hSpa, hinfo, hne_blk, hnp56, hnpEq, hmaj⟩
        obtain ⟨d, pa, us, info, h_par, ext2p, extp3, hd_at, hfn, rpa3, hSpa, hinfo, hne_blk,
          hnp56, rfl, hmaj⟩ := haux_arm
        subst hshape
        obtain ⟨d', hd_at', -, hrep_sp, hspIn⟩ := extract_aux_spec_params_from_rec_spec
          (by omega) hnp56 extp3 hmaj
          (RomBound.bounded_mono hbd (sub fun c hc' => by rw [hc]; simp [hc']))
          (htm.mono (ext2p.trans extp3)) htyIn evsp
        have hd_eq : d' = d := Option.some.inj (hd_at'.symm.trans hd_at)
        subst d'
        obtain ⟨d'', pa', us', hd_at'', hfn', hrep_us⟩ := extract_aux_occ_us_spec (by omega)
          (extp3.trans evsp.heap_extends) hmaj
          (htm.mono (ext2p.trans (extp3.trans evsp.heap_extends))) evus
        have hd_eq2 : d'' = d := Option.some.inj (hd_at''.symm.trans hd_at)
        subst d''
        have hfn_eq := hfn'.symm.trans hfn
        injection hfn_eq with _ hus_eq; subst us'
        have ext35 := evsp.heap_extends.trans evus.heap_extends
        have ext05 := ext02.trans (ext2p.trans (extp3.trans ext35))
        have hin := aux_already_in_spec hinj acc evin
          (RomBound.bounded_mono hbd (sub fun c hc' => by rw [hc]; simp [hc']))
          (flatList_mono ext05 hacc)
          (Bytes.repAddressRef_heapMono₂ addrTy ext35 rpa3)
          (tmOExactList_mono evus.heap_extends hrep_sp) hrep_us
        set sp := (d.getAppArgs.take info.np).map
          (Ix.Kernel.Expr.lowerBVars (rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) 0)
        have hcond : auxEntryIn acc (ixAddr pa) sp us = false := by
          cases hcnd : auxEntryIn acc (ixAddr pa) sp us
          · rfl
          · rw [hcnd] at hin; exact (hneIn hin).elim
        have ext06 := ext05.trans evin.heap_extends
        have hentry : FlatEntryRepExact (Core.keyOf t) m6 ⟨ixAddr pa, true, sp, us⟩
            (.tuple [xpa, .field 1, vsp, vus]) :=
          ⟨xpa, vsp, vus, pa, rfl,
            Bytes.repAddressRef_heapMono₂ addrTy (ext35.trans evin.heap_extends) rpa3, rfl,
            tmOExactList_mono (evus.heap_extends.trans evin.heap_extends) hrep_sp,
            hrep_us.mono evin.heap_extends⟩
        have hsn := flat_snoc_spec evsn (flatList_mono ext06 hacc) hentry
        have hacc'S : ∀ e ∈ acc ++ [⟨ixAddr pa, true, sp, us⟩],
            Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p := by
          intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with hm | rfl
          · exact haccS e hm
          · exact ⟨hSpa, hspIn⟩
        obtain rfl := binop_add_one_nat op1
        have ext07 := ext06.trans evsn.heap_extends
        obtain ⟨res, hres, hrep_res, hresS⟩ := ih (pos + 1) (acc ++ [⟨ixAddr pa, true, sp, us⟩])
          (sub fun c hc' => by rw [hc]; simp [hc']) (by simp at hlen; omega) hidx'
          (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext07 hall)
          (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext07 hrest)
          (Bytes.repAddressRef_heapMono₂ addrTy ext07 rrba)
          (Bytes.repAddressRef_heapMono₂ addrTy ext07 rpba) hsn hacc'S evrec
        have hka : keyAddr t (Core.keyOf t (ixAddr pa)) = some (ixAddr pa) :=
          addrOf_ofStore (E₀ := E₀) hwf (ixAddr pa)
        refine ⟨res, ?_, hrep_res, hresS⟩
        simp only [buildFlatAuxStep, hloaded, hd_at, hfn, hka, hinfo,
          beq_eq_false_iff_ne.mpr hne_blk, Bool.false_eq_true, ↓reduceIte]
        change buildFlatAuxStep t E₀ (ixAddr rba) crb rs (ixAddr pba) (pos + 1) rest
          (if auxEntryIn acc (ixAddr pa) sp us = true then acc
            else acc ++ [⟨ixAddr pa, true, sp, us⟩]) = some res
        simp only [hcond, Bool.false_eq_true, ↓reduceIte, hres]
    | .Cons_other (x_m := xm) (x_rest := xrest) (cs1029 := cs1) (v1038 := vpos1) (ld12 := ld)
        (hne1022 := hne) (op1094 := op1) (ev1031 := evrec) (hc1096 := hc) .. =>
      obtain ⟨m', rest', h1, hm', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      injection h1 with h1m h1r; subst h1m h1r
      cases m with
      | recr _ => obtain ⟨_, hshape⟩ := hm'; exact (hne _ rfl hshape).elim
      | defn _ | indc _ =>
        obtain rfl := binop_add_one_nat op1
        obtain ⟨res, hres, hrep_res, hresS⟩ := ih (pos + 1) acc
          (sub fun c hc' => by rw [hc]; simp [hc']) (by simp at hlen; omega) hidx'
          hall hrest rrba rpba hacc haccS evrec
        exact ⟨res, by simpa [buildFlatAuxStep] using hres, hrep_res, hresS⟩

/-- **`KernelCheck::detect_aux_from_recrs_ex`** on a `Muts` recursor block computes
`buildFlatAuxStep t E₀ rb crb rs prim 0 rs.toList originals`. -/
theorem detect_aux_from_recrs_ex_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c') (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {rba pba : Bytes.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {off : Nat} {orig : List FlatEntry}
    {xrba xpba xorig r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (hSrb : Held R (ixAddr rba)) (hcrbE : recordOf E₀ (ixAddr rba) = some crb)
    (hmuts : crb.info = .muts rs)
    (rrba : Bytes.RepAddressRef addrTy h rba xrba)
    (rpba : Bytes.RepAddressRef addrTy h pba xpba)
    (horig : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h orig xorig)
    (horigS : ∀ e ∈ orig, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p)
    (ev : ObsFn W "KernelCheck::detect_aux_from_recrs_ex"
      [xrba, xpba, .field (off : F), xorig] h r h' cs) :
    ∃ res : List FlatEntry,
      buildFlatAuxStep t E₀ (ixAddr rba) crb rs (ixAddr pba) 0 rs.toList orig = some res ∧
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h' res r ∧
      (∀ e ∈ res, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) := by
  match Obs.«KernelCheck::detect_aux_from_recrs_ex».obs ev with
  | .Muts (m2 := m2) (cs12 := cs1) (x_members := xmem) (cs92 := cs2)
      (ev14 := evld) (ev94 := evwalk) (hc150 := hc) .. =>
    obtain ⟨xm, _, _, _, _, hv, hms⟩ := load_verified_muts_of_record hS
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcrbE hmuts rrba evld
    injection hv with _ _ hl; injection hl with hm _; injection hm with _ _ hml
    injection hml with hx; subst hx
    have evwalk' : ObsFn W "KernelCheck::aux_from_recrs_walk_ex"
        [xmem, xmem, xrba, xpba, .field (off : F), xorig, .field ((0 : Nat) : F)] m2 r h' cs2 := by
      simpa using evwalk
    exact aux_from_recrs_walk_ex_spec ht hwf hS hH hbd hRagree hcl hlv hSrb hcrbE hmuts
      rs.toList 0 orig (fun c hc' => hsub c (by rw [hc]; simp [hc'])) (by simp)
      (fun i m hm => by simpa [← Array.getElem?_toList] using hm) hms hms
      (Bytes.repAddressRef_heapMono₂ addrTy evld.heap_extends rrba)
      (Bytes.repAddressRef_heapMono₂ addrTy evld.heap_extends rpba)
      (flatList_mono evld.heap_extends horig) horigS evwalk'
  | .other (cs12 := cs1) (ev14 := evld) (hne151 := hne) (hc158 := hc) .. =>
    obtain ⟨xm, _, _, _, _, hv, -⟩ := load_verified_muts_of_record hS
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcrbE hmuts rrba evld
    injection hv with _ _ hl; injection hl with hm _
    exact (hne [xm] rfl hm).elim

/-- **`KernelCheck::build_flat_block`** on a `Muts` recursor block `rb` and `Muts` parent/fallback
block `fb` computes the primary parent block `prim`, its `originals`, and `buildFlatAuxStep`
producing `flat` on `FlatEntryRepExact` with `Held R` and `AddrIn (Held R)` on all entries. -/
theorem build_flat_block_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c') (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {rba fba : Bytes.Address} {crb cbF : Ixon.Constant} {rs msF : Array Ixon.MutConst}
    {off : Nat} {xrba xfba r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hoff : off ≤ 1) (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (hSrb : Held R (ixAddr rba)) (hcrbE : recordOf E₀ (ixAddr rba) = some crb)
    (hmuts : crb.info = .muts rs)
    (hSfb : Held R (ixAddr fba)) (hfbE : recordOf E₀ (ixAddr fba) = some cbF)
    (hfbMuts : cbF.info = .muts msF)
    (rrba : Bytes.RepAddressRef addrTy h rba xrba)
    (rfba : Bytes.RepAddressRef addrTy h fba xfba)
    (ev : ObsFn W "KernelCheck::build_flat_block" [xrba, xfba, .field (off : F)] h r h' cs) :
    ∃ (prim : _root_.Address) (cprim : Ixon.Constant) (msp : Array Ixon.MutConst)
      (os flat : List FlatEntry),
      firstRecrParentBlock t E₀ (ixAddr rba) crb rs (ixAddr fba) 0 rs.toList = some prim ∧
      Held R prim ∧ recordOf E₀ prim = some cprim ∧ cprim.info = .muts msp ∧
      originals (FlatView.ofStore t E₀) off (indcAddrs prim 0 msp.toList) = some os ∧
      buildFlatAuxStep t E₀ (ixAddr rba) crb rs prim 0 rs.toList os = some flat ∧
      flat.filter (fun e => !e.aux) = os ∧
      (∀ e ∈ os, e.aux = false ∧ e.params = [] ∧ Held R e.addr ∧
        ∃ idx ind, msp[idx]? = some (.indc ind) ∧ e.addr = memberAddr prim idx (.indc ind)) ∧
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h' flat r ∧
      (∀ e ∈ flat, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → ∀ c ∈ cs', c ∈ rootCalls :=
    fun hs c hc => hsub c (hs c hc)
  match Obs.«KernelCheck::build_flat_block».obs ev with
  | .n0 (cs12 := cs1) (cs42 := cs2) (cs73 := cs3)
      (ev14 := evprim) (ev44 := evorig) (ev75 := evmut) (hc91 := hc) .. =>
    have ext02 := evprim.heap_extends.trans evorig.heap_extends
    have hm := is_muts_block_spec hS (sub fun c hc' => by rw [hc]; simp [hc']) hcrbE
      (Bytes.repAddressRef_heapMono₂ addrTy ext02 rrba) evmut
    rw [hmuts] at hm; simp only at hm
    exact absurd (Value.field.inj hm) (by decide)
  | .other (v1 := xprim) (m2 := m1) (cs12 := cs1) (v31 := xorig) (m32 := m2) (cs42 := cs2)
      (m62 := m3) (cs73 := cs3) (cs99 := cs4)
      (ev14 := evprim) (ev44 := evorig) (ev75 := evmut) (ev101 := evdet) (hc134 := hc) .. =>
    obtain ⟨pba, cprim, msp, hfrp, rpba, hSp, hcprim, hmsp⟩ :=
      primary_parent_block_of_spec ht hwf hS hH hbd hRagree hcl hlv
        (sub fun c hc' => by rw [hc]; simp [hc']) hSrb hcrbE hmuts hSfb hfbE hfbMuts
        rrba rfba evprim
    obtain ⟨os, hos, hrep_os, -, hos_props⟩ := build_flat_originals_muts_spec hS hH hbd hRagree hcl
      hoff (sub fun c hc' => by rw [hc]; simp [hc']) hSp hcprim hmsp rpba evorig
    have hosS : ∀ e ∈ os, Held R e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p := by
      intro e he
      obtain ⟨-, hparams, hheld, -⟩ := hos_props e he
      exact ⟨hheld, fun p hp => by rw [hparams] at hp; cases hp⟩
    have ext03 := evprim.heap_extends.trans (evorig.heap_extends.trans evmut.heap_extends)
    obtain ⟨flat, hflat, hrep_flat, hflatS⟩ := detect_aux_from_recrs_ex_spec ht hwf hS hH hbd
      hRagree hcl hlv (sub fun c hc' => by rw [hc]; simp [hc']) hSrb hcrbE hmuts
      (Bytes.repAddressRef_heapMono₂ addrTy ext03 rrba)
      (Bytes.repAddressRef_heapMono₂ addrTy (evorig.heap_extends.trans evmut.heap_extends) rpba)
      (flatList_mono evmut.heap_extends hrep_os) hosS evdet
    have hfilt : flat.filter (fun e => !e.aux) = os := by
      rw [buildFlatAuxStep_filter_nonAux hflat]
      exact List.filter_eq_self.mpr (fun e he => by simp [(hos_props e he).1])
    exact ⟨ixAddr pba, cprim, msp, os, flat, hfrp, hSp, hcprim, hmsp, hos, hflat, hfilt,
      hos_props, hrep_flat, hflatS⟩

end IxVM.Refinement.Binding.FamilyRecon

