/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Support

/-! Whole-reference substitution for independently checked model companions.
A constructor may map to a definition, so this operation is more general
than renaming a block address while retaining its member/constructor tag. -/

namespace Ix.Theory

universe u v w x
variable {β : Type u} {γ : Type v} {δ : Type w}

def VExpr.mapRefs (mapping : ConstRef β → ConstRef γ) : VExpr β → VExpr γ
  | .bvar i => .bvar i
  | .sort level => .sort level
  | .const ref levels => .const (mapping ref) levels
  | .app f a => .app (f.mapRefs mapping) (a.mapRefs mapping)
  | .lam type body => .lam (type.mapRefs mapping) (body.mapRefs mapping)
  | .forallE type body => .forallE (type.mapRefs mapping) (body.mapRefs mapping)
  | .proj ref index major => .proj (mapping ref) index (major.mapRefs mapping)
  | .natLit n => .natLit n

namespace Model

def AExpr.mapRefs (mapping : ConstRef β → ConstRef γ) : AExpr β → AExpr γ
  | .bvar i => .bvar i
  | .sort level => .sort level
  | .const ref levels => .const (mapping ref) levels
  | .app f a => .app (f.mapRefs mapping) (a.mapRefs mapping)
  | .lam condition type body => .lam condition (type.mapRefs mapping) (body.mapRefs mapping)
  | .forallE condition type body => .forallE condition (type.mapRefs mapping) (body.mapRefs mapping)
  | .proj ref index major => .proj (mapping ref) index (major.mapRefs mapping)
  | .natLit n => .natLit n

@[simp] theorem AExpr.erase_mapRefs (e : AExpr β) (mapping : ConstRef β → ConstRef γ) :
    (e.mapRefs mapping).erase = e.erase.mapRefs mapping := by
  induction e <;> simp_all [AExpr.mapRefs, AExpr.erase, VExpr.mapRefs]

@[simp] theorem AExpr.scope_mapRefs (e : AExpr β) (mapping : ConstRef β → ConstRef γ) (n k : Nat) :
    (e.mapRefs mapping).Scope n k ↔ e.Scope n k := by
  induction e generalizing k <;> simp_all [AExpr.mapRefs, AExpr.Scope]

@[simp] theorem AExpr.references_mapRefs (e : AExpr β) (mapping : ConstRef β → ConstRef γ) :
    (e.mapRefs mapping).references = e.references.map mapping := by
  induction e <;> simp_all [AExpr.mapRefs, AExpr.references]

@[simp] theorem AExpr.mapRefs_liftN (e : AExpr β) (mapping : ConstRef β → ConstRef γ) (n k : Nat) :
    (e.liftN n k).mapRefs mapping = (e.mapRefs mapping).liftN n k := by
  induction e generalizing k <;> simp_all [AExpr.mapRefs, AExpr.liftN]

@[simp] theorem AExpr.mapRefs_inst (e a : AExpr β) (mapping : ConstRef β → ConstRef γ) (k : Nat) :
    (e.inst a k).mapRefs mapping = (e.mapRefs mapping).inst (a.mapRefs mapping) k := by
  induction e generalizing k with
  | bvar i =>
    by_cases hi : i < k
    · simp [AExpr.inst, AExpr.instVar, AExpr.mapRefs, hi]
    · by_cases he : i = k <;> simp [AExpr.inst, AExpr.instVar, AExpr.mapRefs, hi, he]
  | _ => simp_all [AExpr.inst, AExpr.mapRefs]

@[simp] theorem AExpr.mapRefs_instL (e : AExpr β) (mapping : ConstRef β → ConstRef γ) (levels : List VLevel) :
    (e.instL levels).mapRefs mapping = (e.mapRefs mapping).instL levels := by
  induction e <;> simp_all [AExpr.instL, AExpr.mapRefs]

@[simp] theorem AExpr.mapRefs_id (e : AExpr β) : e.mapRefs id = e := by
  induction e <;> simp_all [AExpr.mapRefs]

theorem AExpr.mapRefs_comp (e : AExpr β) (first : ConstRef β → ConstRef γ) (second : ConstRef γ → ConstRef δ) :
    (e.mapRefs first).mapRefs second = e.mapRefs (second ∘ first) := by
  induction e <;> simp_all [AExpr.mapRefs, Function.comp_def]

theorem AExpr.mapRefs_congr (e : AExpr β) (first second : ConstRef β → ConstRef γ)
    (h : ∀ ref ∈ e.references, first ref = second ref) : e.mapRefs first = e.mapRefs second := by
  induction e with
  | const ref levels => simp [AExpr.mapRefs, h ref (by simp [AExpr.references])]
  | app f a hf ha | lam condition f a hf ha | forallE condition f a hf ha =>
    simp only [AExpr.mapRefs,
      hf (fun ref hr => h ref (List.mem_append_left _ hr)),
      ha (fun ref hr => h ref (List.mem_append_right _ hr))]
  | proj ref index major ih =>
    simp only [AExpr.mapRefs, h ref (List.mem_cons_self), ih (fun ref hr => h ref (List.mem_cons_of_mem _ hr))]
  | _ => rfl

/-- Restoration needs an inverse only on the references actually used by
the restored expression. Unrelated auxiliaries are outside the premise. -/
theorem AExpr.mapRefs_restore (e : AExpr β) (forward : ConstRef β → ConstRef γ)
    (backward : ConstRef γ → ConstRef β)
    (h : ∀ ref ∈ e.references, backward (forward ref) = ref) :
    (e.mapRefs forward).mapRefs backward = e := by
  rw [AExpr.mapRefs_comp, e.mapRefs_congr (backward ∘ forward) id h, AExpr.mapRefs_id]

variable {V : Type x} [SetTheory V]

theorem interp_mapRefs (e : AExpr β) (mapping : ConstRef β → ConstRef γ)
    (constants : Assignment γ V) (levels : List Nat) (env : Nat → V) :
    interp constants levels env (e.mapRefs mapping) =
      interp (fun ref values => constants (mapping ref) values) levels env e := by
  induction e generalizing env with
  | lam condition type body ht hb | forallE condition type body ht hb =>
    simp only [AExpr.mapRefs, interp, ht]
    congr 1
    funext value
    exact hb _
  | _ => simp_all [AExpr.mapRefs, interp]

theorem wellDenoted_mapRefs (e : AExpr β) (mapping : ConstRef β → ConstRef γ)
    (constants : Assignment γ V) (levels : List Nat) (env : Nat → V) :
    WellDenoted constants levels env (e.mapRefs mapping) ↔
      WellDenoted (fun ref values => constants (mapping ref) values) levels env e := by
  induction e generalizing env with
  | lam condition type body ht hb | forallE condition type body ht hb =>
    simp only [AExpr.mapRefs, WellDenoted, ht, hb, interp_mapRefs]
  | _ => simp_all [AExpr.mapRefs, WellDenoted, interp_mapRefs]

/-- A permutation changes addresses and pulls the assignment back through its
inverse. Only references actually used by the expression need an inverse. -/
theorem interp_mapRefs_permutation (e : AExpr β) (forward : ConstRef β → ConstRef γ)
    (backward : ConstRef γ → ConstRef β) (constants : Assignment β V)
    (inverse : ∀ ref ∈ e.references, backward (forward ref) = ref)
    (levels : List Nat) (env : Nat → V) :
    interp (fun ref values => constants (backward ref) values) levels env (e.mapRefs forward) =
      interp constants levels env e := by
  rw [interp_mapRefs]
  exact interp_congr_constants e _ constants
    (fun ref hr values => congrArg (fun r => constants r values) (inverse ref hr)) levels env

theorem wellDenoted_mapRefs_permutation (e : AExpr β) (forward : ConstRef β → ConstRef γ)
    (backward : ConstRef γ → ConstRef β) (constants : Assignment β V)
    (inverse : ∀ ref ∈ e.references, backward (forward ref) = ref)
    (levels : List Nat) (env : Nat → V) :
    WellDenoted (fun ref values => constants (backward ref) values) levels env (e.mapRefs forward) ↔
      WellDenoted constants levels env e := by
  rw [wellDenoted_mapRefs]
  exact wellDenoted_congr_constants e _ constants
    (fun ref hr values => congrArg (fun r => constants r values) (inverse ref hr)) levels env

/-- Restoring the retained reference support preserves the entire interpreted
expression, including binder annotations and both sides of a rule. -/
theorem interp_mapRefs_restore (e : AExpr β) (forward : ConstRef β → ConstRef γ)
    (backward : ConstRef γ → ConstRef β) (constants : Assignment β V)
    (inverse : ∀ ref ∈ e.references, backward (forward ref) = ref)
    (levels : List Nat) (env : Nat → V) :
    interp constants levels env ((e.mapRefs forward).mapRefs backward) = interp constants levels env e := by
  rw [e.mapRefs_restore forward backward inverse]

/-- Equivalent model auxiliaries may share a representative. No injectivity
is needed: the checked consumer must establish agreement of their values. -/
theorem interp_mapRefs_merge (e : AExpr β) (before : Assignment β V) (after : Assignment γ V)
    (mapping : ConstRef β → ConstRef γ)
    (agree : ∀ ref ∈ e.references, ∀ levels, before ref levels = after (mapping ref) levels)
    (levels : List Nat) (env : Nat → V) :
    interp before levels env e = interp after levels env (e.mapRefs mapping) := by
  rw [interp_mapRefs]
  exact interp_congr_constants e before _ agree levels env

theorem wellDenoted_mapRefs_merge (e : AExpr β) (before : Assignment β V) (after : Assignment γ V)
    (mapping : ConstRef β → ConstRef γ)
    (agree : ∀ ref ∈ e.references, ∀ levels, before ref levels = after (mapping ref) levels)
    (levels : List Nat) (env : Nat → V) :
    WellDenoted before levels env e ↔ WellDenoted after levels env (e.mapRefs mapping) := by
  rw [wellDenoted_mapRefs]
  exact wellDenoted_congr_constants e before _ agree levels env

end Model
end Ix.Theory
