/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Rename.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Expr

/-! # Address renaming for anonymous expressions

The shared syntax operation is independent of inductive generation.
-/

namespace Ix.Kernel

/-- A dependency-free bijection used to transport abstract block addresses.
The Theory intentionally does not import Lean's metadata equivalence API. -/
structure AddressEquiv (β : Type u) (γ : Type v) where
  toFun : β → γ
  invFun : γ → β
  left_inv : ∀ block, invFun (toFun block) = block
  right_inv : ∀ block, toFun (invFun block) = block

namespace AddressEquiv

instance : CoeFun (AddressEquiv β γ) fun _ => β → γ :=
  ⟨AddressEquiv.toFun⟩

@[simp] theorem inv_apply_apply (mapping : AddressEquiv β γ) (block : β) :
    mapping.invFun (mapping block) = block :=
  mapping.left_inv block

@[simp] theorem apply_inv_apply (mapping : AddressEquiv β γ) (block : γ) :
    mapping (mapping.invFun block) = block :=
  mapping.right_inv block

theorem injective (mapping : AddressEquiv β γ) : Function.Injective mapping := by
  intro left right equality
  simpa using congrArg mapping.invFun equality

/-- Identity address bijection. -/
def refl (β : Type u) : AddressEquiv β β where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Reverse an address bijection. -/
def symm (mapping : AddressEquiv β γ) : AddressEquiv γ β where
  toFun := mapping.invFun
  invFun := mapping
  left_inv := mapping.right_inv
  right_inv := mapping.left_inv

/-- Compose address bijections. -/
def trans (first : AddressEquiv β γ)
    (second : AddressEquiv γ δ) : AddressEquiv β δ where
  toFun := second ∘ first
  invFun := first.invFun ∘ second.invFun
  left_inv := by
    intro block
    simp
  right_inv := by
    intro block
    simp

@[simp] theorem symm_apply (mapping : AddressEquiv β γ) (block : γ) :
    mapping.symm block = mapping.invFun block := rfl

@[simp] theorem trans_apply (first : AddressEquiv β γ)
    (second : AddressEquiv γ δ) (block : β) :
    (first.trans second) block = second (first block) := rfl

@[simp] theorem beq_apply (mapping : AddressEquiv β γ)
    [DecidableEq β] [DecidableEq γ] (left right : β) :
    (mapping left == mapping right) = (left == right) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, mapping.injective.eq_iff]

@[simp] theorem bne_apply (mapping : AddressEquiv β γ)
    [DecidableEq β] [DecidableEq γ] (left right : β) :
    (mapping left != mapping right) = (left != right) := by
  simp only [bne, beq_apply]

end AddressEquiv

namespace ConstRef

/-- Rename the block address carried by a constant reference. -/
def rename (mapping : β → γ) : ConstRef β → ConstRef γ
  | .member block index => .member (mapping block) index
  | .ctor block index ctorIndex => .ctor (mapping block) index ctorIndex

@[simp] theorem rename_id (ref : ConstRef β) :
    ref.rename id = ref := by
  cases ref <;> rfl

@[simp] theorem rename_comp (second : γ → δ) (first : β → γ)
    (ref : ConstRef β) :
    (ref.rename first).rename second = ref.rename (second ∘ first) := by
  cases ref <;> rfl

@[simp] theorem rename_block (mapping : β → γ) (ref : ConstRef β) :
    (ref.rename mapping).block = mapping ref.block := by
  cases ref <;> rfl

/-- Renaming references along an address bijection is injective. -/
theorem rename_injective (mapping : AddressEquiv β γ) :
    Function.Injective (ConstRef.rename mapping) := by
  have inverse : Function.LeftInverse
      (ConstRef.rename mapping.invFun) (ConstRef.rename mapping) := by
    intro ref
    cases ref <;> simp [ConstRef.rename]
  exact inverse.injective

@[simp] theorem rename_eq_rename_iff (mapping : AddressEquiv β γ)
    (left right : ConstRef β) :
    left.rename mapping = right.rename mapping ↔ left = right :=
  (rename_injective mapping).eq_iff

@[simp] theorem rename_inverse (mapping : AddressEquiv β γ)
    (ref : ConstRef β) :
    (ref.rename mapping).rename mapping.invFun = ref := by
  cases ref <;> simp [ConstRef.rename]

end ConstRef

namespace VExpr

/-- Rename every block address in an expression.  Binder indices and universe
levels are unchanged. -/
def rename (mapping : β → γ) : VExpr β → VExpr γ
  | .bvar index => .bvar index
  | .sort level => .sort level
  | .const ref levels => .const (ref.rename mapping) levels
  | .app function argument =>
      .app (function.rename mapping) (argument.rename mapping)
  | .lam domain body => .lam (domain.rename mapping) (body.rename mapping)
  | .forallE domain body =>
      .forallE (domain.rename mapping) (body.rename mapping)
  | .proj ref field major =>
      .proj (ref.rename mapping) field (major.rename mapping)
  | .natLit value => .natLit value

@[simp] theorem rename_id (expression : VExpr β) :
    expression.rename id = expression := by
  induction expression with
  | const ref levels => cases ref <;> rfl
  | proj ref field major ih => cases ref <;> simp [rename, ih]
  | _ => simp_all [rename]

@[simp] theorem rename_comp (second : γ → δ) (first : β → γ)
    (expression : VExpr β) :
    (expression.rename first).rename second =
      expression.rename (second ∘ first) := by
  induction expression with
  | const ref levels => cases ref <;> rfl
  | proj ref field major ih => cases ref <;> simp [rename, ih]
  | _ => simp_all [rename]

@[simp] theorem rename_inverse (mapping : AddressEquiv β γ)
    (expression : VExpr β) :
    (expression.rename mapping).rename mapping.invFun = expression := by
  induction expression <;>
    simp_all only [rename, ConstRef.rename_inverse]

/-- Expression renaming along an address bijection is injective. -/
theorem rename_injective (mapping : AddressEquiv β γ) :
    Function.Injective (VExpr.rename mapping) := by
  have inverse : Function.LeftInverse
      (VExpr.rename mapping.invFun) (VExpr.rename mapping) :=
    VExpr.rename_inverse mapping
  exact inverse.injective

@[simp] theorem rename_appN (mapping : β → γ) (function : VExpr β)
    (arguments : List (VExpr β)) :
    (function.appN arguments).rename mapping =
      (function.rename mapping).appN (arguments.map (VExpr.rename mapping)) := by
  induction arguments generalizing function with
  | nil => rfl
  | cons argument arguments ih =>
      simp [VExpr.appN, VExpr.rename, ih]

@[simp] theorem rename_liftN (mapping : β → γ) (expression : VExpr β)
    (count cutoff : Nat) :
    (expression.liftN count cutoff).rename mapping =
      (expression.rename mapping).liftN count cutoff := by
  induction expression generalizing cutoff <;> simp_all [VExpr.liftN, rename]

@[simp] theorem rename_instL (mapping : β → γ) (expression : VExpr β)
    (levels : List VLevel) :
    (expression.instL levels).rename mapping =
      (expression.rename mapping).instL levels := by
  induction expression <;> simp_all [VExpr.instL, rename]

@[simp] theorem rename_inst (mapping : β → γ) (expression argument : VExpr β)
    (cutoff : Nat) :
    (expression.inst argument cutoff).rename mapping =
      (expression.rename mapping).inst (argument.rename mapping) cutoff := by
  induction expression generalizing cutoff with
  | bvar index =>
      by_cases below : index < cutoff
      · simp [VExpr.inst, VExpr.instVar, below, rename]
      · by_cases equal : index = cutoff
        · simp [VExpr.inst, VExpr.instVar, equal, rename]
        · simp [VExpr.inst, VExpr.instVar, below, equal, rename]
  | _ => simp_all [VExpr.inst, rename]

@[simp] theorem rename_lamN (mapping : β → γ)
    (binders : List (VExpr β)) (body : VExpr β) :
    (VExpr.lamN binders body).rename mapping =
      VExpr.lamN (binders.map (VExpr.rename mapping)) (body.rename mapping) := by
  induction binders with
  | nil => rfl
  | cons binder binders ih => simp [VExpr.lamN, rename, ih]

@[simp] theorem rename_forallN (mapping : β → γ)
    (binders : List (VExpr β)) (body : VExpr β) :
    (VExpr.forallN binders body).rename mapping =
      VExpr.forallN (binders.map (VExpr.rename mapping))
        (body.rename mapping) := by
  induction binders with
  | nil => rfl
  | cons binder binders ih => simp [VExpr.forallN, rename, ih]

@[simp] theorem rename_liftTelN (mapping : β → γ) (count : Nat) :
    ∀ (binders : List (VExpr β)) (cutoff : Nat),
      (VExpr.liftTelN count binders cutoff).map (VExpr.rename mapping) =
        VExpr.liftTelN count
          (binders.map (VExpr.rename mapping)) cutoff
  | [], _ => rfl
  | binder :: binders, cutoff => by
      simp [VExpr.liftTelN, rename_liftTelN mapping count binders]

@[simp] theorem rename_telN (mapping : β → γ) (count : Nat)
    (expression : VExpr β) :
    (expression.rename mapping).telN count =
      (expression.telN count).map (VExpr.rename mapping) := by
  induction count generalizing expression with
  | zero => rfl
  | succ count ih =>
      cases expression with
      | forallE domain body =>
          simp only [rename, VExpr.telN, List.map_cons]
          rw [ih]
      | _ => rfl

@[simp] theorem rename_dropN (mapping : β → γ) (count : Nat)
    (expression : VExpr β) :
    (expression.rename mapping).dropN count =
      (expression.dropN count).rename mapping := by
  induction count generalizing expression with
  | zero => rfl
  | succ count ih =>
      cases expression <;> simp [rename, VExpr.dropN, ih]

@[simp] theorem rename_resultOf (mapping : β → γ) (expression : VExpr β) :
    (expression.rename mapping).resultOf =
      expression.resultOf.rename mapping := by
  induction expression <;> simp_all [rename, VExpr.resultOf]

@[simp] theorem rename_appArgs (mapping : β → γ) (expression : VExpr β)
    (accumulator : List (VExpr β)) :
    (expression.rename mapping).appArgs
        (accumulator.map (VExpr.rename mapping)) =
      (expression.appArgs accumulator).map (VExpr.rename mapping) := by
  induction expression generalizing accumulator with
  | app function argument functionIH argumentIH =>
      simp only [rename, VExpr.appArgs]
      simpa only [List.map_cons] using functionIH (argument :: accumulator)
  | _ => rfl

@[simp] theorem rename_appHead (mapping : β → γ) (expression : VExpr β) :
    (expression.rename mapping).appHead =
      expression.appHead.rename mapping := by
  induction expression <;> simp_all [rename, VExpr.appHead]

@[simp] theorem rename_instTelN (mapping : β → γ) (argument : VExpr β) :
    ∀ (binders : List (VExpr β)) (cutoff : Nat),
      (VExpr.instTelN argument binders cutoff).map (VExpr.rename mapping) =
        VExpr.instTelN (argument.rename mapping)
          (binders.map (VExpr.rename mapping)) cutoff
  | [], _ => rfl
  | binder :: binders, cutoff => by
      simp [VExpr.instTelN, rename_instTelN mapping argument binders]

@[simp] theorem rename_instRev (mapping : β → γ) (expression : VExpr β)
    (arguments : List (VExpr β)) :
    (VExpr.instRev expression arguments).rename mapping =
      VExpr.instRev (expression.rename mapping)
        (arguments.map (VExpr.rename mapping)) := by
  induction arguments generalizing expression with
  | nil => rfl
  | cons argument arguments ih =>
      simp [VExpr.instRev, ih]

@[simp] theorem rename_instRevAt (mapping : β → γ) (expression : VExpr β)
    (arguments : List (VExpr β)) (cutoff : Nat) :
    (VExpr.instRevAt expression arguments cutoff).rename mapping =
      VExpr.instRevAt (expression.rename mapping)
        (arguments.map (VExpr.rename mapping)) cutoff := by
  induction arguments generalizing expression with
  | nil => rfl
  | cons argument arguments ih =>
      simp [VExpr.instRevAt, ih]

end VExpr

end Ix.Kernel
