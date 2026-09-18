/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Model/Context.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.WellDenoted

namespace Ix.Kernel.Model

open SetTheory

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

/-- All entries are expressed in the full current context. Pushing a binder
lifts both its type and every existing entry. -/
abbrev Context (β : Type u) := List (AExpr β)

def Context.push (A : AExpr β) (Γ : Context β) : Context β :=
  A.liftN 1 :: Γ.map (AExpr.liftN 1 ·)

def Context.Valid (constants : Assignment β V) (levels : List Nat)
    (Γ : Context β) (env : Nat → V) : Prop :=
  ∀ i A, Γ[i]? = some A →
    WellDenoted constants levels env A ∧ env i ∈ˢ interp constants levels env A

theorem Context.valid_nil (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) : Context.Valid constants levels [] env := by
  intro i A h
  simp at h

omit [SetTheory V] in
@[simp] theorem Valuation.skip_one_cons (x : V) (env : Nat → V) :
    Valuation.skip 1 0 (Valuation.cons x env) = env := by
  funext i
  simp [Valuation.skip, Nat.add_comm 1 i]

theorem Context.Valid.push {constants : Assignment β V} {levels : List Nat}
    {Γ : Context β} {env : Nat → V} {A : AExpr β} {x : V}
    (hΓ : Γ.Valid constants levels env) (hA : WellDenoted constants levels env A)
    (hx : x ∈ˢ interp constants levels env A) :
    (Γ.push A).Valid constants levels (Valuation.cons x env) := by
  intro i B hi
  cases i with
  | zero =>
    simp only [Context.push, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst B
    simpa only [wellDenoted_liftN, interp_liftN, Valuation.skip_one_cons,
      Valuation.cons_zero] using And.intro hA hx
  | succ i =>
    simp only [Context.push, List.getElem?_cons_succ, List.getElem?_map] at hi
    obtain ⟨C, hC, rfl⟩ := Option.map_eq_some_iff.mp hi
    simpa only [wellDenoted_liftN, interp_liftN, Valuation.skip_one_cons,
      Valuation.cons_succ] using hΓ i C hC

end Ix.Kernel.Model
