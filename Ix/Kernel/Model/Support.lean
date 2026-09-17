/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Model/Support.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Environment

namespace Ix.Kernel.Model

open SetTheory

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

namespace AExpr

def references : AExpr β → List (ConstRef β)
  | .bvar _ | .sort _ | .natLit _ => []
  | .const r _ => [r]
  | .app f a | .lam _ f a | .forallE _ f a => f.references ++ a.references
  | .proj r _ e => r :: e.references

def ReferencesIn (entries : Environment β) (e : AExpr β) : Prop :=
  ∀ r ∈ e.references, (entries r).isSome = true

instance {entries : Environment β} {e : AExpr β} : Decidable (e.ReferencesIn entries) :=
  inferInstanceAs (Decidable (∀ r ∈ e.references, (entries r).isSome = true))

end AExpr

def ConstantFact.Scope (n : Nat) : ConstantFact β → Prop
  | .typed e type => e.Scope n 0 ∧ type.Scope n 0
  | .natural .. => n = 0

def ConstantFact.references : ConstantFact β → List (ConstRef β)
  | .typed e type => e.references ++ type.references
  | .natural zero succ => [zero, succ]

def ConstantFact.ReferencesIn (entries : Environment β) (fact : ConstantFact β) : Prop :=
  ∀ r ∈ fact.references, (entries r).isSome = true

instance {n : Nat} {fact : ConstantFact β} : Decidable (fact.Scope n) := by
  cases fact <;> unfold ConstantFact.Scope <;> infer_instance

instance {entries : Environment β} {fact : ConstantFact β} : Decidable (fact.ReferencesIn entries) :=
  inferInstanceAs (Decidable (∀ r ∈ fact.references, (entries r).isSome = true))

theorem interp_congr_constants (e : AExpr β) (constants constants' : Assignment β V)
    (h : ∀ r ∈ e.references, ∀ ls, constants r ls = constants' r ls)
    (levels : List Nat) (env : Nat → V) :
    interp constants levels env e = interp constants' levels env e := by
  induction e generalizing env with
  | const r ls => exact h r (by simp [AExpr.references]) _
  | app f a hf ha =>
    have hf' := hf (fun r hr => h r (List.mem_append_left _ hr)) env
    have ha' := ha (fun r hr => h r (List.mem_append_right _ hr)) env
    simp only [interp, hf', ha']
  | lam p A b hA hb | forallE p A b hA hb =>
    have hA' := hA (fun r hr => h r (List.mem_append_left _ hr)) env
    simp only [interp, hA']
    congr 1
    funext x
    exact hb (fun r hr => h r (List.mem_append_right _ hr)) _
  | proj r i e ih =>
    simp only [interp, ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) env]
  | _ => rfl

theorem wellDenoted_congr_constants (e : AExpr β) (constants constants' : Assignment β V)
    (h : ∀ r ∈ e.references, ∀ ls, constants r ls = constants' r ls)
    (levels : List Nat) (env : Nat → V) :
    WellDenoted constants levels env e ↔ WellDenoted constants' levels env e := by
  induction e generalizing env with
  | app f a hf ha =>
    have hfr := fun r hr => h r (List.mem_append_left _ hr)
    have har := fun r hr => h r (List.mem_append_right _ hr)
    simp only [WellDenoted, hf hfr, ha har, interp_congr_constants _ _ _ hfr,
      interp_congr_constants _ _ _ har]
  | lam p A b hA hb | forallE p A b hA hb =>
    have hAr := fun r hr => h r (List.mem_append_left _ hr)
    have hbr := fun r hr => h r (List.mem_append_right _ hr)
    simp only [WellDenoted, hA hAr, hb hbr, interp_congr_constants _ _ _ hAr,
      interp_congr_constants _ _ _ hbr]
  | proj r i e ih => exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) env
  | _ => rfl

theorem interp_congr_env (e : AExpr β) (constants : Assignment β V)
    (levels : List Nat) {n k : Nat} (hs : e.Scope n k) (env env' : Nat → V)
    (h : ∀ i, i < k → env i = env' i) :
    interp constants levels env e = interp constants levels env' e := by
  induction e generalizing k env env' with
  | bvar i => exact h i hs
  | app f a hf ha => simp only [interp, hf hs.1 env env' h, ha hs.2 env env' h]
  | lam p A b hA hb | forallE p A b hA hb =>
    simp only [interp, hA hs.2.1 env env' h]
    congr 1
    funext x
    apply hb hs.2.2
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (by omega)
  | proj r i e ih => simp only [interp, ih hs env env' h]
  | _ => rfl

theorem interp_closed (e : AExpr β) (constants : Assignment β V)
    (levels : List Nat) {n : Nat} (hs : e.Scope n 0) (env env' : Nat → V) :
    interp constants levels env e = interp constants levels env' e :=
  interp_congr_env e constants levels hs env env' (fun _ h => (Nat.not_lt_zero _ h).elim)

/-- Syntactic closure of an admitted interface. Semantic realizability remains
a separate, produced fact. -/
structure Environment.WF (entries : Environment β) : Prop where
  typeScope : ∀ r entry, entries r = some entry → entry.type.Scope entry.universes 0
  bodyScope : ∀ r entry, entries r = some entry → ∀ body, entry.body = some body →
    body.Scope entry.universes 0
  typeReferences : ∀ r entry, entries r = some entry → entry.type.ReferencesIn entries
  bodyReferences : ∀ r entry, entries r = some entry → ∀ body, entry.body = some body →
    body.ReferencesIn entries
  equationScope : ∀ r entry, entries r = some entry → ∀ equation ∈ entry.equations,
    equation.lhs.Scope entry.universes 0 ∧ equation.rhs.Scope entry.universes 0
  equationReferences : ∀ r entry, entries r = some entry → ∀ equation ∈ entry.equations,
    equation.lhs.ReferencesIn entries ∧ equation.rhs.ReferencesIn entries
  factScope : ∀ r entry, entries r = some entry → ∀ fact ∈ entry.facts, fact.Scope entry.universes
  factReferences : ∀ r entry, entries r = some entry → ∀ fact ∈ entry.facts, fact.ReferencesIn entries

end Ix.Kernel.Model
