/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Model/WellDenoted.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Interpret

/-!
# Hereditary validity of annotated expressions

Application carries domain membership, and both binder forms carry a
codomain universe whose zero test agrees with the annotation. The invariant
is a semantic specification, not input accepted on trust: checker rules must
construct it. Projection validity follows its major premise; literal validity
is structural. Their membership still requires admitted primitive facts.
-/

namespace Ix.Kernel.Model

open SetTheory SetModel

universe u v w
variable {β : Type u} {V : Type v} [SetTheory V]

def WellDenoted (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) : AExpr β → Prop
  | .bvar _ | .sort _ | .const .. => True
  | .app f a =>
    WellDenoted constants levels env f ∧ WellDenoted constants levels env a ∧
      ∃ (v : Nat) (A : V) (B : V → V),
        interp constants levels env f ∈ˢ piR v A B ∧
        interp constants levels env a ∈ˢ A ∧
        ∀ x, x ∈ˢ A → B x ∈ˢ univ v
  | .lam p A b =>
    WellDenoted constants levels env A ∧
      (∀ x, x ∈ˢ interp constants levels env A →
        WellDenoted constants levels (Valuation.cons x env) b) ∧
      ∃ (v : Nat) (B : V → V), (regime p levels = 0 ↔ v = 0) ∧
        ∀ x, x ∈ˢ interp constants levels env A →
          interp constants levels (Valuation.cons x env) b ∈ˢ B x ∧
          B x ∈ˢ univ v
  | .forallE p A B =>
    WellDenoted constants levels env A ∧
      (∀ x, x ∈ˢ interp constants levels env A →
        WellDenoted constants levels (Valuation.cons x env) B) ∧
      ∃ v : Nat, (regime p levels = 0 ↔ v = 0) ∧
        ∀ x, x ∈ˢ interp constants levels env A →
          interp constants levels (Valuation.cons x env) B ∈ˢ univ v
  | .proj _ _ e => WellDenoted constants levels env e
  | .natLit _ => True

theorem wellDenoted_liftN (e : AExpr β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) (n k : Nat) :
    WellDenoted constants levels env (e.liftN n k) ↔
      WellDenoted constants levels (Valuation.skip n k env) e := by
  induction e generalizing k env with
  | lam p A b hA hb | forallE p A b hA hb =>
    simp only [AExpr.liftN, WellDenoted, hA, hb, interp_liftN, Valuation.skip_cons]
  | _ => simp_all [AExpr.liftN, WellDenoted, interp_liftN]

/-- Substitution also needs hereditary validity of the substituted argument.
Interpretation equality alone cannot supply this fact. -/
theorem wellDenoted_inst (e a : AExpr β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) (k : Nat)
    (ha : WellDenoted constants levels (Valuation.skip k 0 env) a)
    (he : WellDenoted constants levels
      (Valuation.insert k (interp constants levels (Valuation.skip k 0 env) a) env) e) :
    WellDenoted constants levels env (e.inst a k) := by
  induction e generalizing k env with
  | bvar i =>
    by_cases hi : i < k
    · simp [AExpr.inst, AExpr.instVar, hi, WellDenoted]
    · by_cases hik : i = k
      · simpa [AExpr.inst, AExpr.instVar, hi, hik, wellDenoted_liftN] using ha
      · simp [AExpr.inst, AExpr.instVar, hi, hik, WellDenoted]
  | app f b hf hb =>
    rcases he with ⟨hfw, hbw, v, A, B, hfm, hbm, hB⟩
    exact ⟨hf env k ha hfw, hb env k ha hbw, v, A, B,
      by simpa only [interp_inst] using hfm,
      by simpa only [interp_inst] using hbm, hB⟩
  | lam p A b hA hb =>
    rcases he with ⟨hAw, hbw, v, B, hz, hB⟩
    refine ⟨hA env k ha hAw, ?_, v, B, hz, ?_⟩
    · intro x hx
      apply hb (Valuation.cons x env) (k + 1)
      · simpa only [Valuation.skip_succ_cons] using ha
      · simp only [Valuation.skip_succ_cons, Valuation.insert_cons]
        exact hbw x (by simpa only [interp_inst] using hx)
    · intro x hx
      simpa only [interp_inst, Valuation.skip_succ_cons, Valuation.insert_cons] using
        hB x (by simpa only [interp_inst] using hx)
  | forallE p A b hA hb =>
    rcases he with ⟨hAw, hbw, v, hz, hB⟩
    refine ⟨hA env k ha hAw, ?_, v, hz, ?_⟩
    · intro x hx
      apply hb (Valuation.cons x env) (k + 1)
      · simpa only [Valuation.skip_succ_cons] using ha
      · simp only [Valuation.skip_succ_cons, Valuation.insert_cons]
        exact hbw x (by simpa only [interp_inst] using hx)
    · intro x hx
      simpa only [interp_inst, Valuation.skip_succ_cons, Valuation.insert_cons] using
        hB x (by simpa only [interp_inst] using hx)
  | proj _ _ e ih => exact ih env k ha he
  | _ => exact he

theorem wellDenoted_instL (e : AExpr β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) (ls : List VLevel) :
    WellDenoted constants levels env (e.instL ls) ↔
      WellDenoted constants (ls.map (VLevel.eval levels)) env e := by
  induction e generalizing env with
  | lam p A b hA hb | forallE p A b hA hb =>
    simp only [AExpr.instL, WellDenoted, hA, hb, interp_instL, regime_instCondition]
  | _ => simp_all [AExpr.instL, WellDenoted, interp_instL]

theorem wellDenoted_rename {γ : Type w} (e : AExpr β) (mapping : β → γ)
    (constants : Assignment β V) (constants' : Assignment γ V)
    (h : ∀ r ls, constants' (r.rename mapping) ls = constants r ls)
    (levels : List Nat) (env : Nat → V) :
    WellDenoted constants' levels env (e.rename mapping) ↔
      WellDenoted constants levels env e := by
  induction e generalizing env with
  | lam p A b hA hb | forallE p A b hA hb =>
    simp only [AExpr.rename, WellDenoted, hA, hb, interp_rename _ _ _ _ h]
  | _ => simp_all [AExpr.rename, WellDenoted, interp_rename _ _ _ _ h]

/-- Conservative beta uses the actual lambda domain even in the proof regime.
The application invariant's possibly different product domain is insufficient
for this step when the lambda's value is the proof point. -/
theorem wellDenoted_beta {constants : Assignment β V} {levels : List Nat}
    {env : Nat → V} {p : Certified.PropWhen} {A b a : AExpr β}
    (hl : WellDenoted constants levels env (.lam p A b))
    (haw : WellDenoted constants levels env a)
    (ha : interp constants levels env a ∈ˢ interp constants levels env A) :
    WellDenoted constants levels env (b.inst a) ∧
      interp constants levels env (.app (.lam p A b) a) =
        interp constants levels env (b.inst a) := by
  rcases hl with ⟨_, hbw, v, B, hz, hB⟩
  constructor
  · apply wellDenoted_inst
    · simpa using haw
    · simpa using hbw _ ha
  · simp only [interp, interp_inst, Valuation.skip_zero, Valuation.insert_zero]
    apply app_lamR ha (fun x hx => (hB x hx).1)
    intro hp x hx
    have hv := hz.mp hp
    simpa only [hv, univ_zero] using (hB x hx).2

end Ix.Kernel.Model
