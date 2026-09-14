/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Domain

/-! The checked native rational formulas evaluate the selector polynomials
away from the trace domain. Their row values include the native, unnormalized
last-row factor `n * generator`, which is a nonzero Goldilocks element.
-/

namespace Aiur.NativeAIR.Domain

open Lean.Grind
open ProofCodec (Extension)
open Algebra

theorem first_at_row (domain : Subgroup) (index : Fin (size domain)) :
    dividedPowers (point domain index) (1 : G) (size domain) =
      if index.val = 0 then G.ofNat (size domain) else 0 := by
  by_cases first : index.val = 0
  · rw [if_pos first, (point_first_iff domain index).mpr first, dividedPowers_diagonal,
      Semiring.one_pow, Semiring.mul_one]
    rfl
  · rw [if_neg first]
    have factor := root_dividedPowers (point domain index) (1 : G)
      (Semiring.one_pow (size domain))
    rw [point_power, (by decide : (1 : G) - 1 = 0)] at factor
    exact ((G.mul_eq_zero_iff _ _).mp factor).resolve_left
      (fun zero => first ((point_first_iff domain index).mp ((G.sub_eq_zero_iff _ _).mp zero)))

theorem last_at_row (domain : Subgroup) (index : Fin (size domain)) :
    dividedPowers (point domain index) (lastPoint domain) (size domain) =
      if index.val = size domain - 1 then normalizer domain else 0 := by
  by_cases last : index.val = size domain - 1
  · rw [if_pos last, (point_last_iff domain index).mpr last, dividedPowers_diagonal,
      lastPoint_predecessor]
    rfl
  · rw [if_neg last]
    have factor := root_dividedPowers (point domain index) (lastPoint domain) (lastPoint_power domain)
    rw [point_power, (by decide : (1 : G) - 1 = 0)] at factor
    exact ((G.mul_eq_zero_iff _ _).mp factor).resolve_left
      (fun zero => last ((point_last_iff domain index).mp ((G.sub_eq_zero_iff _ _).mp zero)))

theorem transition_at_row (domain : Subgroup) (index : Fin (size domain)) :
    point domain index - lastPoint domain = 0 ↔ index.val = size domain - 1 := by
  rw [G.sub_eq_zero_iff, point_last_iff]

theorem ofBase_dividedPowers (x a : G) (n : Nat) :
    Extension.ofBase (dividedPowers x a n) =
      dividedPowers (Extension.ofBase x) (Extension.ofBase a) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dividedPowers, dividedPowers, Extension.ofBase_add,
      Extension.ofBase_mul, Extension.ofBase_power, ih]

theorem vanishing_eq (domain : Subgroup) (value : Extension) :
    vanishing domain value = value ^ size domain - 1 := by
  rw [vanishing, Extension.power_eq]

theorem vanishing_at_row (domain : Subgroup) (index : Fin (size domain)) :
    vanishing domain (Extension.ofBase (point domain index)) = 0 := by
  rw [vanishing_eq, ← Extension.ofBase_power, point_power]
  change (1 : Extension) - 1 = 0
  grind

theorem lastPoint_extension_power (domain : Subgroup) :
    Extension.ofBase (lastPoint domain) ^ size domain = 1 := by
  rw [← Extension.ofBase_power, lastPoint_power]
  rfl

theorem root_difference_nonzero (x a : Extension) {n : Nat}
    (root : a ^ n = 1) (nonzero : x ^ n - 1 ≠ 0) : x - a ≠ 0 := by
  intro zero
  have same : x = a := by grind
  subst x
  apply nonzero
  rw [root]
  grind

theorem selectors_success (domain : Subgroup) (value : Extension) (selected : Selectors Extension)
    (accepted : selectors domain value = some selected) :
    selected.isFirst = dividedPowers value 1 (size domain) ∧
    selected.isLast = dividedPowers value (Extension.ofBase (lastPoint domain)) (size domain) ∧
    selected.isTransition = value - Extension.ofBase (lastPoint domain) ∧
    vanishing domain value * selected.invVanishing = 1 := by
  simp only [selectors, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at accepted
  obtain ⟨firstInverse, first, lastInverse, last, vanishingInverse, invert, rfl⟩ := accepted
  exact ⟨by
    rw [vanishing_eq]
    exact dividedPowers_off_root value 1 firstInverse (Semiring.one_pow _)
      ((Extension.tryInverse_some_iff _ _).mp first), by
    rw [vanishing_eq]
    exact dividedPowers_off_root value _ lastInverse (lastPoint_extension_power domain)
      ((Extension.tryInverse_some_iff _ _).mp last), rfl,
    (Extension.tryInverse_some_iff _ _).mp invert⟩

theorem selectors_defined (domain : Subgroup) (value : Extension)
    (nonzero : vanishing domain value ≠ 0) : ∃ selected, selectors domain value = some selected := by
  have polynomial : value ^ size domain - 1 ≠ 0 := by rwa [vanishing_eq] at nonzero
  obtain ⟨first, firstDefined⟩ := Option.ne_none_iff_exists'.mp (fun absent =>
    root_difference_nonzero value 1 (Semiring.one_pow _) polynomial
      ((Extension.tryInverse_none_iff _).mp absent))
  obtain ⟨last, lastDefined⟩ := Option.ne_none_iff_exists'.mp (fun absent =>
    root_difference_nonzero value _ (lastPoint_extension_power domain) polynomial
      ((Extension.tryInverse_none_iff _).mp absent))
  obtain ⟨inverse, inverseDefined⟩ := Option.ne_none_iff_exists'.mp (fun absent =>
    nonzero ((Extension.tryInverse_none_iff _).mp absent))
  refine ⟨⟨vanishing domain value * first, vanishing domain value * last,
    value - Extension.ofBase (lastPoint domain), inverse⟩, ?_⟩
  simp only [selectors, firstDefined, lastDefined, inverseDefined, bind, pure, Option.bind_some]

theorem selectors_defined_iff (domain : Subgroup) (value : Extension) :
    (∃ selected, selectors domain value = some selected) ↔ vanishing domain value ≠ 0 := by
  constructor
  · rintro ⟨selected, accepted⟩ zero
    have inverse := (selectors_success domain value selected accepted).2.2.2
    rw [zero, Extension.zero_mul] at inverse
    exact Extension.one_ne_zero inverse.symm
  · exact selectors_defined domain value

theorem selectors_none_at_row (domain : Subgroup) (index : Fin (size domain)) :
    selectors domain (Extension.ofBase (point domain index)) = none := by
  by_cases absent : selectors domain (Extension.ofBase (point domain index)) = none
  · exact absent
  · obtain ⟨selected, accepted⟩ := Option.ne_none_iff_exists'.mp absent
    exact False.elim ((selectors_defined_iff _ _).mp ⟨selected, accepted⟩ (vanishing_at_row _ _))

end Aiur.NativeAIR.Domain
