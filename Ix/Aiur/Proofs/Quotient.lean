/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.QuotientAlgebra
import Ix.Aiur.Proofs.Selectors

/-! Checked coordinate pairing and the exact out-of-domain equality.
This reflects arithmetic only; commitment binding and low-degree extraction
remain distinct obligations before the equality implies trace constraints.
-/

namespace Aiur.NativeAIR.Quotient

open ProofCodec (Extension)
open LogUp (Coordinates)

theorem coefficients_flatten (pairs : List (Coordinates Extension)) :
    coefficients (Coordinates.flatten pairs) =
      some (pairs.map fun pair => pair.c0 + pair.c1 * Extension.basis) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
    simp only [Coordinates.flatten, List.flatMap_cons, List.cons_append, List.nil_append,
      List.map_cons] at *
    simp only [coefficients, ih, bind, pure, Option.bind_some]

theorem coefficients_success {row values : List Extension} (accepted : coefficients row = some values) :
    ∃ pairs : List (Coordinates Extension), row = Coordinates.flatten pairs ∧
      values = pairs.map (fun pair => pair.c0 + pair.c1 * Extension.basis) := by
  induction row using coefficients.induct generalizing values with
  | case1 => cases accepted; exact ⟨[], rfl, rfl⟩
  | case2 first => cases accepted
  | case3 first second rest ih =>
    simp only [coefficients, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at accepted
    obtain ⟨tail, tailRead, rfl⟩ := accepted
    obtain ⟨pairs, restEqual, tailEqual⟩ := ih tailRead
    refine ⟨⟨first, second⟩ :: pairs, ?_, ?_⟩
    · simp only [Coordinates.flatten, List.flatMap_cons, List.cons_append, List.nil_append] at *
      rw [restEqual]
    · rw [tailEqual]; rfl

theorem coefficients_length {row values : List Extension} (accepted : coefficients row = some values) :
    row.length = 2 * values.length := by
  obtain ⟨pairs, rfl, rfl⟩ := coefficients_success accepted
  rw [Coordinates.flatten_length, List.length_map]

theorem coefficients_defined (row : List Extension) (even : row.length % 2 = 0) :
    ∃ values, coefficients row = some values := by
  induction row using coefficients.induct with
  | case1 => exact ⟨[], rfl⟩
  | case2 first => simp only [List.length_cons, List.length_nil] at even; omega
  | case3 first second rest ih =>
    have tailEven : rest.length % 2 = 0 := by
      simp only [List.length_cons] at even
      omega
    obtain ⟨tail, read⟩ := ih tailEven
    exact ⟨(first + second * Extension.basis) :: tail, by
      simp only [coefficients, read, bind, pure, Option.bind_some]⟩

theorem coefficients_defined_iff (row : List Extension) :
    (∃ values, coefficients row = some values) ↔ row.length % 2 = 0 := by
  constructor
  · rintro ⟨values, accepted⟩
    rw [coefficients_length accepted]
    omega
  · exact coefficients_defined row

theorem evaluate_success (domain : Domain.Subgroup) (point : Extension) {row : List Extension} {value : Extension}
    (accepted : evaluate domain point row = some value) :
    ∃ values, coefficients row = some values ∧
      value = horner (point ^ Domain.size domain) values := by
  simp only [evaluate, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at accepted
  obtain ⟨values, read, rfl⟩ := accepted
  exact ⟨values, read, by rw [Extension.power_eq]⟩

theorem evaluate_powers (domain : Domain.Subgroup) (point : Extension) {row : List Extension} {value : Extension}
    (accepted : evaluate domain point row = some value) :
    ∃ pairs : List (Coordinates Extension), row = Coordinates.flatten pairs ∧
      value = LogUp.sum ((pairs.zipIdx).map fun (pair, index) =>
        point ^ (Domain.size domain * index) * (pair.c0 + pair.c1 * Extension.basis)) := by
  obtain ⟨values, read, rfl⟩ := evaluate_success domain point accepted
  obtain ⟨pairs, rowEqual, rfl⟩ := coefficients_success read
  refine ⟨pairs, rowEqual, ?_⟩
  have powers := horner_powers (point ^ Domain.size domain)
    (pairs.map fun pair => pair.c0 + pair.c1 * Extension.basis) 0
  simp only [Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.one_mul] at powers
  rw [powers]
  simp only [List.zipIdx_map, List.map_map, Function.comp_def, Domain.Algebra.power_mul,
    Prod.map, id]

theorem check_true_iff (domain : Domain.Subgroup) (point alpha : Extension) (constraints row : List Extension) :
    check domain point alpha constraints row = some true ↔
      Domain.vanishing domain point ≠ 0 ∧ ∃ values, coefficients row = some values ∧
        composition alpha constraints =
          Domain.vanishing domain point * horner (point ^ Domain.size domain) values := by
  constructor
  · intro accepted
    simp only [check, bind, pure, Option.bind_eq_some_iff, Option.some.injEq, beq_iff_eq] at accepted
    obtain ⟨selected, selectorsRead, value, valueRead, equal⟩ := accepted
    have invert := (Domain.selectors_success domain point selected selectorsRead).2.2.2
    obtain ⟨values, read, valueEqual⟩ := evaluate_success domain point valueRead
    refine ⟨(Domain.selectors_defined_iff _ _).mp ⟨selected, selectorsRead⟩, values, read, ?_⟩
    rw [← valueEqual]
    exact (inverse_check _ _ _ _ invert).mp equal
  · rintro ⟨nonzero, values, read, identity⟩
    obtain ⟨selected, selectorsRead⟩ := Domain.selectors_defined domain point nonzero
    have invert := (Domain.selectors_success domain point selected selectorsRead).2.2.2
    have equal := (inverse_check _ _ _ _ invert).mpr identity
    simp only [check, selectorsRead, evaluate, read, bind, pure, Option.bind_some,
      Extension.power_eq, equal, beq_self_eq_true]

end Aiur.NativeAIR.Quotient
