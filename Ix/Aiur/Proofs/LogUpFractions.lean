/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.LogUp

/-! Denominator cancellation on base-field trace rows. The coordinate pairs
then identify with the proved native extension field. This identification
and cancellation are not applied to arbitrary challenge-field coordinates.
The pole-free premise remains a cryptographic obligation. -/

namespace Aiur.NativeAIR.LogUp

open ProofCodec (Extension)

/-- The total inverse convention is used only under `PoleFree` below. -/
def inverseValue (value : Extension) : Extension := value.tryInverse.getD 0

def fractionSum (entries : List (Extension × Extension)) : Extension :=
  sum (entries.map fun (weight, message) => weight * inverseValue message)

def PoleFree (entries : List (Extension × Extension)) : Prop :=
  ∀ entry ∈ entries, entry.2 ≠ 0

def fieldEntries (entries : List (Coordinates G × Coordinates G)) : List (Extension × Extension) :=
  entries.map fun (weight, message) => (weight.toExtension, message.toExtension)

theorem inverseValue_correct (value : Extension) (nonzero : value ≠ 0) :
    value * inverseValue value = 1 := by
  obtain ⟨read, correct⟩ := Extension.inverse_correct value nonzero
  simpa only [inverseValue, read, Option.getD_some] using correct

theorem product_nonzero (values : List Extension) (nonzero : ∀ value ∈ values, value ≠ 0) :
    product values ≠ 0 := by
  induction values with
  | nil => exact Extension.one_ne_zero
  | cons value values ih =>
    rw [product_cons]
    intro zero
    exact ((Extension.mul_eq_zero_iff _ _).mp zero).elim
      (nonzero value List.mem_cons_self)
      (ih (fun value member => nonzero value (List.mem_cons_of_mem _ member)))

theorem poleFree_product (entries : List (Extension × Extension)) (free : PoleFree entries) :
    product (entries.map Prod.snd) ≠ 0 := by
  apply product_nonzero
  intro value member
  obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
  exact free entry present

theorem fractionSum_cons (weight message : Extension) (entries : List (Extension × Extension)) :
    fractionSum ((weight, message) :: entries) = weight * inverseValue message + fractionSum entries := rfl

theorem fractionSum_append (left right : List (Extension × Extension)) :
    fractionSum (left ++ right) = fractionSum left + fractionSum right := by
  induction left with
  | nil => change fractionSum right = 0 + fractionSum right; grind
  | cons entry entries ih =>
    obtain ⟨weight, message⟩ := entry
    simp only [List.cons_append, fractionSum_cons, ih]
    grind

theorem fractionSum_clears (entries : List (Extension × Extension)) (free : PoleFree entries) :
    product (entries.map Prod.snd) * fractionSum entries = numerator entries := by
  induction entries with
  | nil => change (1 : Extension) * 0 = 0; grind
  | cons entry entries ih =>
    obtain ⟨weight, message⟩ := entry
    have inverse := inverseValue_correct message (free _ List.mem_cons_self)
    have tail := ih (fun entry member => free entry (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, product_cons, fractionSum_cons, numerator]
    exact clears_cons _ _ _ _ _ _ inverse tail

theorem groupEquation_zero_iff (entries : List (Extension × Extension)) (difference : Extension)
    (free : PoleFree entries) : groupEquation entries difference = 0 ↔ difference = fractionSum entries := by
  rw [groupEquation_polynomial, sub_zero_iff]
  constructor
  · intro zero
    apply Extension.mul_left_cancel (poleFree_product entries free)
    rw [fractionSum_clears entries free]
    exact zero
  · intro same
    rw [same, fractionSum_clears entries free]

theorem product_toExtension (values : List (Coordinates G)) :
    (product values).toExtension = product (values.map Coordinates.toExtension) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [product_cons, Coordinates.toExtension_mul, List.map_cons, ih]

theorem fieldEntries_messages (entries : List (Coordinates G × Coordinates G)) :
    (fieldEntries entries).map Prod.snd = (entries.map Prod.snd).map Coordinates.toExtension := by
  simp only [fieldEntries, List.map_map]
  rfl

theorem numerator_toExtension (entries : List (Coordinates G × Coordinates G)) :
    (numerator entries).toExtension = numerator (fieldEntries entries) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨weight, message⟩ := entry
    change (weight * product (entries.map Prod.snd) + message * numerator entries).toExtension =
      weight.toExtension * product ((fieldEntries entries).map Prod.snd) +
        message.toExtension * numerator (fieldEntries entries)
    rw [Coordinates.toExtension_add, Coordinates.toExtension_mul, Coordinates.toExtension_mul,
      product_toExtension, fieldEntries_messages, ih]

theorem groupEquation_toExtension (entries : List (Coordinates G × Coordinates G)) (difference : Coordinates G) :
    (groupEquation entries difference).toExtension = groupEquation (fieldEntries entries) difference.toExtension := by
  rw [groupEquation_polynomial, groupEquation_polynomial, Coordinates.toExtension_sub,
    Coordinates.toExtension_mul, product_toExtension, numerator_toExtension, fieldEntries_messages]

theorem coordinate_group_zero_iff (entries : List (Coordinates G × Coordinates G)) (difference : Coordinates G)
    (free : PoleFree (fieldEntries entries)) :
    groupEquation entries difference = 0 ↔ difference.toExtension = fractionSum (fieldEntries entries) := by
  rw [← Coordinates.toExtension_zero_iff, groupEquation_toExtension, groupEquation_zero_iff _ _ free]

theorem coordinate_polynomial_zero_iff (entries : List (Coordinates G × Coordinates G)) (difference : Coordinates G)
    (free : PoleFree (fieldEntries entries)) :
    product (entries.map Prod.snd) * difference = numerator entries ↔
      difference.toExtension = fractionSum (fieldEntries entries) := by
  have reflected := coordinate_group_zero_iff entries difference free
  rw [groupEquation_polynomial] at reflected
  have subtract : product (entries.map Prod.snd) * difference - numerator entries = 0 ↔
      product (entries.map Prod.snd) * difference = numerator entries := by
    constructor <;> intro equal <;> grind
  exact subtract.symm.trans reflected

theorem fingerprint_toExtension (gamma : Coordinates G) (args : List G) :
    (fingerprint gamma args).toExtension =
      args.foldr (fun arg acc => acc * gamma.toExtension + Extension.ofBase arg) 0 := by
  induction args with
  | nil => rfl
  | cons arg args ih =>
    rw [fingerprint_cons, Coordinates.toExtension_add, Coordinates.toExtension_mul, ih]
    rfl

/-- A zero denominator can make an accumulator step unconstrained. -/
theorem pole_can_hide_step :
    groupEquation ([(0, 0)] : List (Extension × Extension)) 1 = 0 ∧
      (1 : Extension) ≠ fractionSum [(0, 0)] := by
  constructor
  · change (0 : Extension) * 1 - 0 = 0; grind
  · have zero : fractionSum ([(0, 0)] : List (Extension × Extension)) = 0 := by
      change (0 : Extension) * inverseValue 0 + 0 = 0; grind
    rw [zero]
    exact Extension.one_ne_zero

end Aiur.NativeAIR.LogUp
