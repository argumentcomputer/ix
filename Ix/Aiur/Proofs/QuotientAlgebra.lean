/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Quotient
import Ix.Aiur.Proofs.SelectorAlgebra
import Ix.Aiur.Proofs.LogUpAlgebra

/-! The two Horner conventions used by the native verifier: quotient
coefficients in ascending powers and constraints in descending powers.
-/

namespace Aiur.NativeAIR.Quotient

open Lean.Grind
variable {W : Type} [CommRing W]

theorem horner_nil (point : W) : horner point [] = 0 := rfl

theorem horner_cons (point first : W) (rest : List W) :
    horner point (first :: rest) = first + point * horner point rest := rfl

theorem horner_append (point : W) (left right : List W) :
    horner point (left ++ right) = horner point left + point ^ left.length * horner point right := by
  induction left with
  | nil => simp only [List.nil_append, List.length_nil, horner_nil, Semiring.pow_zero]; grind
  | cons first rest ih =>
    simp only [List.cons_append, horner_cons, ih, List.length_cons, Semiring.pow_succ]
    grind

theorem horner_powers (point : W) (values : List W) (offset : Nat) :
    point ^ offset * horner point values =
      LogUp.sum ((values.zipIdx offset).map fun (value, index) => point ^ index * value) := by
  induction values generalizing offset with
  | nil => simp only [horner_nil, Semiring.mul_zero, List.zipIdx_nil, List.map_nil, LogUp.sum, List.foldr_nil]
  | cons first rest ih =>
    simp only [horner_cons, List.zipIdx_cons, List.map_cons, LogUp.sum, List.foldr_cons]
    have tail := ih (offset + 1)
    rw [Semiring.pow_succ] at tail
    simp only [LogUp.sum] at tail
    grind

theorem composition_from (point initial : W) (values : List W) :
    values.foldl (fun accumulated value => accumulated * point + value) initial =
      initial * point ^ values.length + horner point values.reverse := by
  induction values generalizing initial with
  | nil => simp only [List.foldl_nil, List.length_nil, List.reverse_nil, horner_nil, Semiring.pow_zero]; grind
  | cons first rest ih =>
    simp only [List.foldl_cons, ih, List.length_cons, List.reverse_cons, horner_append,
      List.length_reverse, horner_cons, horner_nil, Semiring.pow_succ]
    grind

theorem composition_horner (point : W) (values : List W) : composition point values = horner point values.reverse := by
  rw [composition, composition_from, Semiring.zero_mul]
  grind

theorem composition_order (point : W) (values : List W) :
    composition point values =
      LogUp.sum ((values.reverse.zipIdx).map fun (value, index) => point ^ index * value) := by
  rw [composition_horner]
  have powers := horner_powers point values.reverse 0
  simpa only [Semiring.pow_zero, Semiring.one_mul] using powers

theorem composition_append (point : W) (user lookup : List W) :
    composition point (user ++ lookup) =
      composition point user * point ^ lookup.length + composition point lookup := by
  rw [composition, List.foldl_append, composition_from, ← composition_horner]
  rfl

theorem composition_zero (point : W) (values : List W) (zero : ∀ value ∈ values, value = 0) :
    composition point values = 0 := by
  rw [composition_horner]
  suffices h : ∀ values : List W, (∀ value ∈ values, value = 0) → horner point values = 0 from
    h values.reverse (by simpa only [List.mem_reverse] using zero)
  intro values zero
  induction values with
  | nil => rfl
  | cons first rest ih =>
    rw [horner_cons, zero first (by simp), ih (fun value member => zero value (by simp [member]))]
    grind

theorem inverse_check (vanishing inverse composition quotient : W) (cancel : vanishing * inverse = 1) :
    composition * inverse = quotient ↔ composition = vanishing * quotient := by
  constructor
  · intro accepted
    have multiplied := congrArg (fun value => vanishing * value) accepted
    grind
  · intro identity
    rw [identity]
    grind

end Aiur.NativeAIR.Quotient
