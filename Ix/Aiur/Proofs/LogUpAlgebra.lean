/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.LogUp
import Ix.Aiur.Proofs.LookupCoordinates

/-! Product reflection for grouped logUp, valid in a commutative ring even
when the coordinate algebra has zero divisors. Denominator cancellation is
deliberately a separate result requiring nonzero native field messages. -/

namespace Aiur.NativeAIR.LogUp

section Algebra

variable {R : Type u} [Lean.Grind.CommRing R]

theorem sub_zero_iff (left right : R) : left - right = 0 ↔ left = right := by
  constructor <;> intro equal <;> grind

theorem clears_cons (weight message inverse denominator fractions cleared : R)
    (inverts : message * inverse = 1) (tail : denominator * fractions = cleared) :
    message * denominator * (weight * inverse + fractions) = weight * denominator + message * cleared := by
  grind

theorem product_cons (value : R) (values : List R) : product (value :: values) = value * product values := rfl

theorem product_append (left right : List R) : product (left ++ right) = product left * product right := by
  induction left with
  | nil => simp only [List.nil_append, product, List.foldr_nil]; grind
  | cons x xs ih =>
    simp only [List.cons_append, product, List.foldr_cons] at *
    rw [ih]
    grind

theorem product_foldl (values : List R) (initial : R) :
    values.foldl (· * ·) initial = initial * product values := by
  induction values generalizing initial with
  | nil => simp only [List.foldl_nil, product, List.foldr_nil]; grind
  | cons x xs ih => simp only [List.foldl_cons, ih, product, List.foldr_cons]; grind

theorem sum_foldl (values : List R) (initial : R) :
    values.foldl (· + ·) initial = initial + sum values := by
  induction values generalizing initial with
  | nil => simp only [List.foldl_nil, sum, List.foldr_nil]; grind
  | cons x xs ih => simp only [List.foldl_cons, ih, sum, List.foldr_cons]; grind

theorem sum_append (left right : List R) : sum (left ++ right) = sum left + sum right := by
  induction left with
  | nil => change sum right = 0 + sum right; grind
  | cons x xs ih =>
    change x + sum (xs ++ right) = (x + sum xs) + sum right
    rw [ih]
    grind

theorem telescope (states increments : Nat → R) (count : Nat)
    (steps : ∀ index, index < count → states (index + 1) - states index = increments index) :
    states count - states 0 = sum ((List.range count).map increments) := by
  induction count with
  | zero => change states 0 - states 0 = 0; grind
  | succ count ih =>
    have earlier := ih (fun index bound => steps index (by omega))
    have last := steps count (by omega)
    rw [List.range_succ, List.map_append, sum_append]
    change states (count + 1) - states 0 = sum ((List.range count).map increments) + (increments count + 0)
    grind

theorem cyclic_accumulator (states fractions : Nat → R) (count : Nat) (delta : R)
    (positive : 0 < count) (wrap : states count = states 0)
    (rows : ∀ index, index < count →
      states (index + 1) - states index + (if index + 1 = count then delta else 0) = fractions index) :
    sum ((List.range count).map fractions) = delta := by
  cases count with
  | zero => omega
  | succ count =>
    have earlier := telescope states fractions count (by
      intro index bound
      have row := rows index (by omega)
      rw [if_neg (by omega : index + 1 ≠ count + 1), Lean.Grind.Semiring.add_zero] at row
      exact row)
    have last := rows count (by omega)
    rw [if_pos rfl, wrap] at last
    rw [List.range_succ, List.map_append, sum_append]
    change sum ((List.range count).map fractions) + (fractions count + 0) = delta
    grind

theorem final_accumulator (accumulators contributions : Nat → R) (count : Nat)
    (finalZero : accumulators count = 0)
    (circuits : ∀ index, index < count → accumulators (index + 1) - accumulators index = contributions index) :
    accumulators 0 + sum ((List.range count).map contributions) = 0 := by
  have total := telescope accumulators contributions count circuits
  rw [finalZero] at total
  grind

theorem prefix_products (values : List R) (initial : R) (index : Nat) :
    (values.scanl (· * ·) initial)[index]? =
      if index ≤ values.length then some (initial * product (values.take index)) else none := by
  rw [List.getElem?_scanl, product_foldl]

theorem prefix_seeded (first : R) (rest : List R) :
    (first :: rest).scanl (· * ·) 1 = 1 :: rest.scanl (· * ·) first := by
  rw [List.scanl_cons, Lean.Grind.Semiring.one_mul]

theorem suffix_seeded (rest : List R) (last : R) :
    (rest ++ [last]).scanr (· * ·) 1 = rest.scanr (· * ·) last ++ [1] := by
  simp only [List.scanr_append, List.foldr_cons, List.foldr_nil, Lean.Grind.Semiring.mul_one,
    List.scanr_cons, List.scanr_nil, List.tail_cons]

theorem suffix_products (values : List R) (index : Nat) :
    (values.scanr (· * ·) 1)[index]? =
      if index ≤ values.length then some (product (values.drop index)) else none := by
  induction values generalizing index with
  | nil => cases index <;> simp [product]
  | cons x xs ih =>
    cases index with
    | zero => simp only [List.scanr_cons, List.getElem?_cons_zero, Nat.zero_le,
        ↓reduceIte, List.drop_zero, product]
    | succ index =>
      simp only [List.scanr_cons, List.getElem?_cons_succ, List.length_cons,
        Nat.succ_le_succ_iff, List.drop_succ_cons, ih]

theorem prefixSuffixTerms_cons (weight message initial : R) (entries : List (R × R)) :
    prefixSuffixTerms initial ((weight, message) :: entries) =
      initial * product (entries.map Prod.snd) * weight :: prefixSuffixTerms (initial * message) entries := by
  cases entries <;>
    simp [prefixSuffixTerms, List.scanl_cons, List.scanr_cons, product]

theorem prefixSuffixTerms_sum (entries : List (R × R)) (initial : R) :
    sum (prefixSuffixTerms initial entries) = initial * numerator entries := by
  induction entries generalizing initial with
  | nil => simp only [prefixSuffixTerms, List.map_nil, List.zip_nil_left, sum, List.foldr_nil,
      numerator]; grind
  | cons entry entries ih =>
    obtain ⟨weight, message⟩ := entry
    rw [prefixSuffixTerms_cons]
    change initial * product (entries.map Prod.snd) * weight +
      sum (prefixSuffixTerms (initial * message) entries) = _
    rw [ih]
    simp only [numerator]
    grind

theorem groupEquation_polynomial (entries : List (R × R)) (difference : R) :
    groupEquation entries difference = product (entries.map Prod.snd) * difference - numerator entries := by
  cases entries with
  | nil => simp only [groupEquation, List.map_nil, product, List.foldr_nil, numerator]; grind
  | cons entry entries =>
    obtain ⟨weight, message⟩ := entry
    cases entries with
    | nil => simp only [groupEquation, List.map_cons, List.map_nil, product, List.foldr_cons,
        List.foldr_nil, numerator]; grind
    | cons entry entries =>
      rw [groupEquation, product_foldl, sum_foldl, prefixSuffixTerms_sum] <;> grind

theorem numerator_append (left right : List (R × R)) :
    numerator (left ++ right) = numerator left * product (right.map Prod.snd) +
      product (left.map Prod.snd) * numerator right := by
  induction left with
  | nil => simp only [List.nil_append, numerator, List.map_nil, product, List.foldr_nil]; grind
  | cons entry entries ih =>
    obtain ⟨weight, message⟩ := entry
    simp only [List.cons_append, numerator, List.map_append, product_append, ih,
      List.map_cons, product_cons]
    grind

end Algebra

section Fingerprint

variable {W : Type u} [Lean.Grind.CommRing W]

theorem fingerprint_reverse_horner (gamma : Coordinates W) (args : List W) :
    fingerprint gamma args = args.reverse.foldl (fun acc arg => acc * gamma + Coordinates.ofBase arg) 0 := by
  simp only [fingerprint, List.foldl_reverse]

theorem fingerprint_nil (gamma : Coordinates W) : fingerprint gamma [] = 0 := rfl

theorem fingerprint_cons (gamma : Coordinates W) (arg : W) (args : List W) :
    fingerprint gamma (arg :: args) = fingerprint gamma args * gamma + Coordinates.ofBase arg := rfl

theorem fingerprint_trailing_zero (gamma : Coordinates W) (args : List W) :
    fingerprint gamma (args ++ [0]) = fingerprint gamma args := by
  induction args with
  | nil => change 0 * gamma + (0 : Coordinates W) = 0; grind
  | cons arg args ih => simp only [List.cons_append, fingerprint_cons, ih]

theorem fingerprint_padding (gamma : Coordinates W) (args : List W) (count : Nat) :
    fingerprint gamma (args ++ List.replicate count 0) = fingerprint gamma args := by
  induction count with
  | zero => simp only [List.replicate_zero, List.append_nil]
  | succ count ih =>
    rw [List.replicate_succ', ← List.append_assoc, fingerprint_trailing_zero, ih]

end Fingerprint
end Aiur.NativeAIR.LogUp
