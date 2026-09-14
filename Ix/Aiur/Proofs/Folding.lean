/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Folding
import Ix.Aiur.Proofs.Interpolation

/-! A native row fold evaluates one global polynomial of reduced degree.
The same global coefficients apply at every child-domain query point.
-/

namespace Aiur.NativeAIR.Folding

open Lean.Grind
open _root_.Aiur.NativeAIR.Quotient (horner horner_nil horner_cons)

variable {R : Type} [CommRing R]

theorem horner_split (point : R) (width : Nat) (coefficients : List R) :
    horner point coefficients = horner point (coefficients.take width) +
      point ^ width * horner point (coefficients.drop width) := by
  have split := Quotient.horner_append point (coefficients.take width) (coefficients.drop width)
  rw [List.take_append_drop, List.length_take] at split
  by_cases enough : width ≤ coefficients.length
  · simpa only [Nat.min_eq_left enough] using split
  · have empty : coefficients.drop width = [] := List.drop_eq_nil_iff.mpr (by omega)
    rw [empty, horner_nil, Semiring.mul_zero, Semiring.add_zero] at split ⊢
    exact split

theorem rowCoefficients_length (arity : Domain.Subgroup) (point : R) (coefficients : List R) :
    (rowCoefficients arity point coefficients).length ≤ Domain.size arity := by
  induction coefficients using rowCoefficients.induct arity with
  | case1 => rw [rowCoefficients, dif_pos rfl]; exact Nat.zero_le _
  | case2 coefficients nonempty ih =>
    rw [rowCoefficients, dif_neg nonempty, Polynomial.add_length, Polynomial.scale_length]
    apply Nat.max_le.mpr
    exact ⟨by simp only [List.length_take]; omega, ih⟩

theorem rowCoefficients_value (arity : Domain.Subgroup) (point root : R) (coefficients : List R)
    (power : root ^ Domain.size arity = point) :
    horner root (rowCoefficients arity point coefficients) = horner root coefficients := by
  induction coefficients using rowCoefficients.induct arity with
  | case1 => rw [rowCoefficients, dif_pos rfl]
  | case2 coefficients nonempty ih =>
    rw [rowCoefficients, dif_neg nonempty, Polynomial.horner_add, Polynomial.horner_scale, ih]
    exact (horner_split root (Domain.size arity) coefficients |>.trans (by rw [power])).symm

theorem rowCoefficients_fold (arity : Domain.Subgroup) (point challenge : R) (coefficients : List R) :
    horner challenge (rowCoefficients arity point coefficients) =
      horner point (foldCoefficients arity challenge coefficients) := by
  induction coefficients using rowCoefficients.induct arity with
  | case1 => rw [rowCoefficients, dif_pos rfl, foldCoefficients, dif_pos rfl]; rfl
  | case2 coefficients nonempty ih =>
    rw [rowCoefficients, dif_neg nonempty, foldCoefficients, dif_neg nonempty,
      Polynomial.horner_add, Polynomial.horner_scale, horner_cons, ih]

theorem foldCoefficients_degree (arity : Domain.Subgroup) (challenge : R) (degree : Nat)
    (coefficients : List R) (bounded : coefficients.length ≤ Domain.size arity * degree) :
    (foldCoefficients arity challenge coefficients).length ≤ degree := by
  induction degree generalizing coefficients with
  | zero =>
    have empty : coefficients = [] := by simpa only [Nat.mul_zero, Nat.le_zero, List.length_eq_zero_iff] using bounded
    subst coefficients
    rw [foldCoefficients, dif_pos rfl]
    exact Nat.le_refl _
  | succ degree ih =>
    by_cases empty : coefficients = []
    · subst coefficients; rw [foldCoefficients, dif_pos rfl]; exact Nat.zero_le _
    · rw [foldCoefficients, dif_neg empty, List.length_cons]
      apply Nat.succ_le_succ
      apply ih
      simp only [List.length_drop]
      rw [Nat.mul_succ] at bounded
      omega

open ProofCodec (Extension)

theorem foldRow_global (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) {index : Nat}
    (bounded : index < 2^(parent.val - arity.val)) (values coefficients : List Extension)
    (shape : values.length = Domain.size arity)
    (agrees : ∀ sample ∈ Interpolation.foldSamples parent arity index values,
      horner sample.1 coefficients = sample.2) (challenge : Extension) :
    Interpolation.foldRow parent arity index values challenge =
      some (horner (Extension.ofBase (FriDomain.queryPoint child index))
        (foldCoefficients arity challenge coefficients)) := by
  rw [← rowCoefficients_fold]
  apply Interpolation.foldRow_evaluate parent child arity dimensions bounded values
    (rowCoefficients arity (Extension.ofBase (FriDomain.queryPoint child index)) coefficients)
    shape (rowCoefficients_length arity _ coefficients)
  intro sample member
  rw [rowCoefficients_value arity _ sample.1 coefficients, agrees sample member]
  have power := Interpolation.foldSamples_powers parent child arity dimensions index values shape sample member
  rwa [Interpolation.foldSamples_length parent arity index values shape] at power

theorem foldRow_codeword (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) {index : Nat}
    (bounded : index < 2^(parent.val - arity.val)) (coefficients : List Extension)
    (challenge : Extension) :
    Interpolation.foldRow parent arity index
      ((Polynomial.foldingNodes parent arity index).map (fun root => horner (Extension.ofBase root) coefficients))
      challenge = some (horner (Extension.ofBase (FriDomain.queryPoint child index))
        (foldCoefficients arity challenge coefficients)) := by
  apply foldRow_global parent child arity dimensions bounded _ coefficients
  · simp only [List.length_map, Polynomial.foldingNodes_length]
  · intro sample member
    unfold Interpolation.foldSamples at member
    have mapped :
        (Polynomial.foldingNodes parent arity index).map (fun root => horner (Extension.ofBase root) coefficients) =
          ((Polynomial.foldingNodes parent arity index).map Extension.ofBase).map (fun root => horner root coefficients) := by
      rw [List.map_map]
      rfl
    rw [mapped, ← List.map_prod_left_eq_zip] at member
    obtain ⟨root, _, rfl⟩ := List.mem_map.mp member
    rfl

theorem foldRow_codeword_degree (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) (degree : Nat)
    (coefficients : List Extension) (length : coefficients.length ≤ Domain.size arity * degree)
    (challenge : Extension) :
    ∃ folded : List Extension, folded.length ≤ degree ∧
      ∀ index, index < 2^(parent.val - arity.val) →
        Interpolation.foldRow parent arity index
          ((Polynomial.foldingNodes parent arity index).map (fun root => horner (Extension.ofBase root) coefficients))
          challenge = some (horner (Extension.ofBase (FriDomain.queryPoint child index)) folded) := by
  exact ⟨foldCoefficients arity challenge coefficients,
    foldCoefficients_degree arity challenge degree coefficients length,
    fun _ bounded => foldRow_codeword parent child arity dimensions bounded coefficients challenge⟩

theorem values_of_agreement (parent arity : Domain.Subgroup) (index : Nat)
    (values coefficients : List Extension) (shape : values.length = Domain.size arity)
    (agrees : ∀ sample ∈ Interpolation.foldSamples parent arity index values,
      horner sample.1 coefficients = sample.2) :
    values = (Polynomial.foldingNodes parent arity index).map (fun root => horner (Extension.ofBase root) coefficients) := by
  calc
    values = (Interpolation.foldSamples parent arity index values).map Prod.snd := by
      apply Eq.symm
      apply List.map_snd_zip
      simp only [List.length_map, Polynomial.foldingNodes_length, shape, Nat.le_refl]
    _ = (Interpolation.foldSamples parent arity index values).map (fun sample => horner sample.1 coefficients) :=
      List.map_congr_left (fun sample member => (agrees sample member).symm)
    _ = _ := by
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map (fun root => horner root coefficients))
          (Interpolation.foldSamples_roots parent arity index values shape)

theorem interpolant_values (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) {index : Nat}
    (bounded : index < 2^(parent.val - arity.val)) (values : List Extension)
    (shape : values.length = Domain.size arity) :
    values = (Polynomial.foldingNodes parent arity index).map (fun root => horner (Extension.ofBase root)
      (Interpolation.coefficients (Interpolation.foldSamples parent arity index values)
        (Extension.ofBase (Interpolation.foldScale parent arity index)))) := by
  apply values_of_agreement parent arity index values _ shape
  intro sample member
  have atNode := Interpolation.foldRow_at_node parent child arity dimensions bounded values shape sample.1 sample.2 member
  rw [Interpolation.foldRow_polynomial parent child arity dimensions bounded values shape] at atNode
  exact Option.some.inj atNode

theorem interpolants_different (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) {index : Nat}
    (bounded : index < 2^(parent.val - arity.val)) (left right : List Extension)
    (leftShape : left.length = Domain.size arity) (rightShape : right.length = Domain.size arity)
    (different : left ≠ right) :
    ¬ Polynomial.IsZero (Polynomial.sub
      (Interpolation.coefficients (Interpolation.foldSamples parent arity index left)
        (Extension.ofBase (Interpolation.foldScale parent arity index)))
      (Interpolation.coefficients (Interpolation.foldSamples parent arity index right)
        (Extension.ofBase (Interpolation.foldScale parent arity index)))) := by
  intro zero
  apply different
  conv => lhs; rw [interpolant_values parent child arity dimensions bounded left leftShape]
  conv => rhs; rw [interpolant_values parent child arity dimensions bounded right rightShape]
  apply List.map_congr_left
  intro root _
  have equal := Polynomial.horner_zero (Extension.ofBase root) zero
  rw [Polynomial.horner_sub] at equal
  exact (LogUp.sub_zero_iff _ _).mp equal

/-- A deterministic bound for two fixed distinct rows and distinct challenges. -/
theorem foldRow_equal_count_le (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) {index : Nat}
    (bounded : index < 2^(parent.val - arity.val)) (left right challenges : List Extension)
    (leftShape : left.length = Domain.size arity) (rightShape : right.length = Domain.size arity)
    (different : left ≠ right) (unique : challenges.Nodup) :
    (challenges.filter (fun challenge => Interpolation.foldRow parent arity index left challenge ==
      Interpolation.foldRow parent arity index right challenge)).length ≤ Domain.size arity - 1 := by
  have bound := Polynomial.equal_count_le (fun a b => (Extension.mul_eq_zero_iff a b).mp) _ _ challenges
    (interpolants_different parent child arity dimensions bounded left right leftShape rightShape different) unique
  have leftBound := Interpolation.coefficients_length (Interpolation.foldSamples parent arity index left)
    (Extension.ofBase (Interpolation.foldScale parent arity index))
  have rightBound := Interpolation.coefficients_length (Interpolation.foldSamples parent arity index right)
    (Extension.ofBase (Interpolation.foldScale parent arity index))
  rw [Interpolation.foldSamples_length parent arity index left leftShape] at leftBound
  rw [Interpolation.foldSamples_length parent arity index right rightShape] at rightBound
  simp only [Interpolation.foldRow_polynomial parent child arity dimensions bounded left leftShape,
    Interpolation.foldRow_polynomial parent child arity dimensions bounded right rightShape,
    Option.some_beq_some]
  omega

end Aiur.NativeAIR.Folding
