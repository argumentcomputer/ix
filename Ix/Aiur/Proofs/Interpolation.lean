/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Interpolation
import Ix.Aiur.Proofs.Polynomial

/-! Lagrange interpolation on the native folding cosets. Synthetic division
and the checked polynomial root bound establish the diagonal weights, exact
node values, degree bound and uniqueness. The runtime formula is then proved
to evaluate those coefficients, with its node branch preceding inversion.
-/

namespace Aiur.NativeAIR.Interpolation

open Lean.Grind
open _root_.Aiur.NativeAIR.Quotient (horner horner_nil horner_cons)
attribute [local instance] Semiring.natCast Ring.intCast

variable {R : Type} [CommRing R]

theorem derivative_zero (point : R) {coefficients : List R} (zero : Polynomial.IsZero coefficients) :
    derivativeValue point coefficients = 0 := by
  induction coefficients with
  | nil => rfl
  | cons coefficient rest ih =>
    obtain ⟨_, tailZero⟩ := (Polynomial.isZero_cons _ _).mp zero
    rw [derivativeValue, Polynomial.horner_zero point tailZero, ih tailZero]
    grind

theorem derivative_neg (point : R) (coefficients : List R) :
    derivativeValue point (coefficients.map (0 - ·)) = 0 - derivativeValue point coefficients := by
  induction coefficients with
  | nil => change (0 : R) = 0 - 0; grind
  | cons first rest ih =>
    simp only [List.map_cons, derivativeValue, Polynomial.horner_neg, ih]
    grind

theorem derivative_sub (point : R) (left right : List R) :
    derivativeValue point (Polynomial.sub left right) = derivativeValue point left - derivativeValue point right := by
  induction left generalizing right with
  | nil => rw [Polynomial.sub, derivative_neg, derivativeValue]
  | cons first left ih =>
    cases right with
    | nil => rw [Polynomial.sub_nil, derivativeValue]; grind
    | cons second right =>
      rw [Polynomial.sub, derivativeValue, Polynomial.horner_sub, ih, derivativeValue, derivativeValue]
      grind

theorem divide_diagonal (point : R) (coefficients : List R) :
    horner point (Polynomial.divide point coefficients) = derivativeValue point coefficients := by
  induction coefficients using Polynomial.divide.induct with
  | case1 => rfl
  | case2 first => simp only [Polynomial.divide, horner_nil, derivativeValue]; grind
  | case3 first next rest ih =>
    change horner point (next :: rest) + point * horner point (Polynomial.divide point (next :: rest)) =
      horner point (next :: rest) + point * derivativeValue point (next :: rest)
    rw [ih]

theorem monomial_value (point : R) (degree : Nat) :
    horner point (List.replicate degree 0 ++ [1]) = point ^ degree := by
  rw [Quotient.horner_append, Polynomial.horner_replicate_zero, List.length_replicate]
  simp only [horner_cons, horner_nil]
  grind

theorem monomial_derivative (point : R) (degree : Nat) :
    derivativeValue point (List.replicate degree 0 ++ [1]) = (degree : R) * point ^ (degree - 1) := by
  induction degree with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, derivativeValue, horner_nil, Semiring.natCast_zero]
    grind
  | succ degree ih =>
    rw [List.replicate_succ, List.cons_append, derivativeValue, monomial_value, ih, Semiring.natCast_succ]
    cases degree with
    | zero => simp only [Nat.zero_sub, Nat.add_sub_cancel, Semiring.pow_zero, Semiring.natCast_zero]; grind
    | succ degree => simp only [Nat.add_sub_cancel, Semiring.pow_succ]; grind

theorem powerMinus_derivative (point constant : R) (degree : Nat) :
    derivativeValue point (Polynomial.powerMinus degree constant) = (degree : R) * point ^ (degree - 1) := by
  rw [Polynomial.powerMinus, derivative_sub, monomial_derivative]
  simp only [derivativeValue, horner_nil]
  grind

theorem root_product_derivative (noZeroDivisors : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0)
    (roots : List R) (constant : R) (unique : roots.Nodup) (positive : 0 < roots.length)
    (powers : ∀ root ∈ roots, root ^ roots.length = constant) (point : R) :
    derivativeValue point (Polynomial.fromRoots roots) = (roots.length : R) * point ^ (roots.length - 1) := by
  have zero : Polynomial.IsZero (Polynomial.sub (Polynomial.fromRoots roots) (Polynomial.powerMinus roots.length constant)) := by
    apply Polynomial.monic_zero_sub_of_samples noZeroDivisors _ _ roots
      (Polynomial.fromRoots_monic roots) (Polynomial.powerMinus_monic positive constant) unique
    · rw [Polynomial.fromRoots_length, Polynomial.powerMinus_length]
    · rw [Polynomial.fromRoots_length]
      omega
    · intro root member
      rw [Polynomial.fromRoots_vanishes roots root member, Polynomial.horner_powerMinus, powers root member]
      grind
  have difference := derivative_zero point zero
  rw [derivative_sub, powerMinus_derivative] at difference
  exact (LogUp.sub_zero_iff _ _).mp difference

theorem root_quotient_diagonal (noZeroDivisors : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0)
    (roots : List R) (constant : R) (unique : roots.Nodup) (positive : 0 < roots.length)
    (powers : ∀ root ∈ roots, root ^ roots.length = constant) (point : R) :
    horner point (Polynomial.divide point (Polynomial.fromRoots roots)) =
      (roots.length : R) * point ^ (roots.length - 1) := by
  rw [divide_diagonal, root_product_derivative noZeroDivisors roots constant unique positive powers]

theorem closed_weight_diagonal (noZeroDivisors : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0)
    (roots : List R) (constant scale root : R) (unique : roots.Nodup) (positive : 0 < roots.length)
    (powers : ∀ root ∈ roots, root ^ roots.length = constant) (member : root ∈ roots)
    (inverts : (roots.length : R) * constant * scale = 1) :
    (root * scale) * horner root (Polynomial.divide root (Polynomial.fromRoots roots)) = 1 := by
  rw [root_quotient_diagonal noZeroDivisors roots constant unique positive powers]
  have power : root ^ (roots.length - 1) * root = constant := by
    rw [← Semiring.pow_succ, Nat.sub_add_cancel (by omega)]
    exact powers root member
  grind

theorem combine_length (vanishing : List R) (scale : R) (samples : List (R × R)) :
    (combine vanishing scale samples).length ≤ vanishing.length - 1 := by
  induction samples with
  | nil => exact Nat.zero_le _
  | cons sample samples ih =>
    rw [combine, Polynomial.add_length, Polynomial.scale_length, Polynomial.divide_length]
    exact Nat.max_le.mpr ⟨Nat.le_refl _, ih⟩

theorem coefficients_length (samples : List (R × R)) (scale : R) :
    (coefficients samples scale).length ≤ samples.length := by
  have bounded := combine_length (Polynomial.fromRoots (samples.map Prod.fst)) scale samples
  simpa only [coefficients, Polynomial.fromRoots_length, Nat.add_sub_cancel, List.length_map] using bounded

theorem combine_zero (vanishing : List R) (scale point : R) (samples : List (R × R))
    (zero : ∀ sample ∈ samples, horner point (Polynomial.divide sample.1 vanishing) = 0) :
    horner point (combine vanishing scale samples) = 0 := by
  induction samples with
  | nil => rfl
  | cons sample samples ih =>
    rw [combine, Polynomial.horner_add, Polynomial.horner_scale,
      zero sample List.mem_cons_self, ih (fun value member => zero value (List.mem_cons_of_mem _ member))]
    grind

theorem combine_at_node (vanishing : List R) (scale root value : R) (samples : List (R × R))
    (unique : (samples.map Prod.fst).Nodup) (member : (root, value) ∈ samples)
    (diagonal : (root * scale) * horner root (Polynomial.divide root vanishing) = 1)
    (offDiagonal : ∀ sample ∈ samples, sample.1 ≠ root → horner root (Polynomial.divide sample.1 vanishing) = 0) :
    horner root (combine vanishing scale samples) = value := by
  induction samples with
  | nil => cases member
  | cons sample samples ih =>
    obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
    rw [combine, Polynomial.horner_add, Polynomial.horner_scale]
    rcases List.mem_cons.mp member with same | later
    · subst sample
      have tailZero : horner root (combine vanishing scale samples) = 0 := by
        apply combine_zero
        intro sample member
        apply offDiagonal sample (List.mem_cons_of_mem _ member)
        intro equal
        exact absent (List.mem_map.mpr ⟨sample, member, equal⟩)
      rw [tailZero]
      grind
    · have different : sample.1 ≠ root := by
        intro same
        exact absent (List.mem_map.mpr ⟨(root, value), later, same.symm⟩)
      rw [offDiagonal sample List.mem_cons_self different,
        ih tailUnique later (fun item member => offDiagonal item (List.mem_cons_of_mem _ member))]
      grind

theorem coefficients_at_node (noZeroDivisors : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0)
    (samples : List (R × R)) (constant scale root value : R)
    (unique : (samples.map Prod.fst).Nodup) (positive : 0 < samples.length)
    (powers : ∀ sample ∈ samples, sample.1 ^ samples.length = constant)
    (inverts : (samples.length : R) * constant * scale = 1) (member : (root, value) ∈ samples) :
    horner root (coefficients samples scale) = value := by
  have rootMember : root ∈ samples.map Prod.fst := List.mem_map.mpr ⟨(root, value), member, rfl⟩
  apply combine_at_node _ scale root value samples unique member
  · apply closed_weight_diagonal noZeroDivisors (samples.map Prod.fst) constant scale root unique
      (by simpa only [List.length_map] using positive) _ rootMember
      (by simpa only [List.length_map] using inverts)
    intro node nodeMember
    obtain ⟨sample, sampleMember, rfl⟩ := List.mem_map.mp nodeMember
    simpa only [List.length_map] using powers sample sampleMember
  · intro sample sampleMember different
    apply Polynomial.divide_root noZeroDivisors sample.1 root _
      (Polynomial.fromRoots_vanishes _ _ (List.mem_map.mpr ⟨sample, sampleMember, rfl⟩))
      (Polynomial.fromRoots_vanishes _ _ rootMember)
    exact Ne.symm different

theorem coefficients_unique (noZeroDivisors : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0)
    (samples : List (R × R)) (constant scale : R) (candidate : List R)
    (unique : (samples.map Prod.fst).Nodup) (positive : 0 < samples.length)
    (powers : ∀ sample ∈ samples, sample.1 ^ samples.length = constant)
    (inverts : (samples.length : R) * constant * scale = 1)
    (bounded : candidate.length ≤ samples.length)
    (agrees : ∀ sample ∈ samples, horner sample.1 candidate = sample.2) :
    Polynomial.IsZero (Polynomial.sub candidate (coefficients samples scale)) := by
  apply Polynomial.zero_sub_of_samples noZeroDivisors candidate (coefficients samples scale)
    (samples.map Prod.fst) unique
  · simpa only [List.length_map] using bounded
  · simpa only [List.length_map] using coefficients_length samples scale
  · intro root member
    obtain ⟨sample, sampleMember, rfl⟩ := List.mem_map.mp member
    rw [agrees sample sampleMember]
    exact (coefficients_at_node noZeroDivisors samples constant scale sample.1 sample.2
      unique positive powers inverts sampleMember).symm

theorem coefficients_evaluate (noZeroDivisors : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0)
    (samples : List (R × R)) (constant scale : R) (candidate : List R)
    (unique : (samples.map Prod.fst).Nodup) (positive : 0 < samples.length)
    (powers : ∀ sample ∈ samples, sample.1 ^ samples.length = constant)
    (inverts : (samples.length : R) * constant * scale = 1)
    (bounded : candidate.length ≤ samples.length)
    (agrees : ∀ sample ∈ samples, horner sample.1 candidate = sample.2) (point : R) :
    horner point (coefficients samples scale) = horner point candidate := by
  have zero := Polynomial.horner_zero point (coefficients_unique noZeroDivisors samples constant scale candidate
    unique positive powers inverts bounded agrees)
  rw [Polynomial.horner_sub] at zero
  exact ((LogUp.sub_zero_iff _ _).mp zero).symm

theorem divide_inverse_value (vanishing : List R) (point root inverse : R)
    (vanishes : horner root vanishing = 0) (inverts : (point - root) * inverse = 1) :
    inverse * horner point vanishing = horner point (Polynomial.divide root vanishing) := by
  have factor := Polynomial.divide_factor point root vanishing
  rw [vanishes] at factor
  calc
    inverse * horner point vanishing = inverse * ((point - root) * horner point (Polynomial.divide root vanishing)) := by
      rw [factor]
      grind
    _ = horner point (Polynomial.divide root vanishing) := by grind

open ProofCodec (Extension)

theorem weightedSum_polynomial (vanishing : List Extension) (scale point : Extension)
    (samples : List (Extension × Extension))
    (roots : ∀ sample ∈ samples, horner sample.1 vanishing = 0)
    (away : ∀ sample ∈ samples, point ≠ sample.1) :
    ∃ result, weightedSum scale point samples = some result ∧
      result * horner point vanishing = horner point (combine vanishing scale samples) := by
  induction samples with
  | nil => exact ⟨0, rfl, by change 0 * horner point vanishing = 0; grind⟩
  | cons sample samples ih =>
    have nonzero : point - sample.1 ≠ 0 := fun zero =>
      away sample List.mem_cons_self ((LogUp.sub_zero_iff _ _).mp zero)
    obtain ⟨returned, inverse⟩ := Extension.inverse_correct (point - sample.1) nonzero
    obtain ⟨tail, tailRead, tailValue⟩ := ih
      (fun entry member => roots entry (List.mem_cons_of_mem _ member))
      (fun entry member => away entry (List.mem_cons_of_mem _ member))
    refine ⟨sample.2 * (sample.1 * scale) * (point - sample.1).conjugate.scale (point - sample.1).norm.inverse + tail, ?_, ?_⟩
    · simp only [weightedSum, returned, tailRead, bind, Option.bind_some, pure]
    · have head := divide_inverse_value vanishing point sample.1 _ (roots sample List.mem_cons_self) inverse
      rw [combine, Polynomial.horner_add, Polynomial.horner_scale]
      rw [Semiring.right_distrib, Semiring.mul_assoc, head, tailValue]

theorem evaluate_polynomial (samples : List (Extension × Extension)) (constant scale point : Extension)
    (unique : (samples.map Prod.fst).Nodup) (positive : 0 < samples.length)
    (powers : ∀ sample ∈ samples, sample.1 ^ samples.length = constant)
    (inverts : (samples.length : Extension) * constant * scale = 1) :
    evaluate scale point samples = some (horner point (coefficients samples scale)) := by
  unfold evaluate
  split
  next sample found =>
    have member := List.mem_of_find?_eq_some found
    have test : (point == sample.1) = true :=
      List.find?_some (p := fun entry : Extension × Extension => point == entry.1) found
    have same : point = sample.1 := beq_iff_eq.mp test
    rw [same, coefficients_at_node (fun a b => (Extension.mul_eq_zero_iff a b).mp)
      samples constant scale sample.1 sample.2 unique positive powers inverts member]
  next missing =>
    have away : ∀ sample ∈ samples, point ≠ sample.1 := by
      intro sample member same
      have absent := List.find?_eq_none.mp missing sample member
      simp only [same, beq_self_eq_true] at absent
      contradiction
    obtain ⟨result, returned, correct⟩ := weightedSum_polynomial
      (Polynomial.fromRoots (samples.map Prod.fst)) scale point samples
      (fun sample member => Polynomial.fromRoots_vanishes _ _ (List.mem_map.mpr ⟨sample, member, rfl⟩)) away
    simp only [returned, bind, Option.bind_some, pure]
    rw [Polynomial.horner_fromRoots] at correct
    simpa only [coefficients, List.map_map, Function.comp_def] using congrArg some correct

theorem foldSamples_roots (parent arity : Domain.Subgroup) (index : Nat) (values : List Extension)
    (shape : values.length = Domain.size arity) :
    (foldSamples parent arity index values).map Prod.fst =
      (Polynomial.foldingNodes parent arity index).map Extension.ofBase := by
  apply List.map_fst_zip
  simp only [List.length_map, Polynomial.foldingNodes_length, shape, Nat.le_refl]

theorem foldSamples_length (parent arity : Domain.Subgroup) (index : Nat) (values : List Extension)
    (shape : values.length = Domain.size arity) :
    (foldSamples parent arity index values).length = Domain.size arity := by
  have length := congrArg List.length (foldSamples_roots parent arity index values shape)
  simpa only [List.length_map, Polynomial.foldingNodes_length] using length

theorem foldSamples_nodup (parent arity : Domain.Subgroup) (nested : arity.val ≤ parent.val)
    {index : Nat} (bounded : index < 2^(parent.val - arity.val)) (values : List Extension)
    (shape : values.length = Domain.size arity) : (foldSamples parent arity index values |>.map Prod.fst).Nodup := by
  rw [foldSamples_roots parent arity index values shape, List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (Polynomial.foldingNodes_nodup parent arity nested bounded).imp
    (fun different equal => different (Extension.ofBase_injective equal))

theorem foldSamples_powers (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) (index : Nat) (values : List Extension)
    (shape : values.length = Domain.size arity) : ∀ sample ∈ foldSamples parent arity index values,
    sample.1 ^ (foldSamples parent arity index values).length = Extension.ofBase (FriDomain.queryPoint child index) := by
  intro sample member
  have rootMember : sample.1 ∈ (foldSamples parent arity index values).map Prod.fst :=
    List.mem_map.mpr ⟨sample, member, rfl⟩
  rw [foldSamples_roots parent arity index values shape] at rootMember
  obtain ⟨node, nodeMember, same⟩ := List.mem_map.mp rootMember
  rw [foldSamples_length parent arity index values shape, ← same, ← Extension.ofBase_power,
    Polynomial.foldingNodes_powers parent child arity dimensions index node nodeMember]

theorem foldScale_inverse (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) (index : Nat) :
    (Domain.size arity : Extension) * Extension.ofBase (FriDomain.queryPoint child index) *
      Extension.ofBase (foldScale parent arity index) = 1 := by
  have nonzero : G.ofNat (Domain.size arity) * FriDomain.queryPoint child index ≠ 0 := by
    intro zero
    exact ((G.mul_eq_zero_iff _ _).mp zero).elim
      (G.ofNat_ne_zero_of_lt (Domain.size_positive arity) (Domain.size_lt_characteristic arity))
      (FriDomain.queryPoint_nonzero child index)
  unfold foldScale
  rw [G.pow_eq _ _ (Domain.size_lt_u64 arity), FriDomain.foldNode_power parent child arity dimensions]
  change Extension.ofBase (G.ofNat (Domain.size arity)) * Extension.ofBase (FriDomain.queryPoint child index) *
    Extension.ofBase (G.ofNat (Domain.size arity) * FriDomain.queryPoint child index).inverse = Extension.ofBase 1
  rw [← Extension.ofBase_mul, ← Extension.ofBase_mul, G.mul_inverse_cancel _ nonzero]

theorem foldRow_polynomial (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) {index : Nat}
    (bounded : index < 2^(parent.val - arity.val)) (values : List Extension)
    (shape : values.length = Domain.size arity) (point : Extension) :
    foldRow parent arity index values point = some (horner point
      (coefficients (foldSamples parent arity index values) (Extension.ofBase (foldScale parent arity index)))) := by
  have nested : arity.val ≤ parent.val := by omega
  have length := foldSamples_length parent arity index values shape
  simp only [foldRow, gt_iff_lt, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, _root_.or_assoc,
    if_neg (by omega : ¬(parent.val < arity.val ∨ 2^(parent.val - arity.val) ≤ index ∨ values.length ≠ Domain.size arity))]
  apply evaluate_polynomial _ (Extension.ofBase (FriDomain.queryPoint child index))
  · exact foldSamples_nodup parent arity nested bounded values shape
  · rw [length]; exact Domain.size_positive arity
  · exact foldSamples_powers parent child arity dimensions index values shape
  · rw [length]; exact foldScale_inverse parent child arity dimensions index

theorem foldRow_reject_shape (parent arity : Domain.Subgroup) (index : Nat) (values : List Extension)
    (point : Extension) (malformed : arity.val > parent.val ∨ index ≥ 2^(parent.val - arity.val) ∨ values.length ≠ Domain.size arity) :
    foldRow parent arity index values point = none := by
  simp only [foldRow, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, _root_.or_assoc, if_pos malformed]

theorem foldRow_at_node (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) {index : Nat}
    (bounded : index < 2^(parent.val - arity.val)) (values : List Extension)
    (shape : values.length = Domain.size arity) (root value : Extension)
    (member : (root, value) ∈ foldSamples parent arity index values) :
    foldRow parent arity index values root = some value := by
  rw [foldRow_polynomial parent child arity dimensions bounded values shape]
  congr 1
  apply coefficients_at_node (fun a b => (Extension.mul_eq_zero_iff a b).mp)
    _ (Extension.ofBase (FriDomain.queryPoint child index)) _ root value _ _ _ _ member
  · exact foldSamples_nodup parent arity (by omega) bounded values shape
  · rw [foldSamples_length parent arity index values shape]; exact Domain.size_positive arity
  · exact foldSamples_powers parent child arity dimensions index values shape
  · rw [foldSamples_length parent arity index values shape]; exact foldScale_inverse parent child arity dimensions index

theorem foldRow_evaluate (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) {index : Nat}
    (bounded : index < 2^(parent.val - arity.val)) (values candidate : List Extension)
    (shape : values.length = Domain.size arity) (degree : candidate.length ≤ Domain.size arity)
    (agrees : ∀ sample ∈ foldSamples parent arity index values, horner sample.1 candidate = sample.2)
    (point : Extension) : foldRow parent arity index values point = some (horner point candidate) := by
  rw [foldRow_polynomial parent child arity dimensions bounded values shape]
  congr 1
  apply coefficients_evaluate (fun a b => (Extension.mul_eq_zero_iff a b).mp)
    _ (Extension.ofBase (FriDomain.queryPoint child index)) _ candidate
  · exact foldSamples_nodup parent arity (by omega) bounded values shape
  · rw [foldSamples_length parent arity index values shape]; exact Domain.size_positive arity
  · exact foldSamples_powers parent child arity dimensions index values shape
  · rw [foldSamples_length parent arity index values shape]; exact foldScale_inverse parent child arity dimensions index
  · rwa [foldSamples_length parent arity index values shape]
  · exact agrees

theorem foldRow_success {parent arity : Domain.Subgroup} {index : Nat} {values : List Extension}
    {point result : Extension} (accepted : foldRow parent arity index values point = some result) :
    arity.val ≤ parent.val ∧ index < 2^(parent.val - arity.val) ∧ values.length = Domain.size arity ∧
      ∃ candidate : List Extension, candidate.length ≤ Domain.size arity ∧
        (∀ sample ∈ foldSamples parent arity index values, horner sample.1 candidate = sample.2) ∧
        result = horner point candidate := by
  have wellFormed : ¬(arity.val > parent.val ∨ index ≥ 2^(parent.val - arity.val) ∨ values.length ≠ Domain.size arity) := by
    intro malformed
    rw [foldRow_reject_shape parent arity index values point malformed] at accepted
    cases accepted
  have nested : arity.val ≤ parent.val := by omega
  have bounded : index < 2^(parent.val - arity.val) := by omega
  have shape : values.length = Domain.size arity := by omega
  let child : Domain.Subgroup := ⟨parent.val - arity.val, by have := parent.isLt; omega⟩
  have dimensions : parent.val = child.val + arity.val := by change parent.val = parent.val - arity.val + arity.val; omega
  refine ⟨nested, bounded, shape,
    coefficients (foldSamples parent arity index values) (Extension.ofBase (foldScale parent arity index)), ?_, ?_, ?_⟩
  · have length := coefficients_length (foldSamples parent arity index values) (Extension.ofBase (foldScale parent arity index))
    rwa [foldSamples_length parent arity index values shape] at length
  · intro sample member
    have atNode := foldRow_at_node parent child arity dimensions bounded values shape sample.1 sample.2 member
    rw [foldRow_polynomial parent child arity dimensions bounded values shape] at atNode
    exact Option.some.inj atNode
  · rw [foldRow_polynomial parent child arity dimensions bounded values shape] at accepted
    exact (Option.some.inj accepted).symm

end Aiur.NativeAIR.Interpolation
