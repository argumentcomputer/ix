/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Polynomial
import Ix.Aiur.Proofs.QuotientAlgebra
import Ix.Aiur.Proofs.FriDomain

/-! Coefficient identities and the distinct-root bound used by native
polynomial checks. Ring identities are separate from the no-zero-divisor
condition, which is proved for both native fields below.
-/

namespace Aiur.NativeAIR.Polynomial

open Lean.Grind
open _root_.Aiur.NativeAIR.Quotient (horner horner_nil horner_cons)

section Ring

variable {R : Type} [CommRing R]

theorem isZero_nil : IsZero ([] : List R) := by intro coefficient member; cases member

theorem isZero_iff_all [BEq R] [LawfulBEq R] (coefficients : List R) :
    IsZero coefficients ↔ coefficients.all (· == 0) = true := by
  simp only [IsZero, List.all_eq_true, beq_iff_eq]

theorem isZero_cons (coefficient : R) (rest : List R) :
    IsZero (coefficient :: rest) ↔ coefficient = 0 ∧ IsZero rest := by
  simp only [IsZero, List.mem_cons, forall_eq_or_imp]

theorem isZero_append (left right : List R) : IsZero (left ++ right) ↔ IsZero left ∧ IsZero right := by
  constructor
  · intro zero
    exact ⟨fun value member => zero value (List.mem_append_left _ member),
      fun value member => zero value (List.mem_append_right _ member)⟩
  · rintro ⟨leftZero, rightZero⟩ value member
    exact (List.mem_append.mp member).elim (leftZero value) (rightZero value)

theorem monic_nonzero {coefficients : List R} (monic : Monic coefficients)
    (nontrivial : (1 : R) ≠ 0) : ¬ IsZero coefficients := by
  obtain ⟨initial, rfl⟩ := monic
  intro zero
  exact nontrivial (zero 1 (by simp))

theorem sub_nil (left : List R) : sub left [] = left := by cases left <;> rfl

theorem horner_zero (point : R) {coefficients : List R} (zero : IsZero coefficients) :
    horner point coefficients = 0 := by
  induction coefficients with
  | nil => rfl
  | cons coefficient rest ih =>
    obtain ⟨first, tail⟩ := (isZero_cons _ _).mp zero
    rw [horner_cons, first, ih tail, Semiring.mul_zero, Semiring.add_zero]

theorem add_length (left right : List R) : (add left right).length = max left.length right.length := by
  induction left generalizing right with
  | nil => simp only [add, List.length_nil, Nat.zero_max]
  | cons first left ih =>
    cases right with
    | nil => simp only [add, List.length_nil, Nat.max_zero]
    | cons second right => simp only [add, List.length_cons, ih, Nat.succ_max_succ]

theorem sub_length (left right : List R) : (sub left right).length = max left.length right.length := by
  induction left generalizing right with
  | nil => simp only [sub, List.length_map, List.length_nil, Nat.zero_max]
  | cons first left ih =>
    cases right with
    | nil => simp only [sub, List.length_nil, Nat.max_zero]
    | cons second right => simp only [sub, List.length_cons, ih, Nat.succ_max_succ]

theorem scale_length (scalar : R) (coefficients : List R) :
    (scale scalar coefficients).length = coefficients.length := List.length_map _

theorem sub_append (left right firstTail secondTail : List R) (same : left.length = right.length) :
    sub (left ++ firstTail) (right ++ secondTail) = sub left right ++ sub firstTail secondTail := by
  induction left generalizing right with
  | nil =>
    have empty : right = [] := by simpa using same.symm
    subst right
    rfl
  | cons first left ih =>
    cases right with
    | nil => simp only [List.length_nil, List.length_cons] at same; omega
    | cons second right =>
      have tailSame : left.length = right.length := by simpa only [List.length_cons, Nat.succ.injEq] using same
      simp only [List.cons_append, sub, ih right tailSame]

theorem sub_append_left (left right tail : List R) (bounded : right.length ≤ left.length) :
    sub (left ++ tail) right = sub left right ++ tail := by
  induction left generalizing right with
  | nil =>
    have empty : right = [] := by simpa using bounded
    subst right
    simp only [List.nil_append, sub_nil]
  | cons first left ih =>
    cases right with
    | nil => simp only [sub_nil]
    | cons second right =>
      have tailBound : right.length ≤ left.length := by simp only [List.length_cons] at bounded; omega
      simp only [List.cons_append, sub, ih right tailBound]

theorem horner_add (point : R) (left right : List R) :
    horner point (add left right) = horner point left + horner point right := by
  induction left generalizing right with
  | nil => rw [add, horner_nil]; grind
  | cons first left ih =>
    cases right with
    | nil => change horner point (first :: left) = horner point (first :: left) + 0; grind
    | cons second right => rw [add, horner_cons, ih, horner_cons, horner_cons]; grind

theorem horner_neg (point : R) (coefficients : List R) :
    horner point (coefficients.map (0 - ·)) = 0 - horner point coefficients := by
  induction coefficients with
  | nil => simp only [List.map_nil, horner_nil]; grind
  | cons first rest ih => rw [List.map_cons, horner_cons, ih, horner_cons]; grind

theorem horner_sub (point : R) (left right : List R) :
    horner point (sub left right) = horner point left - horner point right := by
  induction left generalizing right with
  | nil => rw [sub, horner_neg, horner_nil]
  | cons first left ih =>
    cases right with
    | nil => change horner point (first :: left) = horner point (first :: left) - 0; grind
    | cons second right => rw [sub, horner_cons, ih, horner_cons, horner_cons]; grind

theorem horner_scale (point scalar : R) (coefficients : List R) :
    horner point (scale scalar coefficients) = scalar * horner point coefficients := by
  induction coefficients with
  | nil => change 0 = scalar * 0; grind
  | cons first rest ih =>
    change scalar * first + point * horner point (scale scalar rest) = scalar * (first + point * horner point rest)
    rw [ih]
    grind

theorem mulLinear_length (root : R) (coefficients : List R) :
    (mulLinear root coefficients).length = coefficients.length + 1 := by
  rw [mulLinear, sub_length, scale_length, List.length_cons, Nat.max_eq_left (by omega)]

theorem horner_mulLinear (point root : R) (coefficients : List R) :
    horner point (mulLinear root coefficients) = (point - root) * horner point coefficients := by
  rw [mulLinear, horner_sub, horner_cons, horner_scale]
  grind

theorem fromRoots_length (roots : List R) : (fromRoots roots).length = roots.length + 1 := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
    change (mulLinear root (fromRoots roots)).length = (root :: roots).length + 1
    rw [mulLinear_length, ih, List.length_cons]

theorem horner_fromRoots (point : R) (roots : List R) :
    horner point (fromRoots roots) = LogUp.product (roots.map (point - ·)) := by
  induction roots with
  | nil => change 1 + point * 0 = 1; grind
  | cons root roots ih =>
    change horner point (mulLinear root (fromRoots roots)) = _
    rw [horner_mulLinear, ih, List.map_cons, LogUp.product_cons]

theorem mulLinear_monic (root : R) {coefficients : List R} (monic : Monic coefficients) :
    Monic (mulLinear root coefficients) := by
  obtain ⟨initial, rfl⟩ := monic
  refine ⟨sub (0 :: initial) (scale root (initial ++ [1])), ?_⟩
  rw [mulLinear, ← List.cons_append, sub_append_left]
  simp only [scale_length, List.length_append, List.length_cons, List.length_nil]
  omega

theorem fromRoots_monic (roots : List R) : Monic (fromRoots roots) := by
  induction roots with
  | nil => exact ⟨[], rfl⟩
  | cons root roots ih => exact mulLinear_monic root ih

theorem fromRoots_nonzero (roots : List R) (nontrivial : (1 : R) ≠ 0) : ¬ IsZero (fromRoots roots) :=
  monic_nonzero (fromRoots_monic roots) nontrivial

theorem fromRoots_vanishes (roots : List R) (point : R) (member : point ∈ roots) :
    horner point (fromRoots roots) = 0 := by
  induction roots with
  | nil => cases member
  | cons root roots ih =>
    change horner point (mulLinear root (fromRoots roots)) = 0
    rw [horner_mulLinear]
    rcases List.mem_cons.mp member with same | later
    · rw [same]; grind
    · rw [ih later, Semiring.mul_zero]

theorem powerMinus_length (degree : Nat) (constant : R) :
    (powerMinus degree constant).length = degree + 1 := by
  rw [powerMinus, sub_length]
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

theorem powerMinus_monic {degree : Nat} (positive : 0 < degree) (constant : R) :
    Monic (powerMinus degree constant) := by
  refine ⟨sub (List.replicate degree 0) [constant], ?_⟩
  rw [powerMinus, sub_append_left]
  simp only [List.length_cons, List.length_nil, List.length_replicate]
  omega

theorem horner_replicate_zero (point : R) (count : Nat) : horner point (List.replicate count 0) = 0 :=
  horner_zero point (by intro value member; exact List.mem_replicate.mp member |>.2)

theorem horner_powerMinus (point constant : R) (degree : Nat) :
    horner point (powerMinus degree constant) = point ^ degree - constant := by
  rw [powerMinus, horner_sub, Quotient.horner_append, horner_replicate_zero, List.length_replicate]
  simp only [horner_cons, horner_nil]
  grind

theorem divide_length (point : R) (coefficients : List R) :
    (divide point coefficients).length = coefficients.length - 1 := by
  induction coefficients using divide.induct with
  | case1 => rfl
  | case2 first => rfl
  | case3 first next rest ih =>
    simp only [divide, List.length_cons, ih]
    omega

theorem divide_factor (point root : R) (coefficients : List R) :
    horner point coefficients = horner root coefficients + (point - root) * horner point (divide root coefficients) := by
  induction coefficients using divide.induct with
  | case1 => simp only [divide, horner_nil]; grind
  | case2 first => simp only [divide, horner_cons, horner_nil]; grind
  | case3 first next rest ih =>
    change first + point * horner point (next :: rest) =
      first + root * horner root (next :: rest) + (point - root) *
        (horner root (next :: rest) + point * horner point (divide root (next :: rest)))
    grind

theorem zero_of_divide_zero (root : R) (coefficients : List R)
    (vanishes : horner root coefficients = 0) (zero : IsZero (divide root coefficients)) : IsZero coefficients := by
  induction coefficients using divide.induct with
  | case1 => exact isZero_nil
  | case2 first =>
    apply (isZero_cons _ _).mpr
    constructor
    · simpa only [horner_cons, horner_nil, Semiring.mul_zero, Semiring.add_zero] using vanishes
    · exact isZero_nil
  | case3 first next rest ih =>
    obtain ⟨nextZero, tailZero⟩ := (isZero_cons _ _).mp zero
    have tail := ih nextZero tailZero
    apply (isZero_cons _ _).mpr
    constructor
    · simpa only [horner_cons, nextZero, Semiring.mul_zero, Semiring.add_zero] using vanishes
    · exact tail

theorem divide_nonzero (root : R) {coefficients : List R}
    (nonzero : ¬ IsZero coefficients) (vanishes : horner root coefficients = 0) :
    ¬ IsZero (divide root coefficients) := fun zero => nonzero (zero_of_divide_zero root coefficients vanishes zero)

end Ring

section Domain

variable {R : Type} [CommRing R]
variable (noZeroDivisors : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0)
include noZeroDivisors

theorem divide_root (root point : R) (coefficients : List R)
    (atRoot : horner root coefficients = 0) (atPoint : horner point coefficients = 0)
    (different : point ≠ root) : horner point (divide root coefficients) = 0 := by
  have factor := divide_factor point root coefficients
  rw [atRoot, atPoint] at factor
  have productZero : (point - root) * horner point (divide root coefficients) = 0 := by grind
  exact (noZeroDivisors _ _ productZero).resolve_left
    (fun zero => different ((LogUp.sub_zero_iff _ _).mp zero))

theorem roots_lt_length (coefficients roots : List R) (nonzero : ¬ IsZero coefficients)
    (unique : roots.Nodup) (vanishes : ∀ point ∈ roots, horner point coefficients = 0) :
    roots.length < coefficients.length := by
  suffices bounded : ∀ fuel (coefficients roots : List R), coefficients.length ≤ fuel →
      ¬ IsZero coefficients → roots.Nodup →
      (∀ point ∈ roots, horner point coefficients = 0) → roots.length < coefficients.length from
    bounded coefficients.length coefficients roots (by omega) nonzero unique vanishes
  intro fuel
  induction fuel with
  | zero =>
    intro coefficients roots lengthBound nonzero unique vanishes
    cases coefficients with
    | nil => exact False.elim (nonzero isZero_nil)
    | cons first rest => simp only [List.length_cons] at lengthBound; omega
  | succ fuel ih =>
    intro coefficients roots lengthBound nonzero unique vanishes
    cases roots with
    | nil =>
      cases coefficients with
      | nil => exact False.elim (nonzero isZero_nil)
      | cons first rest => exact Nat.zero_lt_succ _
    | cons root roots =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      have atRoot := vanishes root (by simp)
      have quotientNonzero := divide_nonzero root nonzero atRoot
      have quotientBound : (divide root coefficients).length ≤ fuel := by rw [divide_length]; omega
      have tailZero : ∀ point ∈ roots, horner point (divide root coefficients) = 0 := by
        intro point member
        apply divide_root noZeroDivisors root point coefficients atRoot (vanishes point (by simp [member]))
        intro equal
        exact absent (equal ▸ member)
      have shorter := ih (divide root coefficients) roots quotientBound quotientNonzero tailUnique tailZero
      rw [divide_length] at shorter
      simp only [List.length_cons]
      omega

theorem roots_le_degree (coefficients roots : List R) (nonzero : ¬ IsZero coefficients)
    (unique : roots.Nodup) (vanishes : ∀ point ∈ roots, horner point coefficients = 0) :
    roots.length ≤ coefficients.length - 1 := by
  have := roots_lt_length noZeroDivisors coefficients roots nonzero unique vanishes
  omega

theorem zero_of_roots (coefficients roots : List R) (unique : roots.Nodup)
    (enough : coefficients.length ≤ roots.length)
    (vanishes : ∀ point ∈ roots, horner point coefficients = 0) : IsZero coefficients := by
  apply Classical.byContradiction
  intro nonzero
  have := roots_lt_length noZeroDivisors coefficients roots nonzero unique vanishes
  omega

theorem zero_sub_of_samples (left right samples : List R) (unique : samples.Nodup)
    (leftBound : left.length ≤ samples.length) (rightBound : right.length ≤ samples.length)
    (equal : ∀ point ∈ samples, horner point left = horner point right) : IsZero (sub left right) := by
  apply zero_of_roots noZeroDivisors (sub left right) samples unique
  · rw [sub_length]
    exact Nat.max_le.mpr ⟨leftBound, rightBound⟩
  · intro point member
    rw [horner_sub, equal point member]
    grind

theorem equal_of_samples (left right samples : List R) (unique : samples.Nodup)
    (leftBound : left.length ≤ samples.length) (rightBound : right.length ≤ samples.length)
    (equal : ∀ point ∈ samples, horner point left = horner point right) (point : R) :
    horner point left = horner point right := by
  have zero := horner_zero point (zero_sub_of_samples noZeroDivisors left right samples unique leftBound rightBound equal)
  rw [horner_sub] at zero
  exact (LogUp.sub_zero_iff _ _).mp zero

theorem monic_zero_sub_of_samples (left right samples : List R)
    (leftMonic : Monic left) (rightMonic : Monic right) (unique : samples.Nodup)
    (sameLength : left.length = right.length) (enough : left.length ≤ samples.length + 1)
    (equal : ∀ point ∈ samples, horner point left = horner point right) : IsZero (sub left right) := by
  obtain ⟨leftPrefix, rfl⟩ := leftMonic
  obtain ⟨rightPrefix, rfl⟩ := rightMonic
  have same : leftPrefix.length = rightPrefix.length := by
    simp only [List.length_append, List.length_cons, List.length_nil] at sameLength
    omega
  have tail : sub ([1] : List R) [1] = [0] := by simp only [sub]; congr 1; grind
  rw [sub_append _ _ _ _ same, tail, isZero_append]
  refine ⟨?_, (isZero_cons _ _).mpr ⟨rfl, isZero_nil⟩⟩
  apply zero_of_roots noZeroDivisors (sub leftPrefix rightPrefix) samples unique
  · rw [sub_length, same, Nat.max_self]
    simp only [List.length_append, List.length_cons, List.length_nil] at enough
    omega
  · intro point member
    have atPoint := equal point member
    simp only [Quotient.horner_append, horner_cons, horner_nil, same] at atPoint
    rw [horner_sub]
    grind

theorem monic_equal_of_samples (left right samples : List R)
    (leftMonic : Monic left) (rightMonic : Monic right) (unique : samples.Nodup)
    (sameLength : left.length = right.length) (enough : left.length ≤ samples.length + 1)
    (equal : ∀ point ∈ samples, horner point left = horner point right) (point : R) :
    horner point left = horner point right := by
  have zero := horner_zero point
    (monic_zero_sub_of_samples noZeroDivisors left right samples leftMonic rightMonic unique sameLength enough equal)
  rw [horner_sub] at zero
  exact (LogUp.sub_zero_iff _ _).mp zero

theorem root_product_identity (roots : List R) (constant : R) (unique : roots.Nodup)
    (positive : 0 < roots.length) (powers : ∀ root ∈ roots, root ^ roots.length = constant) (point : R) :
    LogUp.product (roots.map (point - ·)) = point ^ roots.length - constant := by
  rw [← horner_fromRoots, ← horner_powerMinus]
  apply monic_equal_of_samples noZeroDivisors (fromRoots roots) (powerMinus roots.length constant) roots
    (fromRoots_monic roots) (powerMinus_monic positive constant) unique
  · rw [fromRoots_length, powerMinus_length]
  · rw [fromRoots_length]
    omega
  · intro root member
    rw [fromRoots_vanishes roots root member, horner_powerMinus, powers root member]
    grind

theorem root_count_le [BEq R] [LawfulBEq R] (coefficients samples : List R)
    (nonzero : ¬ IsZero coefficients) (unique : samples.Nodup) :
    (samples.filter (fun point => horner point coefficients == 0)).length ≤ coefficients.length - 1 := by
  apply roots_le_degree noZeroDivisors coefficients _ nonzero (unique.filter _)
  intro point member
  exact beq_iff_eq.mp (List.mem_filter.mp member).2

theorem equal_count_le [BEq R] [LawfulBEq R] (left right samples : List R)
    (different : ¬ IsZero (sub left right)) (unique : samples.Nodup) :
    (samples.filter (fun point => horner point left == horner point right)).length ≤
      max left.length right.length - 1 := by
  rw [← sub_length]
  apply roots_le_degree noZeroDivisors (sub left right) _ different (unique.filter _)
  intro point member
  rw [horner_sub, beq_iff_eq.mp (List.mem_filter.mp member).2]
  grind

end Domain

theorem base_roots_lt_length (coefficients roots : List G) (nonzero : ¬ IsZero coefficients)
    (unique : roots.Nodup) (vanishes : ∀ point ∈ roots, horner point coefficients = 0) :
    roots.length < coefficients.length :=
  roots_lt_length (fun a b => (G.mul_eq_zero_iff a b).mp) coefficients roots nonzero unique vanishes

theorem extension_roots_lt_length (coefficients roots : List ProofCodec.Extension)
    (nonzero : ¬ IsZero coefficients) (unique : roots.Nodup)
    (vanishes : ∀ point ∈ roots, horner point coefficients = 0) : roots.length < coefficients.length :=
  roots_lt_length (fun a b => (ProofCodec.Extension.mul_eq_zero_iff a b).mp) coefficients roots nonzero unique vanishes

theorem base_root_count_le (coefficients samples : List G)
    (nonzero : ¬ IsZero coefficients) (unique : samples.Nodup) :
    (samples.filter (fun point => horner point coefficients == 0)).length ≤ coefficients.length - 1 :=
  root_count_le (fun a b => (G.mul_eq_zero_iff a b).mp) coefficients samples nonzero unique

theorem extension_root_count_le (coefficients samples : List ProofCodec.Extension)
    (nonzero : ¬ IsZero coefficients) (unique : samples.Nodup) :
    (samples.filter (fun point => horner point coefficients == 0)).length ≤ coefficients.length - 1 :=
  root_count_le (fun a b => (ProofCodec.Extension.mul_eq_zero_iff a b).mp) coefficients samples nonzero unique

theorem foldingNodes_length (parent arity : Domain.Subgroup) (index : Nat) :
    (foldingNodes parent arity index).length = Domain.size arity := by
  simp only [foldingNodes, List.length_map, List.length_range]

theorem foldingNodes_nodup (parent arity : Domain.Subgroup) (nested : arity.val ≤ parent.val)
    {index : Nat} (bounded : index < 2^(parent.val - arity.val)) :
    (foldingNodes parent arity index).Nodup := by
  unfold foldingNodes
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  apply List.Pairwise.imp_of_mem (R := fun left right : Nat => left ≠ right) _ List.nodup_range
  intro left right leftMem rightMem different equal
  exact different (FriDomain.foldNode_injective parent arity nested bounded
    (List.mem_range.mp leftMem) (List.mem_range.mp rightMem) equal)

theorem foldingNodes_powers (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) (index : Nat) :
    ∀ node ∈ foldingNodes parent arity index, node ^ Domain.size arity = FriDomain.queryPoint child index := by
  intro node member
  obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
  exact FriDomain.foldNode_power parent child arity dimensions index slot

theorem folding_product_identity (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) {index : Nat}
    (bounded : index < 2^(parent.val - arity.val)) (point : ProofCodec.Extension) :
    LogUp.product ((foldingNodes parent arity index).map (fun node => point - ProofCodec.Extension.ofBase node)) =
      point ^ Domain.size arity - ProofCodec.Extension.ofBase (FriDomain.queryPoint child index) := by
  let roots := (foldingNodes parent arity index).map ProofCodec.Extension.ofBase
  have length : roots.length = Domain.size arity := by simp only [roots, List.length_map, foldingNodes_length]
  have unique : roots.Nodup := by
    rw [show roots = (foldingNodes parent arity index).map ProofCodec.Extension.ofBase from rfl,
      List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact (foldingNodes_nodup parent arity (by omega) bounded).imp
      (fun different equal => different (ProofCodec.Extension.ofBase_injective equal))
  have powers : ∀ root ∈ roots, root ^ roots.length = ProofCodec.Extension.ofBase (FriDomain.queryPoint child index) := by
    intro root member
    change root ∈ (foldingNodes parent arity index).map ProofCodec.Extension.ofBase at member
    obtain ⟨node, nodeMember, rfl⟩ := List.mem_map.mp member
    rw [length, ← ProofCodec.Extension.ofBase_power, foldingNodes_powers parent child arity dimensions index node nodeMember]
  have result := root_product_identity (fun a b => (ProofCodec.Extension.mul_eq_zero_iff a b).mp)
    roots _ unique (by rw [length]; exact Domain.size_positive arity) powers point
  simpa only [roots, List.map_map, Function.comp_def, length] using result

end Aiur.NativeAIR.Polynomial
