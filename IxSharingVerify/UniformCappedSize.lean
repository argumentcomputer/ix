import IxC.Kernel.Audit.Axioms
import IxSharingVerify.UniformClasses

/-! Arithmetic contract of Rust's classification-only empty-cost cap.
The cap covers every public UInt64 width. It is not used for general phi,
gains, signed deltas or wire lengths. The sum/empty-telescope lemmas justify
the no-cut capped recurrence; native Rust correspondence is separately
checked against an arbitrary-precision reference. -/

namespace Ix.Sharing.Verify.CappedSize

abbrev Excluded (occ size width : Nat) : Prop := (occ - 1) * size < occ * width

theorem excluded_div {occ size width : Nat} (positive : 0 < occ) (larger : width < size) :
    Excluded occ size width ↔ occ ≤ (size - 1) / (size - width) := by
  have left : (occ - 1) * size + size = occ * size := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  have right : occ * size = occ * (size - width) + occ * width := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt larger)]
  rw [Nat.le_div_iff_mul_le (by omega)]
  unfold Excluded
  omega

/-- Product-free comparison, including occurrence zero and width zero. -/
theorem excluded_fast (occ size width : Nat) :
    Excluded occ size width ↔ occ ≠ 0 ∧ width ≠ 0 ∧
      (size ≤ width ∨ occ ≤ (size - 1) / (size - width)) := by
  by_cases zero : occ = 0
  · simp [Excluded, zero]
  by_cases noWidth : width = 0
  · simp [Excluded, noWidth]
  by_cases small : size ≤ width
  · have scaled := Nat.mul_le_mul_left (occ - 1) small
    have split : occ * width = (occ - 1) * width + width := by
      rw [← Nat.succ_mul]
      congr 1
      omega
    have yes : Excluded occ size width := by unfold Excluded; omega
    simp only [ne_eq, zero, noWidth, not_false_eq_true, small, true_or, and_self, yes]
  · rw [excluded_div (by omega) (by omega)]
    simp only [ne_eq, zero, noWidth, not_false_eq_true, small, false_or, true_and]

theorem excluded_size_lt_two {occ size width : Nat} (repeated : 2 ≤ occ)
    (excluded : Excluded occ size width) : size < 2 * width := by
  apply Classical.byContradiction
  intro large
  have doubled : occ ≤ (occ - 1) * 2 := by omega
  have first := Nat.mul_le_mul_right width doubled
  have second := Nat.mul_le_mul_left (occ - 1) (show 2 * width ≤ size by omega)
  rw [Nat.mul_assoc] at first
  exact Nat.not_lt_of_ge (Nat.le_trans first second) excluded

/-- Large empty costs need not be represented exactly for exclusion. -/
theorem cap_size (occ size width bound : Nat) (covers : 2 * width ≤ bound) :
    Excluded occ (min size bound) width ↔ Excluded occ size width := by
  by_cases fits : size ≤ bound
  · rw [Nat.min_eq_left fits]
  rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge fits))]
  by_cases zero : occ = 0
  · simp [Excluded, zero]
  by_cases once : occ = 1
  · simp [Excluded, once]
  have repeated : 2 ≤ occ := by omega
  have left : ¬ Excluded occ bound width := by
    intro yes
    have := excluded_size_lt_two repeated yes
    omega
  have right : ¬ Excluded occ size width := by
    intro yes
    have := excluded_size_lt_two repeated yes
    omega
  simp only [left, right]

/-- Saturated occurrence counts preserve the same predicate when the
represented size is below the saturation threshold. -/
theorem cap_occ (occ size width bound : Nat) (above : size < bound) :
    Excluded (min occ bound) size width ↔ Excluded occ size width := by
  by_cases fits : occ ≤ bound
  · rw [Nat.min_eq_left fits]
  rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge fits)),
    excluded_fast, excluded_fast]
  have positive : bound ≠ 0 := by omega
  have occPositive : occ ≠ 0 := by omega
  have quotient := Nat.div_le_self (size - 1) (size - width)
  have boundLarge : ¬ bound ≤ (size - 1) / (size - width) := by omega
  have occLarge : ¬ occ ≤ (size - 1) / (size - width) := by omega
  simp only [ne_eq, positive, occPositive, not_false_eq_true, boundLarge, occLarge,
    or_false, true_and]

def maxWidth : Nat := 2 ^ 64 - 1
def emptyCap : Nat := 2 * maxWidth
def occurrenceCap : Nat := 2 ^ 128 - 1

/-- Every public u64 width is covered, including zero; occurrence saturation
and empty-size capping together preserve the uncapped natural predicate. -/
theorem classification_capped (occ size width : Nat) (publicWidth : width ≤ maxWidth) :
    Excluded (min occ occurrenceCap) (min size emptyCap) width ↔ Excluded occ size width := by
  have gap : emptyCap < occurrenceCap := by decide
  have above : min size emptyCap < occurrenceCap := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) gap
  exact (cap_occ occ (min size emptyCap) width occurrenceCap above).trans
    (cap_size occ size width emptyCap (Nat.mul_le_mul_left 2 publicWidth))

/-- The capped additions use inputs at most 2^65-2; even their sum fits
u128, so native addition needs no overflowing intermediate. -/
theorem cap_add_u128_safe (a b : Nat) : min a emptyCap + min b emptyCap < 2 ^ 128 := by
  have bound : 2 * emptyCap < 2 ^ 128 := by decide
  have ha := Nat.min_le_right a emptyCap
  have hb := Nat.min_le_right b emptyCap
  omega

theorem cap_add (bound a b : Nat) :
    min (min a bound + min b bound) bound = min (a + b) bound := by omega

/-- Own-payload vectors and non-telescope children are folds of capped sums.
Every scalar/vector element participates; no u64 Len sentinel is substituted. -/
theorem cap_fold (bound : Nat) (xs : List Nat) (start : Nat) :
    xs.foldl (fun acc x => min (acc + min x bound) bound) (min start bound) =
      min (start + xs.sum) bound := by
  induction xs generalizing start with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, cap_add, ih]
    simp only [List.sum_cons, Nat.add_assoc]

/-- Empty telescope evaluation has only side sums and a natural tail;
there is no available cut and therefore no subtraction of capped values. -/
theorem cap_empty_telescope (bound header extra side previous tail : Nat) :
    min (min (min header bound +
        min (min (min extra bound + min side bound) bound + min previous bound) bound) bound +
      min tail bound) bound = min (header + (extra + side + previous) + tail) bound := by
  rw [cap_add bound extra side, cap_add bound (extra + side) previous,
    cap_add bound header (extra + side + previous), cap_add]

/-- The actual empty Lean evaluator has no available telescope cut. -/
theorem empty_no_cuts (p : Ix.Sharing.Exact.Prep) (width : Nat) (value : Nat → Nat) (term : Nat) :
    Ix.Sharing.Verify.UniformModel.cutCosts p width (fun _ => false) value term = [] := by
  simp [Ix.Sharing.Verify.UniformModel.cutCosts]

theorem empty_telescope_natural (p : Ix.Sharing.Exact.Prep) (width : Nat) (value : Nat → Nat)
    (term : Nat) (tele : p.family[term]! ≠ .none) :
    Ix.Sharing.Verify.UniformModel.inlOf p width (fun _ => false) value term =
      Ix.Sharing.Verify.UniformModel.naturalCost p value term := by
  rw [Ix.Sharing.Verify.UniformModel.inl_tele width _ _ tele, empty_no_cuts]
  rfl

/-- Link the arithmetic contract to the actual Lean classifier definition. -/
theorem certainExcludedTest_contract (p : Ix.Sharing.Exact.Prep)
    (f : Ix.Sharing.Exact.GraphFacts) (width term : Nat) :
    Ix.Sharing.Exact.certainExcludedTest p f width term =
      decide (Excluded f.occ[term]! p.base[term]! width) := rfl

end Ix.Sharing.Verify.CappedSize

#guard_kernel_axioms Ix.Sharing.Verify.CappedSize.excluded_div [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CappedSize.excluded_fast [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CappedSize.excluded_size_lt_two [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CappedSize.cap_size [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CappedSize.cap_occ [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CappedSize.classification_capped [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CappedSize.cap_add_u128_safe [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CappedSize.cap_add [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CappedSize.cap_fold [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CappedSize.cap_empty_telescope [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CappedSize.empty_no_cuts [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CappedSize.empty_telescope_natural [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CappedSize.certainExcludedTest_contract []
