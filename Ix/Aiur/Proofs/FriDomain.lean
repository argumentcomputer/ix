/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.FriDomain
import Ix.Aiur.Proofs.Domain

/-! The bit-reversal permutation, nested two-adic generators, and the
field points used by FRI input openings, row folding and final evaluation.
-/

namespace Aiur.NativeAIR.FriDomain

open Lean.Grind

theorem reverseBits_bound (bits index : Nat) : reverseBits bits index < 2^bits :=
  (BitVec.ofNat bits index).reverse.isLt

theorem reverseBits_zero (bits : Nat) : reverseBits bits 0 = 0 := by
  unfold reverseBits
  rw [show BitVec.ofNat bits 0 = 0#bits from rfl,
    (BitVec.reverse_eq_zero_iff).mpr rfl]
  rfl

theorem reverseBits_zero_width (index : Nat) : reverseBits 0 index = 0 := by
  have := reverseBits_bound 0 index
  simp only [Nat.pow_zero] at this
  omega

theorem reverseBits_mod (bits index : Nat) :
    reverseBits bits (index % 2^bits) = reverseBits bits index := by
  unfold reverseBits
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp

theorem reverseBits_involution (bits index : Nat) :
    reverseBits bits (reverseBits bits index) = index % 2^bits := by
  simp only [reverseBits, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.reverse_reverse_eq, BitVec.toNat_ofNat]

theorem reverseBits_injective {bits left right : Nat}
    (leftBound : left < 2^bits) (rightBound : right < 2^bits)
    (equal : reverseBits bits left = reverseBits bits right) : left = right := by
  have same := congrArg (reverseBits bits) equal
  simpa only [reverseBits_involution, Nat.mod_eq_of_lt leftBound,
    Nat.mod_eq_of_lt rightBound] using same

theorem reverseBits_surjective {bits index : Nat} (bounded : index < 2^bits) :
    ∃ original < 2^bits, reverseBits bits original = index :=
  ⟨reverseBits bits index, reverseBits_bound _ _,
    (reverseBits_involution _ _).trans (Nat.mod_eq_of_lt bounded)⟩

theorem index_split_bound {low high index : Nat} (bounded : index < 2^(high + low)) :
    index / 2^low < 2^high := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
  simpa only [Nat.pow_add] using bounded

theorem reverseBits_split {high low index : Nat} (bounded : index < 2^(high + low)) :
    reverseBits (high + low) index =
      reverseBits low (index % 2^low) * 2^high + reverseBits high (index / 2^low) := by
  have decomposition : BitVec.ofNat (high + low) index =
      BitVec.ofNat high (index / 2^low) ++ BitVec.ofNat low index := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded, BitVec.toNat_append,
      Nat.mod_eq_of_lt (index_split_bound bounded)]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.shiftLeft_eq]
    have := Nat.mod_add_div index (2^low)
    rw [Nat.mul_comm] at this
    omega
  unfold reverseBits
  rw [decomposition, BitVec.reverse_append, BitVec.toNat_cast, BitVec.toNat_append]
  rw [show BitVec.ofNat low (index % 2^low) = BitVec.ofNat low index by
    apply BitVec.eq_of_toNat_eq; simp]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), Nat.shiftLeft_eq]

theorem reverseBits_padding {bits index : Nat} (bounded : index < 2^bits) (extra : Nat) :
    reverseBits (extra + bits) index = reverseBits bits index * 2^extra := by
  have bound : index < 2^(extra + bits) := Nat.lt_of_lt_of_le bounded
    (Nat.pow_le_pow_right (by decide) (by omega))
  rw [reverseBits_split bound, Nat.mod_eq_of_lt bounded, Nat.div_eq_of_lt bounded,
    reverseBits_zero, Nat.add_zero]

theorem wordReverse_eq {wordBits bits index : Nat}
    (supported : bits ≤ wordBits) (bounded : index < 2^bits) :
    wordReverse wordBits bits index = reverseBits bits index := by
  by_cases empty : bits = 0
  · subst bits
    have zero : index = 0 := by simpa using bounded
    subst index
    simp only [wordReverse, Nat.sub_zero, Nat.mod_self,
      reverseBits_zero, BitVec.toNat_ushiftRight, Nat.shiftRight_zero]
    exact reverseBits_zero wordBits
  · have shiftBound : wordBits - bits < wordBits := by omega
    unfold wordReverse
    rw [Nat.mod_eq_of_lt shiftBound, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    change reverseBits wordBits index / 2^(wordBits - bits) = reverseBits bits index
    conv => lhs; arg 1; rw [← Nat.sub_add_cancel supported]
    rw [reverseBits_padding bounded, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem generator_nested (parent child : Domain.Subgroup) (nested : child.val ≤ parent.val) :
    Domain.generator parent ^ (2^(parent.val - child.val)) = Domain.generator child := by
  have step : ∀ (extra bits : Nat) (bounded : bits + extra < 33),
      Domain.generator ⟨bits + extra, bounded⟩ ^ (2^extra) =
        Domain.generator ⟨bits, by omega⟩ := by
    intro extra
    induction extra with
    | zero => intro bits bounded; simp only [Nat.add_zero, Nat.pow_zero, Semiring.pow_one]
    | succ extra ih =>
      intro bits bounded
      have square := Domain.generator_square_certificate ⟨bits + extra, by omega⟩
      have powerSquare : Domain.generator ⟨bits + (extra + 1), bounded⟩ ^ 2 =
          Domain.generator ⟨bits + extra, by omega⟩ := by
        simpa only [Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul, Nat.add_assoc] using square
      rw [Nat.pow_succ, Nat.mul_comm, Domain.Algebra.power_mul, powerSquare]
      exact ih bits (by omega)
  have result := step (parent.val - child.val) child.val (by have := parent.isLt; omega)
  simpa only [Nat.add_sub_of_le nested] using result

theorem queryPoint_eq (domain : Domain.Subgroup) (index : Nat) :
    queryPoint domain index = Domain.generator domain ^ reverseBits domain.val index := by
  exact G.pow_eq _ _ (Nat.lt_trans (reverseBits_bound _ _) (Domain.size_lt_u64 domain))

theorem queryPoint_domain (domain : Domain.Subgroup) (index : Nat) :
    queryPoint domain index = Domain.point domain ⟨reverseBits domain.val index, reverseBits_bound _ _⟩ := rfl

theorem queryPoint_injective (domain : Domain.Subgroup) {left right : Nat}
    (leftBound : left < Domain.size domain) (rightBound : right < Domain.size domain)
    (equal : queryPoint domain left = queryPoint domain right) : left = right := by
  have same := congrArg Fin.val (Domain.point_injective domain equal)
  exact reverseBits_injective leftBound rightBound same

theorem queryPoint_surjective (domain : Domain.Subgroup) (index : Fin (Domain.size domain)) :
    ∃ query < Domain.size domain, queryPoint domain query = Domain.point domain index := by
  obtain ⟨query, bound, reversed⟩ := reverseBits_surjective index.isLt
  refine ⟨query, bound, ?_⟩
  rw [queryPoint_domain]
  congr 1
  exact Fin.ext reversed

theorem queryPoint_nonzero (domain : Domain.Subgroup) (index : Nat) :
    queryPoint domain index ≠ 0 := Domain.point_nonzero _ _

theorem queryPoint_power (domain : Domain.Subgroup) (index : Nat) :
    queryPoint domain index ^ Domain.size domain = 1 := Domain.point_power _ _

theorem queryPoint_zero (domain : Domain.Subgroup) : queryPoint domain 0 = 1 := by
  rw [queryPoint_eq, reverseBits_zero, Semiring.pow_zero]

theorem queryPoint_padding (parent child : Domain.Subgroup) (nested : child.val ≤ parent.val)
    {index : Nat} (bounded : index < Domain.size child) :
    queryPoint parent index = queryPoint child index := by
  rw [queryPoint_eq, queryPoint_eq]
  conv => lhs; arg 2; arg 1; rw [← Nat.sub_add_cancel nested]
  rw [reverseBits_padding bounded, Nat.mul_comm, Domain.Algebra.power_mul, generator_nested _ _ nested]

theorem index_join_bound {high low index slot : Nat}
    (indexBound : index < 2^high) (slotBound : slot < 2^low) :
    index * 2^low + slot < 2^(high + low) := by
  have bound := Nat.mul_le_mul_right (2^low) (Nat.succ_le_of_lt indexBound)
  rw [Nat.succ_mul, ← Nat.pow_add] at bound
  omega

theorem reverseBits_join {high low index slot : Nat}
    (indexBound : index < 2^high) (slotBound : slot < 2^low) :
    reverseBits (high + low) (index * 2^low + slot) =
      reverseBits low slot * 2^high + reverseBits high index := by
  rw [reverseBits_split (index_join_bound indexBound slotBound), Nat.mul_comm index,
    Nat.mul_add_mod, Nat.mod_eq_of_lt slotBound,
    Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt slotBound, Nat.add_zero]

theorem foldNode_eq (parent arity : Domain.Subgroup) (nested : arity.val ≤ parent.val)
    {index slot : Nat} (indexBound : index < 2^(parent.val - arity.val))
    (slotBound : slot < Domain.size arity) :
    foldNode parent arity index slot = queryPoint parent (index * Domain.size arity + slot) := by
  have firstBound : reverseBits (parent.val - arity.val) index < 2^64 :=
    Nat.lt_of_lt_of_le (reverseBits_bound _ _)
      (Nat.pow_le_pow_right (by decide) (by have := parent.isLt; omega))
  rw [foldNode, G.pow_eq _ _ firstBound,
    G.pow_eq _ _ (Nat.lt_trans (reverseBits_bound _ _) (Domain.size_lt_u64 arity)), queryPoint_eq]
  change _ = Domain.generator parent ^
    reverseBits parent.val (index * 2^arity.val + slot)
  conv => rhs; arg 2; arg 1; rw [← Nat.sub_add_cancel nested]
  rw [reverseBits_join indexBound slotBound, Semiring.pow_add,
    Nat.mul_comm, Domain.Algebra.power_mul, generator_nested _ _ nested]
  exact G.mul_comm _ _

theorem foldNode_injective (parent arity : Domain.Subgroup) (nested : arity.val ≤ parent.val)
    {index left right : Nat} (indexBound : index < 2^(parent.val - arity.val))
    (leftBound : left < Domain.size arity) (rightBound : right < Domain.size arity)
    (equal : foldNode parent arity index left = foldNode parent arity index right) : left = right := by
  rw [foldNode_eq _ _ nested indexBound leftBound,
    foldNode_eq _ _ nested indexBound rightBound] at equal
  have boundLeft := index_join_bound indexBound leftBound
  have boundRight := index_join_bound indexBound rightBound
  rw [Nat.sub_add_cancel nested] at boundLeft boundRight
  have same := queryPoint_injective parent boundLeft boundRight equal
  omega

theorem foldNode_nonzero (parent arity : Domain.Subgroup) (nested : arity.val ≤ parent.val)
    {index slot : Nat} (indexBound : index < 2^(parent.val - arity.val))
    (slotBound : slot < Domain.size arity) : foldNode parent arity index slot ≠ 0 := by
  rw [foldNode_eq _ _ nested indexBound slotBound]
  exact queryPoint_nonzero _ _

theorem foldNode_power (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) (index slot : Nat) :
    foldNode parent arity index slot ^ Domain.size arity = queryPoint child index := by
  have nested : child.val ≤ parent.val := by omega
  have height : parent.val - arity.val = child.val := by omega
  have power : 2^(parent.val - child.val) = Domain.size arity := by
    unfold Domain.size
    congr 1
    omega
  unfold foldNode
  rw [height, G.pow_eq _ _ (Nat.lt_trans (reverseBits_bound _ _) (Domain.size_lt_u64 child)),
    G.pow_eq _ _ (Nat.lt_trans (reverseBits_bound _ _) (Domain.size_lt_u64 arity)),
    CommSemiring.mul_pow]
  have right : (Domain.generator arity ^ reverseBits arity.val slot) ^ Domain.size arity = 1 := by
    rw [← Domain.Algebra.power_mul, Nat.mul_comm, Domain.Algebra.power_mul,
      Domain.generator_power, Semiring.one_pow]
  rw [right, Semiring.mul_one, ← Domain.Algebra.power_mul, Nat.mul_comm,
    Domain.Algebra.power_mul, ← power, generator_nested _ _ nested, queryPoint_eq]

theorem queryPoint_reduce (parent child arity : Domain.Subgroup)
    (dimensions : parent.val = child.val + arity.val) {index : Nat}
    (bounded : index < Domain.size parent) :
    queryPoint parent index ^ Domain.size arity =
      queryPoint child (index / Domain.size arity) := by
  have nested : arity.val ≤ parent.val := by omega
  have bound : index / Domain.size arity < 2^(parent.val - arity.val) := by
    apply index_split_bound
    simpa only [Nat.sub_add_cancel nested, Domain.size] using bounded
  have reconstruct : index / Domain.size arity * Domain.size arity + index % Domain.size arity = index := by
    have := Nat.mod_add_div index (Domain.size arity)
    rw [Nat.mul_comm] at this
    omega
  have row := foldNode_eq parent arity nested bound (Nat.mod_lt index (Domain.size_positive arity))
  rw [reconstruct] at row
  rw [← row, foldNode_power _ _ _ dimensions]

theorem inputPoint_nonzero (domain : Domain.Subgroup) (index : Nat) :
    inputPoint domain index ≠ 0 := by
  intro zero
  exact ((G.mul_eq_zero_iff _ _).mp zero).elim (by decide) (queryPoint_nonzero _ _)

theorem inputPoint_injective (domain : Domain.Subgroup) {left right : Nat}
    (leftBound : left < Domain.size domain) (rightBound : right < Domain.size domain)
    (equal : inputPoint domain left = inputPoint domain right) : left = right := by
  apply queryPoint_injective domain leftBound rightBound
  unfold inputPoint at equal
  have zero : (7 : G) * (queryPoint domain left - queryPoint domain right) = 0 := by grind
  exact (G.sub_eq_zero_iff _ _).mp (((G.mul_eq_zero_iff _ _).mp zero).resolve_left (by decide))

theorem inputPoint_power (domain : Domain.Subgroup) (index : Nat) :
    inputPoint domain index ^ Domain.size domain = (7 : G) ^ Domain.size domain := by
  rw [inputPoint, CommSemiring.mul_pow, queryPoint_power, Semiring.mul_one]

theorem coset_shift_certificate : G.pow 7 (2^32) ≠ 1 := by decide +kernel

theorem coset_shift_not_root (domain : Domain.Subgroup) : (7 : G) ^ Domain.size domain ≠ 1 := by
  intro root
  have power := congrArg (fun value : G => value ^ (2^(32 - domain.val))) root
  rw [← Domain.Algebra.power_mul, Domain.size, ← Nat.pow_add,
    Nat.add_sub_of_le (by have := domain.isLt; omega), Semiring.one_pow,
    ← G.pow_eq _ _ (by decide)] at power
  exact coset_shift_certificate power

theorem inputPoint_not_root (domain : Domain.Subgroup) (index : Nat) :
    inputPoint domain index ^ Domain.size domain ≠ 1 := by
  rw [inputPoint_power]
  exact coset_shift_not_root domain

theorem inputPoint_trace_disjoint (query trace : Domain.Subgroup)
    (nested : trace.val ≤ query.val) (index : Nat) (row : Fin (Domain.size trace)) :
    inputPoint query index ≠ Domain.point trace row := by
  intro equal
  apply inputPoint_not_root query index
  rw [equal]
  have sizes : Domain.size query = Domain.size trace * 2^(query.val - trace.val) := by
    simp only [Domain.size, ← Nat.pow_add, Nat.add_sub_of_le nested]
  rw [sizes, Domain.Algebra.power_mul, Domain.point_power, Semiring.one_pow]

end Aiur.NativeAIR.FriDomain
