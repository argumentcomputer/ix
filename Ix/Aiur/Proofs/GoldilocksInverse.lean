/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.GoldilocksAlgebra
import Ix.Aiur.Proofs.Field

/-! Fermat's theorem for the actual Goldilocks representation. Multiplication
by a nonzero element permutes the finite list of nonzero residues. Cancelling
its nonzero product proves the exponent identity and the runtime inverse law.
The argument is symbolic; the list of field elements is never evaluated.
-/

namespace Aiur.G

theorem mul_right_cancel {a b c : G} (nonzero : c ≠ 0) (equal : a * c = b * c) : a = b := by
  have zero : (a - b) * c = 0 := by grind
  have same := (G.mul_eq_zero_iff _ _).mp zero |>.resolve_right nonzero
  exact (G.sub_eq_zero_iff a b).mp same

/-- A mathematical enumeration, excluded from runtime initialization. -/
noncomputable def nonzeroResidues : List G :=
  List.ofFn fun index : Fin (gSize.toNat - 1) => G.ofNat (index.val + 1)

theorem nonzeroResidues_length : nonzeroResidues.length = gSize.toNat - 1 := List.length_ofFn

theorem mem_nonzeroResidues (a : G) : a ∈ nonzeroResidues ↔ a ≠ 0 := by
  constructor
  · intro member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    apply G.ofNat_ne_zero_of_lt (by omega)
    have bound := index.isLt
    omega
  · intro nonzero
    have positive : 0 < a.n := Nat.pos_of_ne_zero fun equal => nonzero ((G.n_eq_zero_iff a).mp equal)
    have bounded := UInt64.lt_iff_toNat_lt.mp a.property
    change a.n < gSize.toNat at bounded
    apply List.mem_ofFn.mpr
    refine ⟨⟨a.n - 1, by omega⟩, ?_⟩
    change G.ofNat (a.n - 1 + 1) = a
    rw [Nat.sub_add_cancel positive, G.ofNat_n]

theorem nonzeroResidues_nodup : nonzeroResidues.Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj lt same
  simp only [nonzeroResidues, List.getElem_ofFn] at same
  have bi : i < gSize.toNat - 1 := by simpa only [nonzeroResidues_length] using hi
  have bj : j < gSize.toNat - 1 := by simpa only [nonzeroResidues_length] using hj
  have equal := G.ofNat_injective_below (by omega : i + 1 < gSize.toNat)
    (by omega : j + 1 < gSize.toNat) same
  omega

theorem map_perm_of_injective (values : List G) (f : G → G) (nodup : values.Nodup)
    (injective : ∀ {x y}, f x = f y → x = y) (subset : values.map f ⊆ values) :
    (values.map f).Perm values := by
  have distinct : (values.map f).Nodup :=
    List.Pairwise.map f (fun _ _ different equal => different (injective equal)) nodup
  apply (List.perm_ext_iff_of_nodup distinct nodup).mpr
  intro value
  constructor
  · exact fun member => subset member
  · intro member
    by_cases included : value ∈ values.map f
    · exact included
    · have enlarged : (value :: values.map f).Nodup :=
        List.nodup_cons.mpr ⟨included, distinct⟩
      have bound := enlarged.length_le_of_subset (l₂ := values) (by
        intro x present
        rcases List.mem_cons.mp present with equal | tail
        · exact equal ▸ member
        · exact subset tail)
      simp only [List.length_cons, List.length_map] at bound
      omega

theorem multiplication_perm (a : G) (nonzero : a ≠ 0) :
    (nonzeroResidues.map (a * ·)).Perm nonzeroResidues := by
  apply map_perm_of_injective nonzeroResidues (a * ·) nonzeroResidues_nodup
  · intro x y equal
    apply mul_right_cancel nonzero
    simpa only [G.mul_comm _ a] using equal
  · intro value member
    obtain ⟨x, present, rfl⟩ := List.mem_map.mp member
    apply (mem_nonzeroResidues _).mpr
    intro zero
    exact ((G.mul_eq_zero_iff _ _).mp zero).elim nonzero ((mem_nonzeroResidues x).mp present)

def product : List G → G
  | [] => 1
  | value :: values => value * product values

theorem product_nonzero (values : List G) (nonzero : ∀ x ∈ values, x ≠ 0) : product values ≠ 0 := by
  induction values with
  | nil => exact G.one_ne_zero
  | cons x xs ih =>
    intro zero
    exact ((G.mul_eq_zero_iff _ _).mp zero).elim
      (nonzero x List.mem_cons_self)
      (ih (fun x member => nonzero x (List.mem_cons_of_mem _ member)))

theorem product_perm {left right : List G} (permuted : left.Perm right) : product left = product right := by
  induction permuted with
  | nil => rfl
  | cons x _ ih => simp only [product, ih]
  | swap a b rest => simp only [product]; grind
  | trans _ _ first second => exact first.trans second

theorem product_map_mul (a : G) (values : List G) :
    product (values.map (a * ·)) = a ^ values.length * product values := by
  induction values with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.length_cons, product, ih, Lean.Grind.Semiring.pow_succ]
    grind

theorem power_eq_one_of_perm (a : G) (values : List G)
    (nonzero : ∀ x ∈ values, x ≠ 0) (permuted : (values.map (a * ·)).Perm values) :
    a ^ values.length = 1 := by
  have same := product_perm permuted
  rw [product_map_mul] at same
  apply mul_right_cancel (product_nonzero values nonzero)
  simpa only [Lean.Grind.Semiring.one_mul] using same

theorem fermat (a : G) (nonzero : a ≠ 0) : a ^ (gSize.toNat - 1) = 1 := by
  have same := power_eq_one_of_perm a nonzeroResidues
    (fun x member => (mem_nonzeroResidues x).mp member) (multiplication_perm a nonzero)
  simpa only [nonzeroResidues_length] using same

theorem inverse_zero : G.inverse 0 = 0 := by decide +kernel

theorem mul_inverse_cancel (a : G) (nonzero : a ≠ 0) : a * a.inverse = 1 := by
  rw [G.inverse_eq_power, G.mul_comm, ← Lean.Grind.Semiring.pow_succ]
  have successor : gSize.toNat - 2 + 1 = gSize.toNat - 1 := by decide
  rw [successor]
  exact fermat a nonzero

end Aiur.G
