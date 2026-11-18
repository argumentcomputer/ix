import Aiur.Tiling.Layout
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Field.ZMod

/-!
# Copy constraints by fixed multiplicities

A class of `o` cells with one label whose multiplicities are `o - 1` on an
anchor and `-1` elsewhere balances, for every value, only if every cell
holds the anchor's value: the cells agreeing with the anchor sum to
`o - k` for `k` of them, which vanishes only when `k = o` (`o < p`).
-/

namespace Aiur.Tiling

variable {F : Type} [Field F] [DecidableEq F]

/-- Naturals below `bound` are nonzero in `F` unless zero. -/
def SmallCast (F : Type) [Field F] (bound : Nat) : Prop := ∀ n < bound, (n : F) = 0 → n = 0

/-- `SmallCast` in a prime field holds up to the characteristic: BN254 and
Goldilocks (`p = 2^64 − 2^32 + 1`) at any `bound ≤ p`. -/
theorem smallCast_zmod (p : Nat) [Fact p.Prime] {bound : Nat} (h : bound ≤ p) : SmallCast (ZMod p) bound := by
  intro n hn e
  rw [ZMod.natCast_eq_zero_iff] at e
  rcases Nat.eq_zero_or_pos n with z | pos
  · exact z
  · exact absurd (Nat.le_of_dvd pos e) (by omega)

theorem SmallCast.inj {bound : Nat} (small : SmallCast F bound) {a b : Nat} (ha : a < bound)
    (hb : b < bound) (h : (a : F) = b) : a = b := by
  rcases Nat.lt_or_ge a b with lt | ge
  · have := small (b - a) (by omega) (by rw [Nat.cast_sub lt.le, h, sub_self])
    omega
  · have := small (a - b) (by omega) (by rw [Nat.cast_sub ge, h, sub_self])
    omega

theorem copy_class {ι : Type} [DecidableEq ι] (S : Finset ι) (anchor : ι) (mem : anchor ∈ S)
    (mult value : ι → F) (anchorMult : mult anchor = (S.card : F) - 1)
    (otherMult : ∀ e ∈ S, e ≠ anchor → mult e = -1)
    (balanced : ∑ e ∈ S.filter (fun e => value e = value anchor), mult e = 0)
    (small : SmallCast F S.card) : ∀ e ∈ S, value e = value anchor := by
  set T := S.filter fun e => value e = value anchor
  have anchorT : anchor ∈ T := Finset.mem_filter.mpr ⟨mem, rfl⟩
  have split : ∑ e ∈ T, mult e = mult anchor + ∑ e ∈ T.erase anchor, mult e :=
    (Finset.add_sum_erase T mult anchorT).symm
  have rest : ∑ e ∈ T.erase anchor, mult e = ∑ e ∈ T.erase anchor, (-1 : F) := by
    apply Finset.sum_congr rfl
    intro e he
    have := Finset.mem_erase.mp he
    exact otherMult e (Finset.mem_filter.mp this.2).1 this.1
  rw [rest, Finset.sum_const, Finset.card_erase_of_mem anchorT, anchorMult] at split
  have le : T.card ≤ S.card := Finset.card_filter_le _ _
  have pos : 1 ≤ T.card := Finset.card_pos.mpr ⟨anchor, anchorT⟩
  have cast : ((S.card - T.card : Nat) : F) = 0 := by
    rw [Nat.cast_sub le]
    rw [balanced, nsmul_eq_mul, Nat.cast_sub pos] at split
    simp only [Nat.cast_one] at split
    linear_combination -split
  have := small (S.card - T.card) (by omega) cast
  have full : T.card = S.card := by omega
  exact Finset.filter_card_eq full

end Aiur.Tiling
