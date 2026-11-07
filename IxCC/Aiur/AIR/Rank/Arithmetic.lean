import IxCC.Aiur.AIR.Rank.Model
import IxCC.Aiur.Field

/-! Natural bounds for the exact pinned field operations. These arguments
use canonical residues and concrete bounds, not primality or field axioms. -/

namespace IxCC.Aiur.AIR.Rank

open _root_.Aiur (G gSize)

theorem mul_n (left right : G) : (left * right).n = (left.n * right.n) % gSize.toNat :=
  G.ofNat_n _

theorem ofNat_n {value : Nat} (small : value < gSize.toNat) : (G.ofNat value).n = value := by
  rw [G.ofNat_n, Nat.mod_eq_of_lt small]

theorem Limbs.value_lt {limbs : Limbs} (bounded : limbs.Bounded) : limbs.value < rankBound := by
  rcases bounded with ⟨low, middle, high⟩
  dsimp only [limbBound] at low middle high
  unfold Limbs.value rankBound
  omega

theorem Limbs.packed_n {limbs : Limbs} (bounded : limbs.Bounded) :
    limbs.packed.n = limbs.value := by
  rcases bounded with ⟨low, middle, high⟩
  dsimp only [limbBound] at low middle high
  have modulus : gSize.toNat = 18446744069414584321 := by decide
  have midConst : (65536 : G).n = 65536 := by decide
  have highConst : (4294967296 : G).n = 4294967296 := by decide
  simp only [Limbs.packed, G.add_n, mul_n, midConst, highConst, modulus]
  rw [Nat.mod_eq_of_lt (show limbs.middle.n * 65536 < 18446744069414584321 by omega)]
  rw [Nat.mod_eq_of_lt (show limbs.high.n * 4294967296 < 18446744069414584321 by omega)]
  rw [Nat.mod_eq_of_lt (show limbs.low.n + limbs.middle.n * 65536 < 18446744069414584321 by omega)]
  rw [Nat.mod_eq_of_lt (show limbs.low.n + limbs.middle.n * 65536 + limbs.high.n * 4294967296 <
    18446744069414584321 by omega)]
  rfl

theorem ordered_n {parent gap : Limbs} (parentBound : parent.Bounded) (gapBound : gap.Bounded) :
    (ordered parent gap).n = parent.value + 1 + gap.value := by
  have hp := parent.value_lt parentBound
  have hg := gap.value_lt gapBound
  dsimp only [rankBound] at hp hg
  have modulus : gSize.toNat = 18446744069414584321 := by decide
  have one : (1 : G).n = 1 := by decide
  simp only [ordered, G.add_n, parent.packed_n parentBound, gap.packed_n gapBound, one, modulus]
  rw [Nat.mod_eq_of_lt (show parent.value + 1 < 18446744069414584321 by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem ordered_eq {parent gap child : Limbs}
    (parentBound : parent.Bounded) (gapBound : gap.Bounded) (childBound : child.Bounded)
    (binding : ordered parent gap = child.packed) :
    child.value = parent.value + 1 + gap.value := by
  have values := congrArg G.n binding
  rw [ordered_n parentBound gapBound, child.packed_n childBound] at values
  exact values.symm

theorem ordered_increases {parent gap child : Limbs}
    (parentBound : parent.Bounded) (gapBound : gap.Bounded) (childBound : child.Bounded)
    (binding : ordered parent gap = child.packed) : parent.value < child.value := by
  have := ordered_eq parentBound gapBound childBound binding
  omega

theorem ordered_no_self {parent gap : Limbs}
    (parentBound : parent.Bounded) (gapBound : gap.Bounded) : ordered parent gap ≠ parent.packed := by
  intro binding
  have := ordered_increases parentBound gapBound parentBound binding
  omega

end IxCC.Aiur.AIR.Rank
