import IxCC.Aiur.AIR.Rank.Arithmetic

/-! Extract each scalar-u16 bound from its complete fixed-table message. -/

namespace IxCC.Aiur.AIR.Rank

open _root_.Aiur (G gSize)

theorem rangeValue_n {index : Nat} (bound : index < limbBound) : (rangeValue index).n = index := by
  change index < 65536 at bound
  have modulus : gSize.toNat = 18446744069414584321 := by decide
  have constant : (256 : G).n = 256 := by decide
  have divBound : index / 256 < 256 := by omega
  have modBound : index % 256 < 256 := Nat.mod_lt _ (by decide)
  have divmod := Nat.div_add_mod index 256
  simp only [rangeValue, G.add_n, mul_n, G.ofNat_n, constant, modulus]
  rw [Nat.mod_eq_of_lt (show index / 256 < 18446744069414584321 by omega)]
  rw [Nat.mod_eq_of_lt (show index % 256 < 18446744069414584321 by omega)]
  rw [Nat.mod_eq_of_lt (show index / 256 * 256 < 18446744069414584321 by omega)]
  rw [Nat.mod_eq_of_lt (show index / 256 * 256 + index % 256 < 18446744069414584321 by omega)]
  omega

theorem rangeValue_eq {index : Nat} (bound : index < limbBound) : rangeValue index = G.ofNat index := by
  apply Field.ext
  rw [rangeValue_n bound, ofNat_n (by change index < 18446744069414584321; change index < 65536 at bound; omega)]

theorem rangeProvided_iff (value : G) : RangeProvided value ↔ value.n < limbBound := by
  constructor
  · rintro ⟨index, bound, message⟩
    have equal : value = rangeValue index := by simpa using message
    rw [equal, rangeValue_n bound]
    exact bound
  · intro bound
    refine ⟨value.n, bound, ?_⟩
    have equal : value = rangeValue value.n := by
      apply Field.ext
      exact (rangeValue_n bound).symm
    exact congrArg (fun item : G => [15, item]) equal

theorem Limbs.rangeProvided_iff (limbs : Limbs) : limbs.RangeProvided ↔ limbs.Bounded := by
  simp only [Limbs.RangeProvided, Limbs.Bounded, Rank.rangeProvided_iff]

theorem rangePull_arguments (current : List G) (index : Nat) :
    rangePull.arguments.mapM (Expr.eval ⟨current, [], false, rangeColumns index⟩) =
      some [15, rangeValue index] := by
  simp [rangePull, Expr.eval, rangeColumns, rangeValue]

theorem rangePull_weight (current : List G) (index : Nat) (weight : G)
    (column : current[7]? = some weight) :
    rangePull.multiplicity.eval ⟨current, [], false, rangeColumns index⟩ = some (0 - weight) := by
  simp [rangePull, Expr.eval, column]

theorem ordered_from_range {parent gap child : Limbs}
    (parentRanges : parent.RangeProvided) (gapRanges : gap.RangeProvided)
    (childRanges : child.RangeProvided) (binding : ordered parent gap = child.packed) :
    child.value = parent.value + 1 + gap.value ∧ parent.value < child.value := by
  have hp := parent.rangeProvided_iff.mp parentRanges
  have hg := gap.rangeProvided_iff.mp gapRanges
  have hc := child.rangeProvided_iff.mp childRanges
  exact ⟨ordered_eq hp hg hc binding, ordered_increases hp hg hc binding⟩

end IxCC.Aiur.AIR.Rank
