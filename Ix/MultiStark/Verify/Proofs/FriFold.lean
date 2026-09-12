module
public import Ix.MultiStark.Verify.Protocol.FriFold
public import Ix.MultiStark.Verify.Proofs.Arithmetic

public section

namespace MultiStark.Verify.Proofs

theorem lowBits_succ (value bits : Nat) :
    Protocol.lowBits value (bits + 1) = value % 2 :: Protocol.lowBits (value / 2) bits := by
  simp [Protocol.lowBits, List.range_succ_eq_map, List.map_map, Nat.pow_succ,
    Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem reverseBits_go_refines (bits value initial : Nat) :
    Fri.reverseBits.go bits value initial =
      (Protocol.lowBits value bits).foldl (fun acc bit => acc * 2 + bit) initial := by
  induction bits generalizing value initial with
  | zero => simp [Fri.reverseBits.go, Protocol.lowBits]
  | succ bits ih => simp only [Fri.reverseBits.go, lowBits_succ, List.foldl_cons, ih]

theorem reverseBits_refines (value bits : Nat) : Fri.reverseBits value bits = Protocol.bitReverse value bits :=
  reverseBits_go_refines bits value 0

theorem reverseBits_go_bounded (bits value initial : Nat) :
    Fri.reverseBits.go bits value initial < (initial + 1) * 2 ^ bits := by
  induction bits generalizing value initial with
  | zero => simp [Fri.reverseBits.go]
  | succ bits ih =>
    have bitBound := Nat.mod_lt value (by decide : 0 < 2)
    calc
      _ < (initial * 2 + value % 2 + 1) * 2 ^ bits := ih (value / 2) (initial * 2 + value % 2)
      _ ≤ (2 * (initial + 1)) * 2 ^ bits := Nat.mul_le_mul_right _ (by omega)
      _ = (initial + 1) * 2 ^ (bits + 1) := by simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]

theorem reverseBits_bounded (value bits : Nat) : Fri.reverseBits value bits < 2 ^ bits := by
  simpa only [Fri.reverseBits, Nat.zero_add, Nat.one_mul] using reverseBits_go_bounded bits value 0

theorem fri_polynomial_refines (coefficients : Array Ext) (point : Ext) :
    Fri.polynomial coefficients point = Protocol.PolynomialValue coefficients.toList point := rfl

theorem rowPoints_refines (index logHeight logArity : Nat) (result : Array Field) :
    Fri.rowPoints index logHeight logArity = .ok result ↔ Protocol.RowPoints index logHeight logArity result := by
  simp only [Fri.rowPoints, bind_ok_iff, unit_exists_iff, ensure_ok_iff, Bool.and_eq_true,
    decide_eq_true_eq, mapError_ok_iff, twoAdicGenerator_refines, pure_ok_iff,
    reverseBits_refines, Protocol.RowPoints, exists_and_left, and_assoc]

theorem interpolationProducts_refines (selected : Nat) (xi : Field) (point : Ext)
    (indexed : List (Field × Nat)) (numerator : Ext) (denominator : Field) :
    Fri.interpolationProducts selected xi point indexed numerator denominator =
      (Protocol.LagrangeNumerator (Protocol.otherRowPoints indexed selected) point numerator,
        Protocol.LagrangeDenominator (Protocol.otherRowPoints indexed selected) xi denominator) := by
  induction indexed generalizing numerator denominator with
  | nil => simp [Fri.interpolationProducts, Protocol.otherRowPoints,
      Protocol.LagrangeNumerator, Protocol.LagrangeDenominator]
  | cons entry rest ih =>
    cases entry with
    | mk xj index =>
      by_cases selectedHere : selected = index
      · subst index
        simpa [Fri.interpolationProducts, Protocol.otherRowPoints,
          Protocol.LagrangeNumerator, Protocol.LagrangeDenominator] using ih numerator denominator
      · simpa [Fri.interpolationProducts, beq_iff_eq, selectedHere, Protocol.otherRowPoints,
          Protocol.LagrangeNumerator, Protocol.LagrangeDenominator] using
          ih (numerator.mul (point.sub (Arithmetic.embed xj))) (denominator.mul (xi.sub xj))

theorem interpolateFrom_refines (allPoints : List (Field × Nat)) (point : Ext)
    (points : List Field) (values : List Ext) (index : Nat) (initial result : Ext) :
    Fri.interpolateFrom allPoints point points values index initial = .ok result ↔
      Protocol.InterpolationSum allPoints point points values index initial result := by
  induction points generalizing values index initial with
  | nil => cases values <;> simp [Fri.interpolateFrom, Protocol.InterpolationSum]
  | cons xi points ih =>
    cases values with
    | nil => simp [Fri.interpolateFrom, Protocol.InterpolationSum]
    | cons yi values =>
      simp only [Fri.interpolateFrom, interpolationProducts_refines, bind_ok_iff,
        mapError_ok_iff, inverseBase_refines, ih, Protocol.InterpolationSum]

theorem interpolate_refines (points : Array Field) (values : Array Ext) (point result : Ext) :
    Fri.interpolate points values point = .ok result ↔ Protocol.Interpolation points values point result := by
  simp only [Fri.interpolate, bind_ok_iff, unit_exists_iff, ensure_ok_iff, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true', Array.isEmpty_eq_false_iff, interpolateFrom_refines,
    Protocol.Interpolation, and_assoc]

theorem foldRow_refines (limits : Fri.Limits) (index logHeight logArity : Nat) (beta : Ext)
    (values : Array Ext) (result : Ext) :
    Fri.foldRow limits index logHeight logArity beta values = .ok result ↔
      Protocol.RowFold limits index logHeight logArity beta values result := by
  simp only [Fri.foldRow, bind_ok_iff, unit_exists_iff, ensure_ok_iff, decide_eq_true_eq,
    beq_iff_eq, rowPoints_refines, interpolate_refines, Protocol.RowFold]

end MultiStark.Verify.Proofs
