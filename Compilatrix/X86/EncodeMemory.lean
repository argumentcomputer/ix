import Compilatrix.X86.EncodeFields

/-! Exact emitted addressing bytes: ModRM mode 0 (no displacement), 1
(disp8) or 2 (disp32), with or without SIB, and their consumption by the
independent parser. -/

namespace Compilatrix.X86.Encode

/-- Scale bits have no architectural effect in the absence of an index. -/
abbrev normalizedAddress (address : MemAddr) : MemAddr := address.normalize

@[simp] theorem normalizedAddress_eval (address : MemAddr) (core : Core) :
    (normalizedAddress address).eval core = address.eval core := by
  cases address with
  | mk base index scale displacement => cases index <;> rfl

theorem normalize_canonical (address : MemAddr) : address.normalize.canonical = true := by
  cases address with
  | mk base index scale displacement =>
      cases index <;> simp [MemAddr.normalize, MemAddr.canonical]

theorem normalize_of_canonical {address : MemAddr} (canonical : address.canonical = true) :
    address.normalize = address := by
  cases address with
  | mk base index scale displacement =>
      cases index <;> simp_all [MemAddr.normalize, MemAddr.canonical]

theorem dispMode_lt (low : Nat) (displacement : Imm32) : dispMode low displacement < 3 := by
  unfold dispMode
  split
  · decide
  · split <;> decide

theorem dispMode_zero {low : Nat} {displacement : Imm32} (zero : dispMode low displacement = 0) :
    low ≠ 5 := by
  unfold dispMode at zero
  split at zero
  · rename_i small
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at small
    exact small.2
  · split at zero <;> contradiction

theorem displacement_decode (low : Nat) (displacement : Imm32) (rest : List UInt8) :
    Decode.displacement (dispMode low displacement)
      (dispBytes (dispMode low displacement) displacement ++ rest) = some (displacement, rest) := by
  unfold dispMode
  by_cases zero : (displacement == 0 && low != 5) = true
  · simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at zero
    simp [zero, Decode.displacement, dispBytes]
  · by_cases fits : fitsDisp8 displacement = true
    · simp [zero, fits, Decode.displacement, dispBytes, readLE_le]; simpa [fitsDisp8] using fits
    · simp [zero, fits, Decode.displacement, dispBytes, readLE_le]


theorem scaleZero : Decode.scale 0 = some .one := rfl

theorem memoryTail_decode (rex : Decode.Rex) (regField : Nat) (address : MemAddr)
    (canonical : address.canonical = true)
    (hx : rex.x = (memoryTail regField address).rexX) (hb : rex.b = (memoryTail regField address).rexB)
    (rest : List UInt8) :
    ∃ modrm more, (memoryTail regField address).bytes = modrm :: more ∧ Decode.modMode modrm ≠ 3 ∧
      Decode.modReg modrm = regField % 8 ∧ Decode.memory rex modrm (more ++ rest) = some (address, rest) := by
  cases address with
  | mk base index scale displacement =>
    cases base with
    | none =>
      cases index with
      | none =>
          simp only [MemAddr.canonical, Option.isSome_none, Bool.false_or, beq_iff_eq] at canonical
          subst canonical
          simp only [memoryTail, Option.map_none] at hx hb
          refine ⟨modRM 0 regField 4, sib 0 4 5 :: le 4 displacement.toUInt64, rfl, by simp, by simp, ?_⟩
          simp [Decode.memory, scaleZero, hx, hb, readLE_le]
      | some index =>
          simp only [memoryTail, Option.map_some] at hx hb
          refine ⟨modRM 0 regField 4,
            sib (scaleBits scale) (registerLow (indexRegCode index)) 5 :: le 4 displacement.toUInt64,
            rfl, by simp, by simp, ?_⟩
          simp [Decode.memory, hx, hb, readLE_le]
    | some base =>
      have modeBound := dispMode_lt (registerLow (gprCode base)) displacement
      have modeZero := @dispMode_zero (registerLow (gprCode base)) displacement
      have notThree : dispMode (registerLow (gprCode base)) displacement ≠ 3 := by omega
      have modeFour : dispMode (registerLow (gprCode base)) displacement < 4 := by omega
      have modeOf := fun (regField rm : Nat) => modRM_mode _ regField rm modeFour
      have notAbsent : ¬(dispMode (registerLow (gprCode base)) displacement = 0 ∧
          registerLow (gprCode base) = 5) := fun ⟨zero, five⟩ => modeZero zero five
      by_cases useSib : (index.isSome || registerLow (gprCode base) == 4) = true
      · cases index with
        | none =>
            simp only [MemAddr.canonical, Option.isSome_none, Bool.false_or, beq_iff_eq] at canonical
            subst canonical
            simp only [memoryTail, useSib, ite_true, Option.map_none] at hx hb
            refine ⟨modRM (dispMode (registerLow (gprCode base)) displacement) regField 4,
              sib 0 4 (registerLow (gprCode base)) ::
                dispBytes (dispMode (registerLow (gprCode base)) displacement) displacement,
              by simp only [memoryTail, useSib, ite_true, Option.map_none]; rfl,
              by rw [modeOf]; exact notThree, by simp, ?_⟩
            simp [Decode.memory, scaleZero, hx, hb, modeOf, notThree, notAbsent, displacement_decode]
        | some index =>
            simp only [memoryTail, useSib, ite_true, Option.map_some] at hx hb
            refine ⟨modRM (dispMode (registerLow (gprCode base)) displacement) regField 4,
              sib (scaleBits scale) (registerLow (indexRegCode index)) (registerLow (gprCode base)) ::
                dispBytes (dispMode (registerLow (gprCode base)) displacement) displacement,
              by simp only [memoryTail, useSib, ite_true, Option.map_some]; rfl,
              by rw [modeOf]; exact notThree, by simp, ?_⟩
            simp [Decode.memory, hx, hb, modeOf, notThree, notAbsent, displacement_decode]
      · have useSib' := useSib
        simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true, Option.isSome_eq_false_iff,
          Option.isNone_iff_eq_none] at useSib'
        obtain ⟨noIndex, notFour⟩ := useSib'
        subst noIndex
        simp only [MemAddr.canonical, Option.isSome_none, Bool.false_or, beq_iff_eq] at canonical
        subst canonical
        simp only [memoryTail, useSib, Bool.false_eq_true, ite_false] at hx hb
        refine ⟨modRM (dispMode (registerLow (gprCode base)) displacement) regField (registerLow (gprCode base)),
          dispBytes (dispMode (registerLow (gprCode base)) displacement) displacement,
          by simp only [memoryTail, useSib, Bool.false_eq_true, ite_false],
          by rw [modeOf]; exact notThree, by simp, ?_⟩
        simp [Decode.memory, hx, hb, modeOf, notThree, notFour, notAbsent, displacement_decode]

end Compilatrix.X86.Encode
