import Aiur.Library.U64
import Aiur.Library.U32.Correctness
import Aiur.Library.U8Facts
import Aiur.Library.Carry
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Algebraic and byte-packing lemmas for the algorithms of the `UInt64` library
(`Aiur.Library.U64`). For each of its twelve operations (`is_zero`, `eq`, `add`,
`wrapping_succ`, `saturating_pred`, `to_field`, `sub_with_borrow`, `mul`, `and`,
`or`, `xor`, `from_field`) they relate the byte-level computation, written out in
Lean, to the packed 64-bit value under `[Field F]` and `U64.Compatible F`. They
are lemmas about these Lean renderings, not theorems that evaluate the Aiur
source of the library functions.
-/
namespace Aiur.Library.U64

def base : Nat := 18446744073709551616

def fieldBound : Nat := 72057594037927936

theorem compatible_of_charZero (F : Type) [AddMonoidWithOne F] [CharZero F] :
    Compatible F := by
  intro _ _ _ _ equal
  exact Nat.cast_injective equal

theorem u32_compatible {F : Type} [NatCast F] (large : Compatible F) :
    U32.Compatible F := by
  intro a ha b hb equal
  apply large
  · change a < 2^56
    change a < 3 * U32.base at ha
    unfold U32.base at ha
    omega
  · change b < 2^56
    change b < 3 * U32.base at hb
    unfold U32.base at hb
    omega
  · exact equal

def pack (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Nat :=
  b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 +
    4294967296 * b4 + 1099511627776 * b5 +
    281474976710656 * b6 + 72057594037927936 * b7

def pack56 (b0 b1 b2 b3 b4 b5 b6 : Nat) : Nat :=
  b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 +
    4294967296 * b4 + 1099511627776 * b5 +
    281474976710656 * b6

def limb2 (r0 r1 : Nat) : Nat :=
  r0 + 256 * r1

def carry3 (c0 c1 c2 : Nat) : Nat :=
  c0 + 256 * c1 + 65536 * c2

theorem pack_eq_pack56_add (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    pack b0 b1 b2 b3 b4 b5 b6 b7 = pack56 b0 b1 b2 b3 b4 b5 b6 + fieldBound * b7 := by
  unfold pack pack56 fieldBound
  ring

theorem pack_lt {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    pack b0 b1 b2 b3 b4 b5 b6 b7 < base := by
  unfold pack base
  omega

theorem pack56_lt {b0 b1 b2 b3 b4 b5 b6 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) :
    pack56 b0 b1 b2 b3 b4 b5 b6 < fieldBound := by
  unfold pack56 fieldBound
  omega

theorem limb2_lt {r0 r1 : Nat} (h0 : r0 < 256) (h1 : r1 < 256) :
    limb2 r0 r1 < 65536 := by
  unfold limb2
  omega

theorem carry3_lt {c0 c1 c2 : Nat} (h0 : c0 < 256) (h1 : c1 < 256) (h2 : c2 < 256) :
    carry3 c0 c1 c2 < 16777216 := by
  unfold carry3
  omega

theorem pack56_inj {a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (_ha6 : a6 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (_hb6 : b6 < 256) :
    pack56 a0 a1 a2 a3 a4 a5 a6 = pack56 b0 b1 b2 b3 b4 b5 b6 ↔
      a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧
      a4 = b4 ∧ a5 = b5 ∧ a6 = b6 := by
  constructor
  · intro h
    unfold pack56 at h
    have h6 : a6 = b6 := by omega
    subst h6
    have h5 : a5 = b5 := by omega
    subst h5
    have h4 : a4 = b4 := by omega
    subst h4
    have h3 : a3 = b3 := by omega
    subst h3
    have h2 : a2 = b2 := by omega
    subst h2
    have h1 : a1 = b1 := by omega
    subst h1
    have h0 : a0 = b0 := by omega
    exact ⟨h0, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

theorem pack_inj {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (_ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (_hb7 : b7 < 256) :
    pack a0 a1 a2 a3 a4 a5 a6 a7 = pack b0 b1 b2 b3 b4 b5 b6 b7 ↔
      a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧
      a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 := by
  constructor
  · intro h
    rw [pack_eq_pack56_add, pack_eq_pack56_add] at h
    have h56a := pack56_lt ha0 ha1 ha2 ha3 ha4 ha5 ha6
    have h56b := pack56_lt hb0 hb1 hb2 hb3 hb4 hb5 hb6
    have h7 : a7 = b7 := by unfold fieldBound at *; omega
    subst h7
    have h56 : pack56 a0 a1 a2 a3 a4 a5 a6 = pack56 b0 b1 b2 b3 b4 b5 b6 := by omega
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
      (pack56_inj ha0 ha1 ha2 ha3 ha4 ha5 ha6 hb0 hb1 hb2 hb3 hb4 hb5 hb6).mp h56
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

variable {F : Type} [Field F]

theorem natCast_inj (large : Compatible F) {a b : Nat}
    (ha : a < fieldBound) (hb : b < fieldBound) (equal : (a : F) = (b : F)) :
    a = b :=
  large (by simpa [fieldBound] using ha) (by simpa [fieldBound] using hb) equal

theorem byte_cast_inj (large : Compatible F) {a b : Nat}
    (ha : a < 256) (hb : b < 256) (equal : (a : F) = (b : F)) :
    a = b :=
  natCast_inj large (by unfold fieldBound; omega) (by unfold fieldBound; omega) equal

theorem byte_cast_eq_iff (large : Compatible F) {a b : Nat}
    (ha : a < 256) (hb : b < 256) :
    ((a : F) = (b : F)) ↔ a = b :=
  ⟨byte_cast_inj large ha hb, fun h => by subst h; rfl⟩

theorem byte_sub_eq_zero_iff (large : Compatible F) {a b : Nat}
    (ha : a < 256) (hb : b < 256) :
    ((a : F) - (b : F) = 0) ↔ a = b := by
  rw [sub_eq_zero]
  exact byte_cast_eq_iff large ha hb

theorem two_ne_zero (large : Compatible F) : (2 : F) ≠ 0 := by
  intro equal
  have := natCast_inj large (a := 2) (b := 0) (by unfold fieldBound; omega)
    (by unfold fieldBound; omega) (by simpa using equal)
  omega

theorem radix_ne_zero (large : Compatible F) : (256 : F) ≠ 0 := by
  intro equal
  have := natCast_inj large (a := 256) (b := 0) (by unfold fieldBound; omega)
    (by unfold fieldBound; omega) (by simpa using equal)
  omega

theorem byte_eq_zero_iff (large : Compatible F) {a : Nat} (ha : a < 256) :
    ((a : F) = 0) ↔ a = 0 := by
  have hz : (0 : F) = ((0 : Nat) : F) := by simp
  rw [hz]
  exact byte_cast_eq_iff large ha (by omega)

/-! ### 1. `is_zero` -/

theorem is_zero_sound (large : Compatible F) {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    ((b0 : F) = 0 ∧ (b1 : F) = 0 ∧ (b2 : F) = 0 ∧ (b3 : F) = 0 ∧
     (b4 : F) = 0 ∧ (b5 : F) = 0 ∧ (b6 : F) = 0 ∧ (b7 : F) = 0) ↔
      pack b0 b1 b2 b3 b4 b5 b6 b7 = 0 := by
  rw [byte_eq_zero_iff large h0, byte_eq_zero_iff large h1,
      byte_eq_zero_iff large h2, byte_eq_zero_iff large h3,
      byte_eq_zero_iff large h4, byte_eq_zero_iff large h5,
      byte_eq_zero_iff large h6, byte_eq_zero_iff large h7]
  unfold pack
  omega

/-! ### 2. `eq` -/

theorem eq_sound (large : Compatible F)
    {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) :
    ((a0 : F) - (b0 : F) = 0 ∧ (a1 : F) - (b1 : F) = 0 ∧
     (a2 : F) - (b2 : F) = 0 ∧ (a3 : F) - (b3 : F) = 0 ∧
     (a4 : F) - (b4 : F) = 0 ∧ (a5 : F) - (b5 : F) = 0 ∧
     (a6 : F) - (b6 : F) = 0 ∧ (a7 : F) - (b7 : F) = 0) ↔
      pack a0 a1 a2 a3 a4 a5 a6 a7 = pack b0 b1 b2 b3 b4 b5 b6 b7 := by
  rw [byte_sub_eq_zero_iff large ha0 hb0,
      byte_sub_eq_zero_iff large ha1 hb1,
      byte_sub_eq_zero_iff large ha2 hb2,
      byte_sub_eq_zero_iff large ha3 hb3,
      byte_sub_eq_zero_iff large ha4 hb4,
      byte_sub_eq_zero_iff large ha5 hb5,
      byte_sub_eq_zero_iff large ha6 hb6,
      byte_sub_eq_zero_iff large ha7 hb7]
  exact (pack_inj ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7).symm

/-! ### 3. `add` -/

theorem split_sum_recover (large : Compatible F) (sum : Nat) :
    let byte := sum % 256
    (((sum : F) - ((byte : Nat) : F)) / (256 : F)) = (((sum / 256 : Nat) : F)) :=
  Carry.recover 256 sum (radix_ne_zero large)

theorem split_sum_step {sum s c : Nat}
    (hs : s = sum % 256) (hc : c = sum / 256) :
    sum = s + 256 * c ∧ s < 256 := by
  subst hs; subst hc
  exact ⟨(Nat.mod_add_div sum 256).symm, Nat.mod_lt sum (by omega)⟩

theorem add_sound
    {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    {s0 s1 s2 s3 s4 s5 s6 s7 c1 c2 c3 c4 c5 c6 c7 c8 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256)
    (hs0 : s0 < 256) (hs1 : s1 < 256) (hs2 : s2 < 256) (hs3 : s3 < 256)
    (hs4 : s4 < 256) (hs5 : s5 < 256) (hs6 : s6 < 256) (hs7 : s7 < 256)
    (h0 : a0 + b0 = s0 + 256 * c1)
    (h1 : a1 + b1 + c1 = s1 + 256 * c2)
    (h2 : a2 + b2 + c2 = s2 + 256 * c3)
    (h3 : a3 + b3 + c3 = s3 + 256 * c4)
    (h4 : a4 + b4 + c4 = s4 + 256 * c5)
    (h5 : a5 + b5 + c5 = s5 + 256 * c6)
    (h6 : a6 + b6 + c6 = s6 + 256 * c7)
    (h7 : a7 + b7 + c7 = s7 + 256 * c8) :
    pack s0 s1 s2 s3 s4 s5 s6 s7 =
      (pack a0 a1 a2 a3 a4 a5 a6 a7 + pack b0 b1 b2 b3 b4 b5 b6 b7) % base ∧
    c8 = (pack a0 a1 a2 a3 a4 a5 a6 a7 + pack b0 b1 b2 b3 b4 b5 b6 b7) / base ∧
    c8 < 2 := by
  have hpack : pack a0 a1 a2 a3 a4 a5 a6 a7 + pack b0 b1 b2 b3 b4 b5 b6 b7 =
      pack s0 s1 s2 s3 s4 s5 s6 s7 + base * c8 := by
    unfold pack base
    omega
  have hs_lt : pack s0 s1 s2 s3 s4 s5 s6 s7 < base :=
    pack_lt hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  have ha_lt : pack a0 a1 a2 a3 a4 a5 a6 a7 < base :=
    pack_lt ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
  have hb_lt : pack b0 b1 b2 b3 b4 b5 b6 b7 < base :=
    pack_lt hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have hc8_lt : c8 < 2 := by omega
  refine ⟨?_, ?_, hc8_lt⟩
  · rw [hpack, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs_lt]
  · rw [hpack, Nat.add_mul_div_left _ _ (by unfold base; omega),
        Nat.div_eq_of_lt hs_lt, Nat.zero_add]

/-! ### 4. `wrapping_succ` -/

def wrappingSuccBytes (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  if b0 = 255 then
    if b1 = 255 then
      if b2 = 255 then
        if b3 = 255 then
          if b4 = 255 then
            if b5 = 255 then
              if b6 = 255 then
                if b7 = 255 then (0, 0, 0, 0, 0, 0, 0, 0)
                else (0, 0, 0, 0, 0, 0, 0, b7 + 1)
              else (0, 0, 0, 0, 0, 0, b6 + 1, b7)
            else (0, 0, 0, 0, 0, b5 + 1, b6, b7)
          else (0, 0, 0, 0, b4 + 1, b5, b6, b7)
        else (0, 0, 0, b3 + 1, b4, b5, b6, b7)
      else (0, 0, b2 + 1, b3, b4, b5, b6, b7)
    else (0, b1 + 1, b2, b3, b4, b5, b6, b7)
  else (b0 + 1, b1, b2, b3, b4, b5, b6, b7)

theorem wrapping_succ_sound {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    let (r0, r1, r2, r3, r4, r5, r6, r7) := wrappingSuccBytes b0 b1 b2 b3 b4 b5 b6 b7
    r0 < 256 ∧ r1 < 256 ∧ r2 < 256 ∧ r3 < 256 ∧
    r4 < 256 ∧ r5 < 256 ∧ r6 < 256 ∧ r7 < 256 ∧
    pack r0 r1 r2 r3 r4 r5 r6 r7 = (pack b0 b1 b2 b3 b4 b5 b6 b7 + 1) % base := by
  unfold wrappingSuccBytes
  split_ifs with hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  · subst_vars; decide
  all_goals
    subst_vars
    dsimp only
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
    rw [Nat.mod_eq_of_lt (by unfold pack base; omega)]
    unfold pack
    omega

theorem wrapping_succ_bytes_sound {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    let (r0, r1, r2, r3, r4, r5, r6, r7) := wrappingSuccBytes b0 b1 b2 b3 b4 b5 b6 b7
    r0 < 256 ∧ r1 < 256 ∧ r2 < 256 ∧ r3 < 256 ∧
    r4 < 256 ∧ r5 < 256 ∧ r6 < 256 ∧ r7 < 256 ∧
    pack r0 r1 r2 r3 r4 r5 r6 r7 = (pack b0 b1 b2 b3 b4 b5 b6 b7 + 1) % base :=
  wrapping_succ_sound h0 h1 h2 h3 h4 h5 h6 h7

/-! ### 5. `saturating_pred` -/

def saturatingPredBytes (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  if b0 = 0 then
    if b1 = 0 then
      if b2 = 0 then
        if b3 = 0 then
          if b4 = 0 then
            if b5 = 0 then
              if b6 = 0 then
                if b7 = 0 then (0, 0, 0, 0, 0, 0, 0, 0)
                else (255, 255, 255, 255, 255, 255, 255, b7 - 1)
              else (255, 255, 255, 255, 255, 255, b6 - 1, b7)
            else (255, 255, 255, 255, 255, b5 - 1, b6, b7)
          else (255, 255, 255, 255, b4 - 1, b5, b6, b7)
        else (255, 255, 255, b3 - 1, b4, b5, b6, b7)
      else (255, 255, b2 - 1, b3, b4, b5, b6, b7)
    else (255, b1 - 1, b2, b3, b4, b5, b6, b7)
  else (b0 - 1, b1, b2, b3, b4, b5, b6, b7)

theorem saturating_pred_sound {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    let (r0, r1, r2, r3, r4, r5, r6, r7) := saturatingPredBytes b0 b1 b2 b3 b4 b5 b6 b7
    r0 < 256 ∧ r1 < 256 ∧ r2 < 256 ∧ r3 < 256 ∧
    r4 < 256 ∧ r5 < 256 ∧ r6 < 256 ∧ r7 < 256 ∧
    pack r0 r1 r2 r3 r4 r5 r6 r7 = pack b0 b1 b2 b3 b4 b5 b6 b7 - 1 := by
  unfold saturatingPredBytes
  split_ifs <;>
    (subst_vars; dsimp only;
     refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩;
     unfold pack; omega)

/-! ### 6. `to_field` -/

theorem top_byte_zero_iff (large : Compatible F) {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    (b7 : F) = 0 ↔ pack b0 b1 b2 b3 b4 b5 b6 b7 < fieldBound := by
  rw [byte_eq_zero_iff large h7, pack_eq_pack56_add]
  have h56 := pack56_lt h0 h1 h2 h3 h4 h5 h6
  unfold fieldBound at *
  omega

theorem to_field_sound (large : Compatible F) {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256)
    (topZero : (b7 : F) = 0) :
    pack b0 b1 b2 b3 b4 b5 b6 b7 < fieldBound ∧
    (b0 : F) + 256 * (b1 : F) + 65536 * (b2 : F) + 16777216 * (b3 : F) +
      4294967296 * (b4 : F) + 1099511627776 * (b5 : F) + 281474976710656 * (b6 : F) =
      ((pack b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : F) := by
  have hb7 : b7 = 0 := byte_cast_inj large h7 (by omega) (by simpa using topZero)
  refine ⟨(top_byte_zero_iff large h0 h1 h2 h3 h4 h5 h6 h7).mp topZero, ?_⟩
  subst hb7
  unfold pack
  push_cast
  ring

/-! ### 7. `sub_with_borrow` -/

theorem sub_with_borrow_sound
    {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    {s0 s1 s2 s3 s4 s5 s6 s7 c1 c2 c3 c4 c5 c6 c7 c8 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256)
    (hs0 : s0 < 256) (hs1 : s1 < 256) (hs2 : s2 < 256) (hs3 : s3 < 256)
    (hs4 : s4 < 256) (hs5 : s5 < 256) (hs6 : s6 < 256) (hs7 : s7 < 256)
    (h0 : a0 + 256 - b0 = s0 + 256 * c1)
    (h1 : a1 + 255 - b1 + c1 = s1 + 256 * c2)
    (h2 : a2 + 255 - b2 + c2 = s2 + 256 * c3)
    (h3 : a3 + 255 - b3 + c3 = s3 + 256 * c4)
    (h4 : a4 + 255 - b4 + c4 = s4 + 256 * c5)
    (h5 : a5 + 255 - b5 + c5 = s5 + 256 * c6)
    (h6 : a6 + 255 - b6 + c6 = s6 + 256 * c7)
    (h7 : a7 + 255 - b7 + c7 = s7 + 256 * c8) :
    pack s0 s1 s2 s3 s4 s5 s6 s7 =
      (pack a0 a1 a2 a3 a4 a5 a6 a7 + base - pack b0 b1 b2 b3 b4 b5 b6 b7) % base ∧
    (1 : F) - (c8 : F) =
      if pack a0 a1 a2 a3 a4 a5 a6 a7 < pack b0 b1 b2 b3 b4 b5 b6 b7 then 1 else 0 := by
  have hs_lt : pack s0 s1 s2 s3 s4 s5 s6 s7 < base :=
    pack_lt hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  have ha_lt : pack a0 a1 a2 a3 a4 a5 a6 a7 < base :=
    pack_lt ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
  have hb_lt : pack b0 b1 b2 b3 b4 b5 b6 b7 < base :=
    pack_lt hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have h0' : a0 + 256 = b0 + s0 + 256 * c1 := by omega
  have h1' : a1 + 255 + c1 = b1 + s1 + 256 * c2 := by omega
  have h2' : a2 + 255 + c2 = b2 + s2 + 256 * c3 := by omega
  have h3' : a3 + 255 + c3 = b3 + s3 + 256 * c4 := by omega
  have h4' : a4 + 255 + c4 = b4 + s4 + 256 * c5 := by omega
  have h5' : a5 + 255 + c5 = b5 + s5 + 256 * c6 := by omega
  have h6' : a6 + 255 + c6 = b6 + s6 + 256 * c7 := by omega
  have h7' : a7 + 255 + c7 = b7 + s7 + 256 * c8 := by omega
  have hadd : pack a0 a1 a2 a3 a4 a5 a6 a7 + base =
      pack b0 b1 b2 b3 b4 b5 b6 b7 + (pack s0 s1 s2 s3 s4 s5 s6 s7 + base * c8) := by
    unfold pack base
    omega
  have hsum : pack a0 a1 a2 a3 a4 a5 a6 a7 + base - pack b0 b1 b2 b3 b4 b5 b6 b7 =
      pack s0 s1 s2 s3 s4 s5 s6 s7 + base * c8 := by
    omega
  have hc8_lt : c8 < 2 := by
    have : base * c8 < base * 2 := by unfold base at *; omega
    exact Nat.lt_of_mul_lt_mul_left this
  constructor
  · rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs_lt]
  · split_ifs with hlt
    · have hc8 : c8 = 0 := by
        rcases (by omega : c8 = 0 ∨ c8 = 1) with rfl | rfl
        · rfl
        · omega
      simp [hc8]
    · have hc8 : c8 = 1 := by
        rcases (by omega : c8 = 0 ∨ c8 = 1) with rfl | rfl
        · omega
        · rfl
      simp [hc8]

/-! ### 8. `mul` and `mul_column` -/

theorem mul_column_sound (large : Compatible F) {val r0 r1 c0 c1 c2 : Nat}
    (hval : val < fieldBound)
    (hr0 : r0 < 256) (hr1 : r1 < 256)
    (hc0 : c0 < 256) (hc1 : c1 < 256) (hc2 : c2 < 256)
    (equal : (val : F) = (r0 : F) + 256 * (r1 : F) +
      65536 * ((c0 : F) + 256 * (c1 : F) + 65536 * (c2 : F))) :
    val = limb2 r0 r1 + 65536 * carry3 c0 c1 c2 ∧
    limb2 r0 r1 = val % 65536 ∧
    carry3 c0 c1 c2 = val / 65536 := by
  have hbound : limb2 r0 r1 + 65536 * carry3 c0 c1 c2 < fieldBound := by
    unfold limb2 carry3 fieldBound
    omega
  have hlifted : val = limb2 r0 r1 + 65536 * carry3 c0 c1 c2 := by
    apply natCast_inj large hval hbound
    unfold limb2 carry3
    push_cast
    linear_combination equal
  have hlimb : limb2 r0 r1 < 65536 := limb2_lt hr0 hr1
  refine ⟨hlifted, ?_, ?_⟩
  · rw [hlifted, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlimb]
  · rw [hlifted, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlimb, Nat.zero_add]

theorem mul_sound
    {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    {r00 r01 r10 r11 r20 r21 r30 r31 r40 r41 r50 r51 r60 r61 : Nat}
    {c00 c01 c02 c10 c11 c12 c20 c21 c22 c30 c31 c32 c40 c41 c42 c50 c51 c52 c60 c61 c62 : Nat}
    (hr00 : r00 < 256) (hr01 : r01 < 256) (hr10 : r10 < 256) (hr11 : r11 < 256)
    (hr20 : r20 < 256) (hr21 : r21 < 256) (hr30 : r30 < 256) (hr31 : r31 < 256)
    (hr40 : r40 < 256) (hr41 : r41 < 256) (hr50 : r50 < 256) (hr51 : r51 < 256)
    (hr60 : r60 < 256) (hr61 : r61 < 256) (hc60 : c60 < 256) (hc61 : c61 < 256)
    (col0 : limb2 a0 a1 * limb2 b0 b1 = limb2 r00 r01 + 65536 * carry3 c00 c01 c02)
    (col1 : limb2 a0 a1 * limb2 b2 b3 + limb2 a2 a3 * limb2 b0 b1 + carry3 c00 c01 c02 =
      limb2 r10 r11 + 65536 * carry3 c10 c11 c12)
    (col2 : limb2 a0 a1 * limb2 b4 b5 + limb2 a2 a3 * limb2 b2 b3 + limb2 a4 a5 * limb2 b0 b1 +
      carry3 c10 c11 c12 = limb2 r20 r21 + 65536 * carry3 c20 c21 c22)
    (col3 : limb2 a0 a1 * limb2 b6 b7 + limb2 a2 a3 * limb2 b4 b5 + limb2 a4 a5 * limb2 b2 b3 +
      limb2 a6 a7 * limb2 b0 b1 + carry3 c20 c21 c22 =
      limb2 r30 r31 + 65536 * carry3 c30 c31 c32)
    (col4 : limb2 a2 a3 * limb2 b6 b7 + limb2 a4 a5 * limb2 b4 b5 + limb2 a6 a7 * limb2 b2 b3 +
      carry3 c30 c31 c32 = limb2 r40 r41 + 65536 * carry3 c40 c41 c42)
    (col5 : limb2 a4 a5 * limb2 b6 b7 + limb2 a6 a7 * limb2 b4 b5 + carry3 c40 c41 c42 =
      limb2 r50 r51 + 65536 * carry3 c50 c51 c52)
    (col6 : limb2 a6 a7 * limb2 b6 b7 + carry3 c50 c51 c52 =
      limb2 r60 r61 + 65536 * carry3 c60 c61 c62)
    (hc62 : c62 = 0) :
    let a := pack a0 a1 a2 a3 a4 a5 a6 a7
    let b := pack b0 b1 b2 b3 b4 b5 b6 b7
    let lo := pack r00 r01 r10 r11 r20 r21 r30 r31
    let hi := pack r40 r41 r50 r51 r60 r61 c60 c61
    a * b = lo + base * hi ∧
    lo = (a * b) % base ∧
    hi = (a * b) / base ∧
    hi < base := by
  dsimp only
  have hlo_lt : pack r00 r01 r10 r11 r20 r21 r30 r31 < base :=
    pack_lt hr00 hr01 hr10 hr11 hr20 hr21 hr30 hr31
  have hhi_lt : pack r40 r41 r50 r51 r60 r61 c60 c61 < base :=
    pack_lt hr40 hr41 hr50 hr51 hr60 hr61 hc60 hc61
  have hprod : pack a0 a1 a2 a3 a4 a5 a6 a7 * pack b0 b1 b2 b3 b4 b5 b6 b7 =
      pack r00 r01 r10 r11 r20 r21 r30 r31 +
      base * pack r40 r41 r50 r51 r60 r61 c60 c61 := by
    subst hc62
    have h0' : (limb2 a0 a1 : Int) * limb2 b0 b1 = limb2 r00 r01 + 65536 * carry3 c00 c01 c02 := by exact_mod_cast col0
    have h1' : (limb2 a0 a1 : Int) * limb2 b2 b3 + limb2 a2 a3 * limb2 b0 b1 + carry3 c00 c01 c02 =
      limb2 r10 r11 + 65536 * carry3 c10 c11 c12 := by exact_mod_cast col1
    have h2' : (limb2 a0 a1 : Int) * limb2 b4 b5 + limb2 a2 a3 * limb2 b2 b3 + limb2 a4 a5 * limb2 b0 b1 +
      carry3 c10 c11 c12 = limb2 r20 r21 + 65536 * carry3 c20 c21 c22 := by exact_mod_cast col2
    have h3' : (limb2 a0 a1 : Int) * limb2 b6 b7 + limb2 a2 a3 * limb2 b4 b5 + limb2 a4 a5 * limb2 b2 b3 +
      limb2 a6 a7 * limb2 b0 b1 + carry3 c20 c21 c22 =
      limb2 r30 r31 + 65536 * carry3 c30 c31 c32 := by exact_mod_cast col3
    have h4' : (limb2 a2 a3 : Int) * limb2 b6 b7 + limb2 a4 a5 * limb2 b4 b5 + limb2 a6 a7 * limb2 b2 b3 +
      carry3 c30 c31 c32 = limb2 r40 r41 + 65536 * carry3 c40 c41 c42 := by exact_mod_cast col4
    have h5' : (limb2 a4 a5 : Int) * limb2 b6 b7 + limb2 a6 a7 * limb2 b4 b5 + carry3 c40 c41 c42 =
      limb2 r50 r51 + 65536 * carry3 c50 c51 c52 := by exact_mod_cast col5
    have h6' : (limb2 a6 a7 : Int) * limb2 b6 b7 + carry3 c50 c51 c52 =
      limb2 r60 r61 + 65536 * carry3 c60 c61 0 := by exact_mod_cast col6
    have hint : (pack a0 a1 a2 a3 a4 a5 a6 a7 : Int) * pack b0 b1 b2 b3 b4 b5 b6 b7 =
        pack r00 r01 r10 r11 r20 r21 r30 r31 +
        base * pack r40 r41 r50 r51 r60 r61 c60 c61 := by
      unfold pack limb2 carry3 base at *
      push_cast at *
      linear_combination
        h0' + 65536 * h1' + 4294967296 * h2' + 281474976710656 * h3' +
        18446744073709551616 * h4' + 1208925819614629174706176 * h5' +
        79228162514264337593543950336 * h6'
    exact_mod_cast hint
  refine ⟨hprod, ?_, ?_, hhi_lt⟩
  · rw [hprod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo_lt]
  · rw [hprod, Nat.add_mul_div_left _ _ (by unfold base; omega),
        Nat.div_eq_of_lt hlo_lt, Nat.zero_add]

/-! ### 9, 10, 11. `and`, `or`, `xor` -/

theorem bitwise_zero_left {f : Bool → Bool → Bool} (_hff : f false false = false) (y : Nat) :
    Nat.bitwise f 0 y = if f false true then y else 0 := by
  rw [Nat.bitwise]
  simp

theorem bitwise_zero_right {f : Bool → Bool → Bool} (_hff : f false false = false) (x : Nat) :
    Nat.bitwise f x 0 = if f true false then x else 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Nat.bitwise]; simp
  · rw [Nat.bitwise]; simp [hx]

theorem bitwise_zero_zero {f : Bool → Bool → Bool} (_hff : f false false = false) :
    Nat.bitwise f 0 0 = 0 := by
  rw [Nat.bitwise]; simp

theorem bitwise_bit {f : Bool → Bool → Bool} (hff : f false false = false)
    {a b : Nat} (ha : a < 2) (hb : b < 2) :
    Nat.bitwise f a b = if f (decide (a = 1)) (decide (b = 1)) then 1 else 0 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · simp [bitwise_zero_zero hff, hff]
  · simp [bitwise_zero_left hff]
  · simp [bitwise_zero_right hff]
  · rw [Nat.bitwise]; dsimp only; simp [bitwise_zero_zero hff]

theorem bitwise_add_mul_two {f : Bool → Bool → Bool} (hff : f false false = false)
    {a b : Nat} (ha : a < 2) (hb : b < 2) (x y : Nat) :
    Nat.bitwise f (a + 2 * x) (b + 2 * y) = Nat.bitwise f a b + 2 * Nat.bitwise f x y := by
  rw [bitwise_bit hff ha hb]
  rcases eq_or_ne (a + 2 * x) 0 with hax | hax
  · have ha0 : a = 0 := by omega
    have hx0 : x = 0 := by omega
    subst ha0; subst hx0
    rw [hax, bitwise_zero_left hff, bitwise_zero_left hff]
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · simp [hff]
    · simp; split_ifs <;> omega
  · rcases eq_or_ne (b + 2 * y) 0 with hby | hby
    · have hb0 : b = 0 := by omega
      have hy0 : y = 0 := by omega
      subst hb0; subst hy0
      rw [hby, bitwise_zero_right hff, bitwise_zero_right hff]
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · simp [hff]
      · simp; split_ifs <;> omega
    · conv_lhs => rw [Nat.bitwise]
      dsimp only
      have hdivx : (a + 2 * x) / 2 = x := by omega
      have hdivy : (b + 2 * y) / 2 = y := by omega
      have hmodx : ((a + 2 * x) % 2 = 1) ↔ (a = 1) := by omega
      have hmody : ((b + 2 * y) % 2 = 1) ↔ (b = 1) := by omega
      have hdecx : decide ((a + 2 * x) % 2 = 1) = decide (a = 1) := decide_eq_decide.mpr hmodx
      have hdecy : decide ((b + 2 * y) % 2 = 1) = decide (b = 1) := decide_eq_decide.mpr hmody
      simp only [hax, hby, ↓reduceIte, hdivx, hdivy, hdecx, hdecy]
      split_ifs <;> omega

theorem bitwise_add_mul_two_pow {f : Bool → Bool → Bool} (hff : f false false = false)
    (k : Nat) : ∀ {a b : Nat}, a < 2^k → b < 2^k → ∀ (x y : Nat),
      Nat.bitwise f (a + 2^k * x) (b + 2^k * y) = Nat.bitwise f a b + 2^k * Nat.bitwise f x y := by
  induction k with
  | zero =>
      intro a b ha hb x y
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst ha0; subst hb0
      simp [bitwise_zero_zero hff]
  | succ k ih =>
      intro a b ha hb x y
      have hmad_a : a % 2 + 2 * (a / 2) = a := Nat.mod_add_div a 2
      have hmad_b : b % 2 + 2 * (b / 2) = b := Nat.mod_add_div b 2
      have ha' : a % 2 + 2 * (a / 2 + 2^k * x) = a + 2^(k + 1) * x := by
        calc a % 2 + 2 * (a / 2 + 2^k * x)
          _ = (a % 2 + 2 * (a / 2)) + 2^k * 2 * x := by ring
          _ = a + 2^(k + 1) * x := by rw [hmad_a, Nat.pow_succ]
      have hb' : b % 2 + 2 * (b / 2 + 2^k * y) = b + 2^(k + 1) * y := by
        calc b % 2 + 2 * (b / 2 + 2^k * y)
          _ = (b % 2 + 2 * (b / 2)) + 2^k * 2 * y := by ring
          _ = b + 2^(k + 1) * y := by rw [hmad_b, Nat.pow_succ]
      have ha_div : a / 2 < 2^k := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [Nat.pow_succ] at ha; omega
      have hb_div : b / 2 < 2^k := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [Nat.pow_succ] at hb; omega
      have h1 := bitwise_add_mul_two hff (a := a % 2) (b := b % 2) (by omega) (by omega)
        (a / 2 + 2^k * x) (b / 2 + 2^k * y)
      have h2 := ih ha_div hb_div x y
      have h3 := bitwise_add_mul_two hff (a := a % 2) (b := b % 2) (by omega) (by omega) (a / 2) (b / 2)
      rw [hmad_a, hmad_b] at h3
      rw [← ha', ← hb', h1, h2, h3, Nat.pow_succ]
      ring

theorem bitwise_lt_two_pow {f : Bool → Bool → Bool} (hff : f false false = false) :
    ∀ (k : Nat) {a b : Nat}, a < 2^k → b < 2^k → Nat.bitwise f a b < 2^k := by
  intro k a b ha hb
  induction k generalizing a b with
  | zero =>
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst ha0; subst hb0; simp [bitwise_zero_zero hff]
  | succ k ih =>
      have ha_div : a / 2 < 2^k := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [Nat.pow_succ] at ha; omega
      have hb_div : b / 2 < 2^k := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [Nat.pow_succ] at hb; omega
      have h3 := bitwise_add_mul_two hff (a := a % 2) (b := b % 2) (by omega) (by omega) (a / 2) (b / 2)
      rw [Nat.mod_add_div, Nat.mod_add_div] at h3
      have hrec := ih ha_div hb_div
      have hmod : Nat.bitwise f (a % 2) (b % 2) < 2 := by
        rw [bitwise_bit hff (by omega) (by omega)]
        split_ifs <;> omega
      rw [h3, Nat.pow_succ]
      omega

theorem bitwise_pack {f : Bool → Bool → Bool} (hff : f false false = false)
    {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (_ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (_hb7 : b7 < 256) :
    pack (Nat.bitwise f a0 b0) (Nat.bitwise f a1 b1) (Nat.bitwise f a2 b2) (Nat.bitwise f a3 b3)
      (Nat.bitwise f a4 b4) (Nat.bitwise f a5 b5) (Nat.bitwise f a6 b6) (Nat.bitwise f a7 b7) =
      Nat.bitwise f (pack a0 a1 a2 a3 a4 a5 a6 a7) (pack b0 b1 b2 b3 b4 b5 b6 b7) := by
  have step : ∀ {x y : Nat}, x < 256 → y < 256 → ∀ u v : Nat,
      Nat.bitwise f (x + 256 * u) (y + 256 * v) = Nat.bitwise f x y + 256 * Nat.bitwise f u v := by
    intro x y hx hy u v
    simpa using bitwise_add_mul_two_pow hff 8 (by simpa using hx) (by simpa using hy) u v
  have hrew : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : Nat,
      pack x0 x1 x2 x3 x4 x5 x6 x7 =
        x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * (x4 + 256 * (x5 + 256 * (x6 + 256 * x7)))))) := by
    intros; unfold pack; ring
  rw [hrew a0, hrew b0, hrew (Nat.bitwise f a0 b0)]
  rw [step ha0 hb0, step ha1 hb1, step ha2 hb2, step ha3 hb3,
      step ha4 hb4, step ha5 hb5, step ha6 hb6]

theorem and_sound (large : Compatible F)
    {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) :
    ((a0 : F) + (b0 : F) - ((Nat.xor a0 b0 : Nat) : F)) / 2 = ((Nat.land a0 b0 : Nat) : F) ∧
    pack (Nat.land a0 b0) (Nat.land a1 b1) (Nat.land a2 b2) (Nat.land a3 b3)
      (Nat.land a4 b4) (Nat.land a5 b5) (Nat.land a6 b6) (Nat.land a7 b7) =
      Nat.land (pack a0 a1 a2 a3 a4 a5 a6 a7) (pack b0 b1 b2 b3 b4 b5 b6 b7) := by
  constructor
  · have h := U8.and_field (two_ne_zero large) (BitVec.ofNat 8 a0) (BitVec.ofNat 8 b0)
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt hb0] using h
  · exact bitwise_pack rfl ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7

theorem or_sound (large : Compatible F)
    {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) :
    ((a0 : F) + (b0 : F) + ((Nat.xor a0 b0 : Nat) : F)) / 2 = ((Nat.lor a0 b0 : Nat) : F) ∧
    pack (Nat.lor a0 b0) (Nat.lor a1 b1) (Nat.lor a2 b2) (Nat.lor a3 b3)
      (Nat.lor a4 b4) (Nat.lor a5 b5) (Nat.lor a6 b6) (Nat.lor a7 b7) =
      Nat.lor (pack a0 a1 a2 a3 a4 a5 a6 a7) (pack b0 b1 b2 b3 b4 b5 b6 b7) := by
  constructor
  · have h := U8.or_field (two_ne_zero large) (BitVec.ofNat 8 a0) (BitVec.ofNat 8 b0)
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt hb0] using h
  · exact bitwise_pack rfl ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7

theorem xor_sound
    {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) :
    pack (Nat.xor a0 b0) (Nat.xor a1 b1) (Nat.xor a2 b2) (Nat.xor a3 b3)
      (Nat.xor a4 b4) (Nat.xor a5 b5) (Nat.xor a6 b6) (Nat.xor a7 b7) =
      Nat.xor (pack a0 a1 a2 a3 a4 a5 a6 a7) (pack b0 b1 b2 b3 b4 b5 b6 b7) :=
  bitwise_pack rfl ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7

/-! ### 12. `from_field` -/

theorem from_field_sound (large : Compatible F) {value : F}
    {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256)
    (topZero : (b7 : F) = 0)
    (recomposed : (b0 : F) + 256 * (b1 : F) + 65536 * (b2 : F) + 16777216 * (b3 : F) +
      4294967296 * (b4 : F) + 1099511627776 * (b5 : F) + 281474976710656 * (b6 : F) = value) :
    b7 = 0 ∧
    pack b0 b1 b2 b3 b4 b5 b6 b7 < fieldBound ∧
    ((pack b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : F) = value := by
  have hb7 : b7 = 0 := byte_cast_inj large h7 (by omega) (by simpa using topZero)
  obtain ⟨hlt, hcast⟩ := to_field_sound large h0 h1 h2 h3 h4 h5 h6 h7 topZero
  exact ⟨hb7, hlt, hcast.symm.trans recomposed⟩

theorem from_field_unique (large : Compatible F) {n : Nat} (hn : n < fieldBound)
    {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256)
    (topZero : (b7 : F) = 0)
    (recomposed : (b0 : F) + 256 * (b1 : F) + 65536 * (b2 : F) + 16777216 * (b3 : F) +
      4294967296 * (b4 : F) + 1099511627776 * (b5 : F) + 281474976710656 * (b6 : F) = (n : F)) :
    pack b0 b1 b2 b3 b4 b5 b6 b7 = n := by
  obtain ⟨_, hlt, hcast⟩ := from_field_sound large h0 h1 h2 h3 h4 h5 h6 h7 topZero recomposed
  exact natCast_inj large hlt hn hcast

end Aiur.Library.U64
