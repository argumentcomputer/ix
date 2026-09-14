import Ix.Ixby

/-! Exact representation relations for the typed runtime. These laws concern
the pinned scalar semantics and concrete values, independently of the source
compiler's erasure and control-flow simulation obligations. -/

namespace Compilatrix.Ixby.Runtime.Representation

open Ix.Ixby

@[simp] theorem ctorId_beq_self (id : CtorId) : (id == id) = true := by
  cases id
  simp [BEq.beq, instBEqCtorId.beq]

/-- The three layouts used by `buildNumbers`; identities are supplied by the
actual program, rather than fixed global tags. The cached word is always the
low 32 bits of the exact Nat. A field box represents its canonical Nat value. -/
structure NumberLayout where
  cached : CtorId
  raw : CtorId
  field : CtorId

inductive Number (layout : NumberLayout) : Nat → Value → Prop
  | cached (n : Nat) : Number layout n
      (.ctor layout.cached #[.scalar (.nat n), .scalar (.word32 n.toUInt32)])
  | raw (n : Nat) : Number layout n (.ctor layout.raw #[.scalar (.nat n)])
  | field (f : Goldilocks) : Number layout f.val (.ctor layout.field #[.scalar (.field f)])

/-- Fin proof erasure may leave any of the three numeric representations. -/
def Field (layout : NumberLayout) (f : Goldilocks) (value : Value) : Prop :=
  Number layout f.val value

def Extension (f : ExtGoldilocks) (value : Value) : Prop :=
  value = .scalar (.extField f)

theorem cached_add (layout : NumberLayout) (a b : Nat) :
    Number layout (a + b) (.ctor layout.cached
      #[.scalar (.nat (a + b)), .scalar (.word32 (a.toUInt32 + b.toUInt32))]) := by
  simpa [Nat.toUInt32] using Number.cached (layout := layout) (a + b)

theorem cached_mul (layout : NumberLayout) (a b : Nat) :
    Number layout (a * b) (.ctor layout.cached
      #[.scalar (.nat (a * b)), .scalar (.word32 (a.toUInt32 * b.toUInt32))]) := by
  simpa [Nat.toUInt32] using Number.cached (layout := layout) (a * b)

/-- Native word subtraction preserves the cache only after the Nat underflow
branch has established the source subtraction is nonnegative. -/
theorem cached_sub (layout : NumberLayout) (a b : Nat) (ordered : b ≤ a) :
    Number layout (a - b) (.ctor layout.cached
      #[.scalar (.nat (a - b)), .scalar (.word32 (a.toUInt32 - b.toUInt32))]) := by
  simpa [Nat.toUInt32, UInt32.ofNat_sub ordered] using Number.cached (layout := layout) (a - b)

theorem cached_sub_underflow (layout : NumberLayout) (a b : Nat) (underflow : a < b) :
    Number layout (a - b) (.ctor layout.cached #[.scalar (.nat 0), .scalar (.word32 0)]) := by
  simpa [Nat.sub_eq_zero_of_le (Nat.le_of_lt underflow)] using Number.cached (layout := layout) 0

/-- Each nibble step in `toWord` preserves the complete low-word value even
for naturals larger than the target word. -/
theorem toWord_nibble (n : Nat) (weight accumulator : UInt32) :
    (accumulator + (n % 16).toUInt32 * weight) +
      (n / 16).toUInt32 * (weight * 16) = accumulator + n.toUInt32 * weight := by
  have decomposition : (n % 16).toUInt32 + 16 * (n / 16).toUInt32 = n.toUInt32 := by
    simpa only [Nat.toUInt32, UInt32.ofNat_add, UInt32.ofNat_mul,
      show UInt32.ofNat 16 = (16 : UInt32) from by decide] using
      congrArg Nat.toUInt32 (Nat.mod_add_div n 16)
  have left_comm (a b c : UInt32) : a * (b * c) = b * (a * c) := by
    rw [← UInt32.mul_assoc, UInt32.mul_comm a b, UInt32.mul_assoc]
  calc
    _ = accumulator + ((n % 16).toUInt32 + 16 * (n / 16).toUInt32) * weight := by
      simp [UInt32.mul_add, UInt32.mul_comm, left_comm,
        UInt32.add_assoc]
    _ = _ := by rw [decomposition]

/-- The corresponding exact-Nat accumulator step in `fromWordLoop`. -/
theorem fromWord_nibble (word : UInt32) (weight accumulator : Nat) :
    accumulator + (word.toNat % 16) * weight +
      (word.toNat / 16) * (weight * 16) = accumulator + word.toNat * weight := by
  calc
    _ = accumulator + (word.toNat % 16 + 16 * (word.toNat / 16)) * weight := by
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.add_assoc]
    _ = _ := by rw [Nat.mod_add_div]

/-- The external Stage2 result observation, including an empty successful
claim. Erased rejection is distinct from every bytes scalar. -/
def claimResult : Option (Array UInt8) → Value
  | none => .erased
  | some bytes => .scalar (.bytes bytes)

theorem claimResult_injective : Function.Injective claimResult := by
  intro a b h
  cases a <;> cases b <;> simp_all [claimResult]

@[simp] theorem claimResult_success_ne_rejection (bytes : Array UInt8) :
    claimResult (some bytes) ≠ claimResult none := by simp [claimResult]

/-- Byte count is exact even when the encoded Nat does not fit. -/
@[simp] theorem bytesLE_size (width n : Nat) : (bytesLE width n).size = width := by
  simp [bytesLE]

private theorem bytesLE_succ (width n : Nat) :
    bytesLE (width + 1) n = #[n.toUInt8] ++ bytesLE width (n / 256) := by
  unfold bytesLE
  rw [Array.range_succ_eq_map, Array.map_append, Array.map_map]
  simp only [Array.map_singleton, Nat.mul_zero, Nat.shiftRight_zero]
  congr 1
  apply Array.map_congr_left
  intro i _
  change (n >>> (8 * (i + 1))).toUInt8 = ((n / 256) >>> (8 * i)).toUInt8
  rw [Nat.mul_add, Nat.mul_one, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.pow_add, Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm 256]

/-- Universal little-endian roundtrip, explicitly retaining truncation. -/
theorem natOfBytesLE_bytesLE (width n : Nat) :
    natOfBytesLE (bytesLE width n) = n % 256 ^ width := by
  induction width generalizing n with
  | zero => simp [bytesLE, natOfBytesLE, Nat.mod_one]
  | succ width ih =>
    rw [bytesLE_succ]
    simp only [natOfBytesLE, Array.toList_append,
      List.singleton_append, List.foldr_cons]
    change n.toUInt8.toNat + 256 * natOfBytesLE (bytesLE width (n / 256)) = _
    rw [ih]
    simp only [Nat.toUInt8, UInt8.toNat_ofNat']
    change n % 256 + 256 * (n / 256 % 256 ^ width) = n % 256 ^ (width + 1)
    rw [Nat.pow_succ 256 width, Nat.mul_comm (256 ^ width) 256, Nat.mod_mul]

theorem natOfBytesLE_bytesLE_of_lt {width n : Nat} (fits : n < 256 ^ width) :
    natOfBytesLE (bytesLE width n) = n := by
  rw [natOfBytesLE_bytesLE, Nat.mod_eq_of_lt fits]

/-- Fixed-width slices agree with the very same byte helper used by the
reference `fieldToBytes` and `bytesToWord32` primitives. -/
theorem bytesLE_extract {width start count n : Nat} (fits : start + count ≤ width) :
    (bytesLE width n).extract start (start + count) =
      bytesLE count (n / 256 ^ start) := by
  apply Array.ext
  · simp [Array.size_extract, bytesLE_size]; omega
  · intro i hi hj
    simp only [Array.getElem_extract, bytesLE, Array.getElem_map, Array.getElem_range]
    congr 1
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
    rw [Nat.mul_add, Nat.pow_add]
    have power : 2 ^ (8 * start) = 256 ^ start := by rw [Nat.pow_mul]
    rw [power]

theorem word_bytes_roundtrip (word : UInt32) :
    natOfBytesLE (bytesLE 4 word.toNat) = word.toNat := by
  apply natOfBytesLE_bytesLE_of_lt
  exact word.toNat_lt

theorem field_bytes_roundtrip (field : Goldilocks) :
    natOfBytesLE (bytesLE 8 field.val) = field.val := by
  apply natOfBytesLE_bytesLE_of_lt
  have : field.val < 18446744069414584321 := field.isLt
  omega

/-- Reconstructing a canonical field's exact Nat from two words does not
perform modular field arithmetic. -/
theorem field_natural_words (field : Goldilocks) :
    (natOfBytesLE ((bytesLE 8 field.val).extract 0 4)).toUInt32.toNat +
      (natOfBytesLE ((bytesLE 8 field.val).extract 4 8)).toUInt32.toNat * 2 ^ 32 =
      field.val := by
  rw [bytesLE_extract (by decide : 0 + 4 ≤ 8),
    bytesLE_extract (by decide : 4 + 4 ≤ 8)]
  simp only [natOfBytesLE_bytesLE, Nat.pow_zero, Nat.div_one,
    Nat.toUInt32, UInt32.toNat_ofNat']
  have : field.val < 18446744069414584321 := field.isLt
  omega

/-- `fieldFromNatural` first reduces modulo p, then converts its two words.
This identity accounts for both native field operations in that lowering. -/
theorem field_from_natural_words (n : Nat) :
    (Goldilocks.reduce (n % goldilocksModulus).toUInt32.toNat).add
      ((Goldilocks.reduce ((n % goldilocksModulus) / 2 ^ 32).toUInt32.toNat).mul
        (Goldilocks.reduce (2 ^ 32))) = Goldilocks.reduce n := by
  apply Fin.ext
  simp only [Goldilocks.add, Goldilocks.mul, Goldilocks.reduce_val,
    Nat.toUInt32, UInt32.toNat_ofNat']
  have bound : n % goldilocksModulus < 18446744069414584321 :=
    Nat.mod_lt n (by decide : 0 < goldilocksModulus)
  have lowBound := Nat.mod_lt (n % goldilocksModulus) (by decide : 0 < 2 ^ 32)
  have highBound : n % goldilocksModulus / 2 ^ 32 < 2 ^ 32 := by omega
  have lowField : n % goldilocksModulus % 2 ^ 32 < goldilocksModulus := by
    unfold goldilocksModulus; omega
  have highField : n % goldilocksModulus / 2 ^ 32 < goldilocksModulus := by
    unfold goldilocksModulus; omega
  simp only [Nat.mod_eq_of_lt highBound,
    Nat.mod_eq_of_lt lowField, Nat.mod_eq_of_lt highField]
  simp only [goldilocksModulus, Nat.reducePow, Nat.reduceMod] at *
  omega

theorem field_comparison_exact (a b : Goldilocks) :
    (a == b) = (a.val == b.val) := by
  apply Bool.eq_iff_iff.mpr
  simp [Fin.ext_iff]

/-- Arbitrary Nat operands in mixed comparisons must remain unreduced. -/
theorem mixed_comparison_exact (a : Goldilocks) (n : Nat) :
    (a.val == n) = true ↔ a.val = n := by simp

theorem mixed_comparison_above_modulus (a : Goldilocks) {n : Nat}
    (large : goldilocksModulus ≤ n) : (a.val == n) = false := by
  have := a.isLt
  simp only [beq_eq_false_iff_ne]
  omega

end Compilatrix.Ixby.Runtime.Representation
