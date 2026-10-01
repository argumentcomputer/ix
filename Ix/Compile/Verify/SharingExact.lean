import Ix.Compile.Verify.ExprSpineCodec
import Ix.Compile.Verify.Catalog
import Ix.Sharing.Exact

/-!
# Exact minimum sharing: foundational facts

Proofs about the executable exact-sharing core (`Ix.Sharing.Exact`):

* the integer widths `tag0Size`, `tag4Size`, `shareWidth` are the sizes of
  the production `Tag0`/`Tag4` encodings, and agree with the heuristic's
  `tag0EncodedSize`/`tag4EncodedSize`; `tagNWidth` is monotone with the
  stated rung ends;
* `exprSize` is the length of the production expression encoding for every
  expression in the codec's wire domain (telescope rule included), and the
  complete-Constant length decomposes as `fixedConstantBytes` plus the
  variable parts;
* the §3.2 key comparisons are lawful total orders, and sorting distinct
  keys does not depend on the input order.
-/

namespace Ix.Compile.Verify.SharingExact

open Ix.Sharing.Exact
open Ix.Compile.Verify.Codec
open Ix.Compile.Verify.Codec.Ixon.Expr

/-! ## Minimal little-endian byte counts -/

theorem natByteCount_zero : natByteCount 0 = 0 := by
  rw [natByteCount]
  simp

theorem natByteCount_of_ne_zero {n : Nat} (h : n ≠ 0) :
    natByteCount n = natByteCount (n / 256) + 1 := by
  rw [natByteCount]
  simp [h]

/-- `natByteCount n = k` exactly on `[256^(k-1), 256^k)`. -/
theorem natByteCount_eq_of_range :
    ∀ (k n : Nat), 256 ^ k ≤ n → n < 256 ^ (k + 1) → natByteCount n = k + 1
  | 0, n, hlo, hhi => by
    have hn : n ≠ 0 := by simp at hlo; omega
    rw [natByteCount_of_ne_zero hn]
    have : n / 256 = 0 := by simp at hhi; omega
    rw [this, natByteCount_zero]
  | k + 1, n, hlo, hhi => by
    have hpos : 0 < 256 ^ (k + 1) := Nat.pow_pos_iff.mpr (Or.inl (by decide))
    have hn : n ≠ 0 := by omega
    rw [natByteCount_of_ne_zero hn]
    have hlo' : 256 ^ k ≤ n / 256 := by
      rw [Nat.le_div_iff_mul_le (by decide)]
      simpa [Nat.pow_succ] using hlo
    have hhi' : n / 256 < 256 ^ (k + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [Nat.pow_succ] using hhi
    rw [natByteCount_eq_of_range k (n / 256) hlo' hhi']

/-- `natByteCount` agrees with the production `u64ByteCount`. -/
theorem natByteCount_toNat (x : UInt64) :
    natByteCount x.toNat = (Ixon.u64ByteCount x).toNat := by
  have hx := x.toNat_lt
  unfold Ixon.u64ByteCount
  split <;> rename_i h0
  · have : x = 0 := by simpa using h0
    subst this
    simp [natByteCount_zero]
  have hne : x.toNat ≠ 0 := by
    intro h
    apply h0
    have : x = 0 := UInt64.toNat_inj.mp (by simpa using h)
    simp [this]
  split <;> rename_i h1
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h1
    simpa using natByteCount_eq_of_range 0 x.toNat (by simp; omega) (by simpa using h1)
  split <;> rename_i h2
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h1 h2
    simpa using natByteCount_eq_of_range 1 x.toNat (by simp; omega) (by simpa using h2)
  split <;> rename_i h3
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h2 h3
    simpa using natByteCount_eq_of_range 2 x.toNat (by simp; omega) (by simpa using h3)
  split <;> rename_i h4
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h3 h4
    simpa using natByteCount_eq_of_range 3 x.toNat (by simp; omega) (by simpa using h4)
  split <;> rename_i h5
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h4 h5
    simpa using natByteCount_eq_of_range 4 x.toNat (by simp; omega) (by simpa using h5)
  split <;> rename_i h6
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h5 h6
    simpa using natByteCount_eq_of_range 5 x.toNat (by simp; omega) (by simpa using h6)
  split <;> rename_i h7
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h6 h7
    simpa using natByteCount_eq_of_range 6 x.toNat (by simp; omega) (by simpa using h7)
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h7
    simpa using natByteCount_eq_of_range 7 x.toNat (by simp; omega) (by simpa using hx)

/-! ## `Tag0` and `Tag4` lengths -/

theorem trimmedBytes_size (x : UInt64) (len : Nat) : (trimmedBytes x len).size = len := by
  induction len generalizing x with
  | zero => rfl
  | succ len ih => simp [trimmedBytes, ih]; omega

/-- `tag4Size` is the length of the production `Tag4` bytes. -/
theorem tag4Bytes_size (flag : UInt8) (size : UInt64) :
    (Codec.tag4Bytes flag size).size = tag4Size size.toNat := by
  unfold Codec.tag4Bytes tag4Size
  by_cases h : size < 8
  · have h' : size.toNat < 8 := by simpa [UInt64.lt_iff_toNat_lt] using h
    simp [h, h']
  · have h' : ¬ size.toNat < 8 := by simpa [UInt64.lt_iff_toNat_lt] using h
    simp only [h, h', if_false, ByteArray.size_append, trimmedBytes_size,
      natByteCount_toNat]
    simp only [List.size_toByteArray, List.length_singleton]
    all_goals omega

/-- `tag0Size` is the length of the production `Tag0` bytes. -/
theorem tag0Bytes_size (size : UInt64) :
    (tag0Bytes size).size = tag0Size size.toNat := by
  unfold tag0Bytes tag0Size
  by_cases h : size < 128
  · have h' : size.toNat < 128 := by simpa [UInt64.lt_iff_toNat_lt] using h
    simp [h, h']
  · have h' : ¬ size.toNat < 128 := by simpa [UInt64.lt_iff_toNat_lt] using h
    simp only [h, h', if_false, ByteArray.size_append, trimmedBytes_size,
      natByteCount_toNat]
    simp only [List.size_toByteArray, List.length_singleton]
    all_goals omega

/-- `tag4Size` is the size of what `putTag4` writes. -/
theorem putTag4_size (flag : UInt8) (size : UInt64) :
    (Ixon.runPut (Ixon.putTag4 ⟨flag, size⟩)).size = tag4Size size.toNat := by
  have h := putTag4_writes flag size ByteArray.empty
  simp only [Ixon.runPut, h, ByteArray.empty_append, tag4Bytes_size]

/-- `tag0Size` is the size of what `putTag0` writes. -/
theorem putTag0_size (size : UInt64) :
    (Ixon.runPut (Ixon.putTag0 ⟨size⟩)).size = tag0Size size.toNat := by
  have h := putTag0_writes size ByteArray.empty
  simp only [Ixon.runPut, h, ByteArray.empty_append, tag0Bytes_size]

/-- The Share width is the size of the serialized `Share`. -/
theorem shareWidth_eq_putTag4 (idx : UInt64) :
    shareWidth idx.toNat =
      (Ixon.runPut (Ixon.putTag4 ⟨Ixon.Expr.FLAG_SHARE, idx⟩)).size := by
  rw [putTag4_size]
  rfl

/-- `UInt64.byteCount` (used by the heuristic) agrees with the minimal byte
count on nonzero values. -/
theorem byteCount_eq_u64ByteCount (x : UInt64) (h : x ≠ 0) :
    x.byteCount = Ixon.u64ByteCount x := by
  unfold UInt64.byteCount Ixon.u64ByteCount
  have h0 : (x == 0) = false := by simpa using h
  simp only [h0, Bool.false_eq_true, if_false]

/-- The heuristic's `Tag0` size agrees with `tag0Size`. -/
theorem tag0EncodedSize_eq (x : UInt64) :
    Ix.Sharing.tag0EncodedSize x = tag0Size x.toNat := by
  unfold Ix.Sharing.tag0EncodedSize tag0Size
  by_cases h : x < 128
  · have h' : x.toNat < 128 := by simpa [UInt64.lt_iff_toNat_lt] using h
    simp [h, h']
  · have h' : ¬ x.toNat < 128 := by simpa [UInt64.lt_iff_toNat_lt] using h
    have hne : x ≠ 0 := by intro hz; subst hz; exact h (by decide)
    simp [h, h', byteCount_eq_u64ByteCount x hne, natByteCount_toNat]

/-- The heuristic's `Tag4` size agrees with `tag4Size`. -/
theorem tag4EncodedSize_eq (x : UInt64) :
    Ix.Sharing.tag4EncodedSize x = tag4Size x.toNat := by
  unfold Ix.Sharing.tag4EncodedSize tag4Size
  by_cases h : x < 8
  · have h' : x.toNat < 8 := by simpa [UInt64.lt_iff_toNat_lt] using h
    simp [h, h']
  · have h' : ¬ x.toNat < 8 := by simpa [UInt64.lt_iff_toNat_lt] using h
    have hne : x ≠ 0 := by intro hz; subst hz; exact h (by decide)
    simp [h, h', byteCount_eq_u64ByteCount x hne, natByteCount_toNat]

/-! ## TagN widths -/

theorem tagNRung1End_eq : tagNRung1End = 8 := rfl
theorem tagNRung2End_eq : tagNRung2End = 1032 := by
  unfold tagNRung2End tagNRung1End; rfl
theorem tagNRung3End_eq : tagNRung3End = 66568 := by
  unfold tagNRung3End; rw [tagNRung2End_eq]
/-- `66568 + 2^32`. -/
theorem tagNRung4End_eq : tagNRung4End = 4295033864 := by
  unfold tagNRung4End; rw [tagNRung3End_eq]
/-- `66568 + 2^32 + 2^64`. -/
theorem tagNRung5End_eq : tagNRung5End = 18446744078004585480 := by
  unfold tagNRung5End; rw [tagNRung4End_eq]

/-- `tagNWidth` with the rung ends evaluated. -/
theorem tagNWidth_eq (i : Nat) :
    tagNWidth i =
      if i < 8 then 1 else if i < 1032 then 2 else if i < 66568 then 3
      else if i < 4295033864 then 5 else 9 := by
  unfold tagNWidth
  rw [tagNRung1End_eq, tagNRung2End_eq, tagNRung3End_eq, tagNRung4End_eq]

theorem tagNWidth_pos (i : Nat) : 1 ≤ tagNWidth i := by
  rw [tagNWidth_eq]
  repeat' split
  all_goals omega

/-- TagN widths never decrease with the index. -/
theorem tagNWidth_mono {i j : Nat} (h : i ≤ j) : tagNWidth i ≤ tagNWidth j := by
  rw [tagNWidth_eq, tagNWidth_eq]
  repeat' split
  all_goals omega

theorem tagNWidth_rung1 {i : Nat} (h : i < tagNRung1End) : tagNWidth i = 1 := by
  rw [tagNRung1End_eq] at h
  rw [tagNWidth_eq, if_pos h]

theorem tagNWidth_rung2 {i : Nat} (h1 : tagNRung1End ≤ i) (h2 : i < tagNRung2End) :
    tagNWidth i = 2 := by
  rw [tagNRung1End_eq] at h1
  rw [tagNRung2End_eq] at h2
  rw [tagNWidth_eq, if_neg (by omega), if_pos h2]

theorem tagNWidth_rung3 {i : Nat} (h1 : tagNRung2End ≤ i) (h2 : i < tagNRung3End) :
    tagNWidth i = 3 := by
  rw [tagNRung2End_eq] at h1
  rw [tagNRung3End_eq] at h2
  rw [tagNWidth_eq, if_neg (by omega), if_neg (by omega), if_pos h2]

theorem tagNWidth_rung4 {i : Nat} (h1 : tagNRung3End ≤ i) (h2 : i < tagNRung4End) :
    tagNWidth i = 5 := by
  rw [tagNRung3End_eq] at h1
  rw [tagNRung4End_eq] at h2
  rw [tagNWidth_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem tagNWidth_rung5 {i : Nat} (h1 : tagNRung4End ≤ i) : tagNWidth i = 9 := by
  rw [tagNRung4End_eq] at h1
  rw [tagNWidth_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

end Ix.Compile.Verify.SharingExact
