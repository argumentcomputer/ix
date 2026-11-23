import IxCC.Rt.Rc.Classes
import IxCC.X86.ELFRodata

/-! # Contiguous Array, ByteArray, and LimbArray Cell Layout

Defines the physical cell layout for all three native contiguous array kinds in
IxCC, compatible with `IxCC.Rt.Rc.Gen` (71 size classes, RC header conventions)
and `IxCC.X86.ELFRodata` (immortal `.rodata` static cells):

```
offset  size   field
+0      u64    header = scan:u8 | cls:u8 | tag:u16 | rc:i32
+8      u64    size   (number of live elements or bytes)
+16     u64    cap    (element or byte capacity in payload)
+24     ...    payload:
                 - ArrayKind.boxed: cap tagged 64-bit Words  (scan = 0xFF, tag = 0x7F01)
                 - ArrayKind.bytes: cap packed raw bytes     (scan = 0,    tag = 0x7F02)
                 - ArrayKind.limbs: cap raw 64-bit UInt64s   (scan = 0,    tag = 0x7F03)
```

* `ArrayKind.boxed` (`scan = 0xFF`, `tag = 0x7F01`): elements are scanned during
  iterative `arr_dec` (the element count lives at `+8`, never colliding with
  constructor scan counts `0..254`).
* `ArrayKind.bytes` (`scan = 0`, `tag = 0x7F02`): unboxed packed byte buffer
  backing both `ByteArray` and UTF-8 `String` (DR4). Released in O(1) with zero
  child traversal.
* `ArrayKind.limbs` (`scan = 0`, `tag = 0x7F03`): unboxed 64-bit limb buffer
  backing `Array UInt64` and `BigNat` (`IxCC/docs/bignum-design.md`). Released
  in O(1) with zero child traversal.

Also provides the O(1) branch-minimal `classForFast` and `classWordsFast`
functions mirrored directly in Lir (`bsr64` + shifts) and proves exact agreement
with `Rt.Rc.classFor` and `Rt.Rc.classWords` across all 71 size classes. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open IxCC.Lir (Word)
open IxCC.Rt (header maxTag maxFields immortalRc)
open IxCC.Rt.Rc (dynamicHeader maxCount maxClass classWords classFor classBytes maxCellWords
  classWords_strictMono classWords_le_max classWords_small classFor_spec classFor_small
  header_scan header_class header_tag header_rc dynamicHeader_count)

/-! ## Array kinds and cell geometry -/

/-- The three native contiguous array representations. -/
inductive ArrayKind where
  /-- Boxed `Array α`: 64-bit tagged words, scanned by RC release (`scan = 0xFF`). -/
  | boxed
  /-- Unboxed `ByteArray` (and UTF-8 `String` backing): packed bytes (`scan = 0`). -/
  | bytes
  /-- Unboxed `Array UInt64` / `BigNat` limbs: raw 64-bit words (`scan = 0`). -/
  | limbs
  deriving DecidableEq, Repr, Inhabited

/-- Header tag for each array kind, matching `IxCC.X86.ELFRodata` and strictly
above `Rt.maxTag = 0x7EFF`. -/
def ArrayKind.tag : ArrayKind → Nat
  | .boxed => X86.ELFRodata.tagBoxedArray
  | .bytes => X86.ELFRodata.tagByteArray
  | .limbs => X86.ELFRodata.tagLimbArray

/-- Header scan byte for each array kind: `0xFF` for boxed arrays (count in `+8`),
`0` for unboxed `ByteArray` and `LimbArray` (O(1) release, no child scanning). -/
def ArrayKind.scan : ArrayKind → Nat
  | .boxed => X86.ELFRodata.scanBoxedArray
  | .bytes => 0
  | .limbs => 0

/-- Whether elements of this array kind are RC-tracked tagged words. -/
def ArrayKind.isBoxed : ArrayKind → Bool
  | .boxed => true
  | .bytes => false
  | .limbs => false

/-- Number of header/metadata words preceding payload: `header`, `size`, `cap`. -/
def arrayHeaderWords : Nat := 3

/-- Byte offset of the `size` field inside an array cell. -/
def arraySizeOffset : Nat := 8

/-- Byte offset of the `cap` field inside an array cell. -/
def arrayCapOffset : Nat := 16

/-- Byte offset of the payload start inside an array cell. -/
def arrayPayloadOffset : Nat := 24

/-- Minimum size class for any array cell (3 words = 24 bytes: header + size + cap). -/
def minArrayClass : Nat := 3

/-- Maximum element capacity for word-backed arrays (`boxed` and `limbs`). -/
def maxWordCap : Nat := maxCellWords - arrayHeaderWords

/-- Maximum byte capacity for `ByteArray` cells. -/
def maxByteCap : Nat := 8 * maxWordCap

/-- Total 64-bit words required by a word-backed array cell of capacity `cap`. -/
def wordArrayWords (cap : Nat) : Nat := arrayHeaderWords + cap

/-- Total 64-bit words required by a `ByteArray` cell of capacity `byteCap` bytes. -/
def byteArrayWords (byteCap : Nat) : Nat := arrayHeaderWords + (byteCap + 7) / 8

/-- Word element capacity provided by an array cell in size class `cls`. -/
def wordCapOfClass (cls : Nat) : Nat := classWords cls - arrayHeaderWords

/-- Byte capacity provided by a `ByteArray` cell in size class `cls`. -/
def byteCapOfClass (cls : Nat) : Nat := 8 * (classWords cls - arrayHeaderWords)

/-- Initial non-empty growth target for word-backed arrays. -/
def initWordGrowCap : Nat := 4

/-- Initial non-empty growth target for byte arrays. -/
def initByteGrowCap : Nat := 8

/-- Dynamic 64-bit header for a live array cell of kind `k`, size class `cls`,
with `refs` abstract references (`rc = refs - 1`). -/
def arrayHeader (k : ArrayKind) (cls refs : Nat) : Word :=
  dynamicHeader k.scan cls k.tag refs

/-- Immortal `.rodata` static header for an array cell of kind `k`
(`cls = 0`, `rc = INT32_MIN`). -/
def staticArrayHeader (k : ArrayKind) : Word :=
  header k.scan 0 k.tag immortalRc

/-! ## Tag, scan, and header compatibility proofs -/

theorem ArrayKind.tag_gt_maxTag (k : ArrayKind) : maxTag < k.tag := by
  cases k <;> decide

theorem ArrayKind.tag_lt (k : ArrayKind) : k.tag < 65536 := by
  cases k <;> decide

theorem ArrayKind.scan_lt (k : ArrayKind) : k.scan < 256 := by
  cases k <;> decide

theorem ArrayKind.tag_injective {k₁ k₂ : ArrayKind} (h : k₁.tag = k₂.tag) : k₁ = k₂ := by
  cases k₁ <;> cases k₂ <;> first | rfl | cases h

theorem ArrayKind.boxed_scan_gt_maxFields : maxFields < ArrayKind.boxed.scan := by
  decide

theorem staticArrayHeader_eq_elfRodata (k : ArrayKind) :
    staticArrayHeader k = X86.ELFRodata.staticHeader k.scan k.tag := by
  cases k <;> rfl

theorem arrayHeader_fields {k : ArrayKind} {cls refs : Nat}
    (hcls : cls ≤ maxClass) (hpos : 0 < refs) (hmax : refs ≤ maxCount) :
    ((arrayHeader k cls refs) &&& 0xFF).toNat = k.scan ∧
      (((arrayHeader k cls refs) >>> 8) &&& 0xFF).toNat = cls ∧
      (((arrayHeader k cls refs) >>> 16) &&& 0xFFFF).toNat = k.tag ∧
      ((arrayHeader k cls refs) >>> 32).toNat + 1 = refs := by
  have hs := k.scan_lt
  have ht := k.tag_lt
  have hc : cls < 256 := by unfold maxClass at hcls; omega
  have hrc : refs - 1 < 2 ^ 32 := by unfold maxCount at hmax; omega
  exact ⟨header_scan hs hc ht hrc,
    header_class hs hc ht hrc,
    header_tag hs hc ht hrc,
    dynamicHeader_count hs hc ht hpos hmax⟩

theorem staticArrayHeader_fields (k : ArrayKind) :
    ((staticArrayHeader k) &&& 0xFF).toNat = k.scan ∧
      (((staticArrayHeader k) >>> 8) &&& 0xFF).toNat = 0 ∧
      (((staticArrayHeader k) >>> 16) &&& 0xFFFF).toNat = k.tag ∧
      ((staticArrayHeader k) >>> 32).toNat = immortalRc := by
  rw [staticArrayHeader_eq_elfRodata]
  exact ⟨X86.ELFRodata.staticHeader_scan k.scan_lt k.tag_lt,
    X86.ELFRodata.staticHeader_cls k.scan_lt k.tag_lt,
    X86.ELFRodata.staticHeader_tag k.scan_lt k.tag_lt,
    X86.ELFRodata.staticHeader_rc k.scan_lt k.tag_lt⟩

theorem staticArrayHeader_rc_signed_neg (k : ArrayKind) :
    X86.Width.signedValue .w32 ((staticArrayHeader k) >>> 32) < 0 := by
  rw [staticArrayHeader_eq_elfRodata]
  exact X86.ELFRodata.staticHeader_rc_signed_neg k.scan_lt k.tag_lt

/-! ## Word/byte capacity arithmetic -/

theorem wordArrayWords_ge_three (cap : Nat) : 3 ≤ wordArrayWords cap := by
  unfold wordArrayWords arrayHeaderWords; omega

theorem wordArrayWords_le_max {cap : Nat} (h : cap ≤ maxWordCap) :
    wordArrayWords cap ≤ maxCellWords := by
  unfold wordArrayWords maxWordCap arrayHeaderWords at *
  have hm : maxCellWords = 2 ^ 26 := IxCC.Rt.Rc.maxCellWords_eq
  omega

theorem byteArrayWords_ge_three (byteCap : Nat) : 3 ≤ byteArrayWords byteCap := by
  unfold byteArrayWords arrayHeaderWords; omega

theorem byteArrayWords_le_max {byteCap : Nat} (h : byteCap ≤ maxByteCap) :
    byteArrayWords byteCap ≤ maxCellWords := by
  unfold byteArrayWords maxByteCap maxWordCap arrayHeaderWords at *
  have hm : maxCellWords = 2 ^ 26 := IxCC.Rt.Rc.maxCellWords_eq
  omega

theorem classWords_ge_three {c : Nat} (h1 : minArrayClass ≤ c) (h2 : c ≤ maxClass) :
    3 ≤ classWords c := by
  rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
  · decide
  · have hlt' := classWords_strictMono hlt h2
    have h3 : classWords minArrayClass = 3 := rfl
    omega

theorem wordCapOfClass_spec {cap cls : Nat}
    (h : classFor (wordArrayWords cap) = some cls) :
    minArrayClass ≤ cls ∧ cls ≤ maxClass ∧ cap ≤ wordCapOfClass cls ∧
      wordArrayWords (wordCapOfClass cls) = classWords cls := by
  obtain ⟨h1, h2, hfit, _⟩ := classFor_spec h
  have hge3 : 3 ≤ classWords cls := by
    have := wordArrayWords_ge_three cap
    omega
  have hcls3 : minArrayClass ≤ cls := by
    rcases Nat.lt_or_ge cls minArrayClass with hlt | hge
    · have hle : cls ≤ 2 := by unfold minArrayClass at hlt; omega
      rw [classWords_small (by omega)] at hge3
      omega
    · exact hge
  refine ⟨hcls3, h2, ?_, ?_⟩
  · unfold wordCapOfClass wordArrayWords arrayHeaderWords at *; omega
  · unfold wordCapOfClass wordArrayWords arrayHeaderWords at *; omega

theorem byteCapOfClass_spec {byteCap cls : Nat}
    (h : classFor (byteArrayWords byteCap) = some cls) :
    minArrayClass ≤ cls ∧ cls ≤ maxClass ∧ byteCap ≤ byteCapOfClass cls ∧
      byteArrayWords (byteCapOfClass cls) = classWords cls := by
  obtain ⟨h1, h2, hfit, _⟩ := classFor_spec h
  have hge3 : 3 ≤ classWords cls := by
    have := byteArrayWords_ge_three byteCap
    omega
  have hcls3 : minArrayClass ≤ cls := by
    rcases Nat.lt_or_ge cls minArrayClass with hlt | hge
    · have hle : cls ≤ 2 := by unfold minArrayClass at hlt; omega
      rw [classWords_small (by omega)] at hge3
      omega
    · exact hge
  refine ⟨hcls3, h2, ?_, ?_⟩
  · unfold byteCapOfClass byteArrayWords arrayHeaderWords at *; omega
  · unfold byteCapOfClass byteArrayWords arrayHeaderWords at *; omega

theorem arrayBytes_eq_classBytes {cls : Nat} (h1 : minArrayClass ≤ cls) (h2 : cls ≤ maxClass) :
    arrayPayloadOffset + 8 * wordCapOfClass cls = classBytes cls ∧
      arrayPayloadOffset + byteCapOfClass cls = classBytes cls := by
  have h3 := classWords_ge_three h1 h2
  unfold arrayPayloadOffset wordCapOfClass byteCapOfClass classBytes arrayHeaderWords
  omega

/-! ## Closed-form O(1) size-class arithmetic (exact mirror of Lir `bsr64` procs) -/

/-- O(1) shift-based `classWords`, mirroring the Lir `arr_class_words` procedure. -/
def classWordsFast (c : Nat) : Nat :=
  if c ≤ 32 then c
  else if c ≤ 56 then
    let k := c - 33
    (32 + (((k &&& 3) + 1) <<< 3)) <<< (k >>> 2)
  else
    4096 <<< (c - 57)

/-- O(1) `log2`/`bsr64`-based `classFor`, mirroring the Lir `arr_class_for` procedure.
Valid for `1 ≤ w ≤ maxCellWords` (`2^26`). -/
def classForFast (w : Nat) : Nat :=
  if w ≤ 32 then w
  else
    let x := w - 1
    let b := x.log2
    if w ≤ 2048 then
      33 + ((b - 5) <<< 2) + ((x >>> (b - 2)) &&& 3)
    else
      b + 46

theorem classWordsFast_eq {c : Nat} (h1 : 1 ≤ c) (h2 : c ≤ maxClass) :
    classWordsFast c = classWords c := by
  have all : ∀ c < maxClass + 1, 1 ≤ c → classWordsFast c = classWords c := by decide
  exact all c (by unfold maxClass at h2 ⊢; omega) h1

/-- Helper: characterizing `classFor w = some c` via the two bounding inequalities
for `1 ≤ c ≤ maxClass`. -/
private theorem classFor_unique_of_bounds {w c : Nat} (hwpos : 1 ≤ w)
    (h1 : 1 ≤ c) (h2 : c ≤ maxClass) (hfit : w ≤ classWords c)
    (hprev : 1 < c → classWords (c - 1) < w) :
    classFor w = some c := by
  have hlemax : w ≤ maxCellWords := Nat.le_trans hfit (classWords_le_max h2)
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (IxCC.Rt.Rc.classFor_total hwpos hlemax)
  obtain ⟨h1', h2', hfit', hmin'⟩ := classFor_spec hc'
  have heq : c' = c := by
    rcases Nat.lt_trichotomy c' c with hlt | heq | hgt
    · have hcgt : 1 < c := by omega
      have hprev_lt := hprev hcgt
      rcases Nat.eq_or_lt_of_le (show c' ≤ c - 1 by omega) with rfl | hlt2
      · omega
      · have hsm := classWords_strictMono hlt2 (by omega)
        omega
    · exact heq
    · have := hmin' c h1 hgt
      omega
  rw [← heq]
  exact hc'

/-- Helper: bit extraction of the 2 bits below the top bit `b` of `x`. -/
private theorem extract_two_bits {x b : Nat} (hb : 5 ≤ b)
    (hlo : 2 ^ b ≤ x) (hhi : x < 2 ^ (b + 1)) :
    let r := (x >>> (b - 2)) &&& 3
    r ≤ 3 ∧
      2 ^ b + r * 2 ^ (b - 2) ≤ x ∧
      x < 2 ^ b + (r + 1) * 2 ^ (b - 2) := by
  intro r
  have hr_eq : r = (x / 2 ^ (b - 2)) % 4 := by
    simp only [r, Nat.shiftRight_eq_div_pow, show (3 : Nat) = 2 ^ 2 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hpow : 2 ^ b = 4 * 2 ^ (b - 2) := by
    have : b = (b - 2) + 2 := by omega
    conv => lhs; rw [this]
    rw [Nat.pow_add]
    omega
  have hpow1 : 2 ^ (b + 1) = 8 * 2 ^ (b - 2) := by
    rw [Nat.pow_succ, hpow]; omega
  have hq_lo : 4 ≤ x / 2 ^ (b - 2) := by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
    omega
  have hq_hi : x / 2 ^ (b - 2) < 8 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    omega
  have hq_eq : x / 2 ^ (b - 2) = 4 + r := by omega
  have hdiv := Nat.div_add_mod x (2 ^ (b - 2))
  have hmod_lt : x % 2 ^ (b - 2) < 2 ^ (b - 2) := Nat.mod_lt x (Nat.two_pow_pos _)
  refine ⟨by omega, ?_, ?_⟩
  · have : 2 ^ (b - 2) * (4 + r) = 2 ^ b + r * 2 ^ (b - 2) := by
      rw [Nat.mul_add, Nat.mul_comm (2 ^ (b - 2)) 4, ← hpow, Nat.mul_comm]
    rw [hq_eq] at hdiv
    omega
  · have : 2 ^ (b - 2) * (4 + r) = 2 ^ b + r * 2 ^ (b - 2) := by
      rw [Nat.mul_add, Nat.mul_comm (2 ^ (b - 2)) 4, ← hpow, Nat.mul_comm]
    have : (r + 1) * 2 ^ (b - 2) = r * 2 ^ (b - 2) + 2 ^ (b - 2) := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hq_eq] at hdiv
    omega

/-- Helper: `classWords` on the octave `[33..56]` equals `2^b + (r + 1) * 2^(b - 2)`. -/
private theorem classWords_mid_octave {b r : Nat} (hb1 : 5 ≤ b) (hb2 : b ≤ 10) (hr : r ≤ 3) :
    classWords (33 + 4 * (b - 5) + r) = 2 ^ b + (r + 1) * 2 ^ (b - 2) ∧
      classWords (33 + 4 * (b - 5) + r - 1) = 2 ^ b + r * 2 ^ (b - 2) := by
  have all : ∀ b < 11, 5 ≤ b → ∀ r < 4,
      classWords (33 + 4 * (b - 5) + r) = 2 ^ b + (r + 1) * 2 ^ (b - 2) ∧
        classWords (33 + 4 * (b - 5) + r - 1) = 2 ^ b + r * 2 ^ (b - 2) := by decide
  exact all b (by omega) hb1 r (by omega)

/-- Helper: `classWords` on the large doubling range `[57..71]` equals `2^(b+1)`. -/
private theorem classWords_high_octave {b : Nat} (hb1 : 11 ≤ b) (hb2 : b ≤ 25) :
    classWords (b + 46) = 2 ^ (b + 1) ∧ classWords (b + 46 - 1) = 2 ^ b := by
  have all : ∀ b < 26, 11 ≤ b →
      classWords (b + 46) = 2 ^ (b + 1) ∧ classWords (b + 46 - 1) = 2 ^ b := by decide
  exact all b (by omega) hb1

/-- Exact agreement between O(1) `classForFast` and `Rt.Rc.classFor` across the
entire 512 MiB allocation range (`1 ≤ w ≤ 2^26`). -/
theorem classForFast_eq {w : Nat} (h1 : 1 ≤ w) (h2 : w ≤ maxCellWords) :
    classFor w = some (classForFast w) := by
  by_cases hsmall : w ≤ 32
  · simp only [classForFast, hsmall, ↓reduceIte]
    exact classFor_small h1 hsmall
  · let x := w - 1
    let b := x.log2
    have hx_ge : 32 ≤ x := by omega
    have hx_lt : x < 2 ^ 26 := by
      have hm : maxCellWords = 2 ^ 26 := IxCC.Rt.Rc.maxCellWords_eq
      omega
    have hb_lo : 2 ^ b ≤ x := Nat.log2_self_le (by omega)
    have hb_hi : x < 2 ^ (b + 1) := by
      have hlt : b < b + 1 := Nat.lt_succ_self b
      exact (Nat.log2_lt (by omega)).mp hlt
    have hb_ge5 : 5 ≤ b := by
      rw [Nat.le_log2 (by omega)]
      omega
    have hb_le25 : b ≤ 25 := by
      have hlt26 : b < 26 := (Nat.log2_lt (by omega)).mpr hx_lt
      omega
    by_cases hmid : w ≤ 2048
    · have hb_le10 : b ≤ 10 := by
        have hlt11 : b < 11 := (Nat.log2_lt (by omega)).mpr (by omega)
        omega
      obtain ⟨hr_le, hlo, hhi⟩ := extract_two_bits hb_ge5 hb_lo hb_hi
      let r := (x >>> (b - 2)) &&& 3
      have hcf : classForFast w = 33 + 4 * (b - 5) + r := by
        simp only [classForFast, hsmall, hmid, ↓reduceIte, Nat.shiftLeft_eq]
        change 33 + (b - 5) * 2 ^ 2 + r = 33 + 4 * (b - 5) + r
        omega
      rw [hcf]
      obtain ⟨hc_eq, hp_eq⟩ := classWords_mid_octave hb_ge5 hb_le10 hr_le
      apply classFor_unique_of_bounds h1 (by omega) (by unfold maxClass; omega)
      · rw [hc_eq]; omega
      · intro _; rw [hp_eq]; omega
    · have hb_ge11 : 11 ≤ b := by
        rw [Nat.le_log2 (by omega)]
        omega
      have hcf : classForFast w = b + 46 := by
        simp only [classForFast, hsmall, hmid, ↓reduceIte]
        rfl
      rw [hcf]
      obtain ⟨hc_eq, hp_eq⟩ := classWords_high_octave hb_ge11 hb_le25
      apply classFor_unique_of_bounds h1 (by omega) (by unfold maxClass; omega)
      · rw [hc_eq]; omega
      · intro _; rw [hp_eq]; omega

theorem classForFast_bounds {w : Nat} (h1 : 1 ≤ w) (h2 : w ≤ maxCellWords) :
    1 ≤ classForFast w ∧ classForFast w ≤ maxClass ∧ w ≤ classWords (classForFast w) := by
  have h := classFor_spec (classForFast_eq h1 h2)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end IxCC.Rt.Rc.Array
