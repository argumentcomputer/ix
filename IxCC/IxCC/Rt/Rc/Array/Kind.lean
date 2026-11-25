import IxCC.Rt.Rc.Array.Layout

/-! # Array element kinds by width

An array cell is `header | size | capacity | elements` (`Layout`). Its *element kind* says how the
elements are held: one tagged word each, scanned on release (`boxed`), or raw values of one machine
width, never scanned (`packed w`: bytes, 16-, 32- or 64-bit words). This is the design's
`ElemKind` (`plans/ONE-PIPELINE.md` 2.4, 3.4), with the width a machine width.

Everything about a cell's geometry is a function of the kind: the element size (`bytes`, a power
of two), the index scale (`scale`), the capacity a size class provides (`capOfClass`), the words a
capacity needs (`cellWords`), and the header (`scan`, `tag`). The header names the kind, so the
release reads it without any certificate: scan byte `0xFF` for a boxed cell (its element count is
its size word), `0` for a packed one (released at once); one tag per kind, above `Rt.maxTag`.

The three kinds of the side path are three of these (`ArrayKind.elem`): `boxed`, `bytes` is
`packed .w8`, `limbs` is `packed .w64`; their tags and scan bytes are unchanged
(`ArrayKind.elem_tag`, `ArrayKind.elem_scan`), so a side-path cell is a cell of its kind. The
16- and 32-bit kinds take the next two tags (`0x7F04` for 32-bit elements, as on the reference
branch `dr3-cow-u32`, and `0x7F05` for 16-bit ones). -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open IxCC.Lir (Word)
open IxCC.Rt (header maxTag maxFields immortalRc)
open IxCC.Rt.Rc (dynamicHeader maxCount maxClass classWords classFor classBytes maxCellWords
  classWords_strictMono classWords_le_max classWords_small classFor_spec
  header_scan header_class header_tag header_rc dynamicHeader_count)

/-- Header tag of a packed array of 32-bit elements. -/
def tagU32Array : Nat := 0x7F04

/-- Header tag of a packed array of 16-bit elements. -/
def tagU16Array : Nat := 0x7F05

/-- How the elements of an array cell are stored. -/
inductive ElemKind where
  /-- One tagged word per element (an immediate or a counted cell), scanned on release. -/
  | boxed
  /-- Raw values of width `w`, never scanned: the cell is a leaf. -/
  | packed (w : X86.Width)
  deriving DecidableEq, Repr, Inhabited

namespace ElemKind

/-- The width an element is loaded and stored at. -/
def width : ElemKind → X86.Width
  | .boxed => .w64
  | .packed w => w

/-- Bytes per element. -/
def bytes (k : ElemKind) : Nat := k.width.bytes

/-- `log₂` of the bytes per element. -/
def shift (k : ElemKind) : Nat :=
  match k.width with
  | .w8 => 0
  | .w16 => 1
  | .w32 => 2
  | .w64 => 3

/-- The index scale of an element address. -/
def scale (k : ElemKind) : X86.Scale :=
  match k.width with
  | .w8 => .one
  | .w16 => .two
  | .w32 => .four
  | .w64 => .eight

/-- Elements per payload word. -/
def perWord (k : ElemKind) : Nat := 2 ^ (3 - k.shift)

/-- The header tag. -/
def tag : ElemKind → Nat
  | .boxed => X86.ELFRodata.tagBoxedArray
  | .packed .w8 => X86.ELFRodata.tagByteArray
  | .packed .w16 => tagU16Array
  | .packed .w32 => tagU32Array
  | .packed .w64 => X86.ELFRodata.tagLimbArray

/-- The header scan byte: `0xFF` for a boxed cell (its count is its size word), `0` for a leaf. -/
def scan : ElemKind → Nat
  | .boxed => X86.ELFRodata.scanBoxedArray
  | .packed _ => 0

/-- Whether the elements are counted references. -/
def isBoxed : ElemKind → Bool
  | .boxed => true
  | .packed _ => false

/-- The element capacity of a cell of size class `cls`. -/
def capOfClass (k : ElemKind) (cls : Nat) : Nat := k.perWord * (classWords cls - arrayHeaderWords)

/-- The words a cell of capacity `cap` needs. -/
def cellWords (k : ElemKind) (cap : Nat) : Nat := arrayHeaderWords + (k.bytes * cap + 7) / 8

/-- The largest capacity: that of the largest class. -/
def maxCap (k : ElemKind) : Nat := k.perWord * maxWordCap

/-- The header of a live cell of class `cls` with `refs` references. -/
def header (k : ElemKind) (cls refs : Nat) : Word := dynamicHeader k.scan cls k.tag refs

/-- The header of a static (immortal, `.rodata`) cell. -/
def staticHeader (k : ElemKind) : Word := IxCC.Rt.header k.scan 0 k.tag immortalRc

/-- The low header bits shared by every live cell of the kind: `scan | tag << 16` (class `0`,
count `0`, that is one reference). -/
def template (k : ElemKind) : Word := UInt64.ofNat (k.scan + 65536 * k.tag)

/-- A value an element of the kind can hold: below `2 ^ bits` of its width. -/
def Fits (k : ElemKind) (x : Word) : Prop := x.toNat < 2 ^ k.width.bits

/-! ## Arithmetic of the kinds -/

theorem width_cases (k : ElemKind) :
    k.width = .w8 ∨ k.width = .w16 ∨ k.width = .w32 ∨ k.width = .w64 := by
  cases h : k.width <;> simp

theorem bytes_eq_shift (k : ElemKind) : k.bytes = 2 ^ k.shift := by
  unfold bytes shift
  cases k.width <;> rfl

theorem shift_le (k : ElemKind) : k.shift ≤ 3 := by
  unfold shift; cases k.width <;> decide

theorem bytes_pos (k : ElemKind) : 0 < k.bytes := by
  unfold bytes; cases k.width <;> decide

theorem bytes_le (k : ElemKind) : k.bytes ≤ 8 := by
  unfold bytes; cases k.width <;> decide

theorem bytes_mul_perWord (k : ElemKind) : k.bytes * k.perWord = 8 := by
  unfold bytes perWord shift; cases k.width <;> rfl

theorem perWord_pos (k : ElemKind) : 0 < k.perWord := by
  unfold perWord; exact Nat.two_pow_pos _

theorem perWord_le (k : ElemKind) : k.perWord ≤ 8 := by
  unfold perWord shift; cases k.width <;> decide

theorem scale_word (k : ElemKind) : k.scale.word = UInt64.ofNat k.bytes := by
  unfold scale bytes; cases k.width <;> rfl

theorem bits_eq (k : ElemKind) : k.width.bits = 8 * k.bytes := by
  unfold bytes; cases k.width <;> rfl

@[simp] theorem boxed_width : ElemKind.boxed.width = .w64 := rfl
@[simp] theorem boxed_bytes : ElemKind.boxed.bytes = 8 := rfl
@[simp] theorem packed_width (w : X86.Width) : (ElemKind.packed w).width = w := rfl
@[simp] theorem boxed_isBoxed : ElemKind.boxed.isBoxed = true := rfl
@[simp] theorem packed_isBoxed (w : X86.Width) : (ElemKind.packed w).isBoxed = false := rfl
@[simp] theorem boxed_scan : ElemKind.boxed.scan = 0xFF := rfl
@[simp] theorem packed_scan (w : X86.Width) : (ElemKind.packed w).scan = 0 := rfl

theorem scan_eq_zero_iff (k : ElemKind) : k.scan = 0 ↔ k.isBoxed = false := by
  cases k <;> simp [scan, isBoxed, X86.ELFRodata.scanBoxedArray]

theorem fits_w64 {k : ElemKind} (hk : k.width = .w64) (x : Word) : k.Fits x := by
  unfold Fits; rw [hk]; exact x.toNat_lt_size

theorem boxed_fits (x : Word) : ElemKind.boxed.Fits x := fits_w64 rfl x

theorem tag_gt_maxTag (k : ElemKind) : maxTag < k.tag := by
  cases k with
  | boxed => decide
  | packed w => cases w <;> decide

theorem tag_lt (k : ElemKind) : k.tag < 65536 := by
  cases k with
  | boxed => decide
  | packed w => cases w <;> decide

theorem scan_lt (k : ElemKind) : k.scan < 256 := by
  cases k <;> simp [scan, X86.ELFRodata.scanBoxedArray]

/-- The header tag names the kind. -/
theorem tag_injective {k₁ k₂ : ElemKind} (h : k₁.tag = k₂.tag) : k₁ = k₂ := by
  cases k₁ with
  | boxed => cases k₂ with
    | boxed => rfl
    | packed w => cases w <;> cases h
  | packed w₁ => cases k₂ with
    | boxed => cases w₁ <;> cases h
    | packed w₂ => cases w₁ <;> cases w₂ <;> first | rfl | cases h

/-- A boxed scan byte is above every constructor's field count. -/
theorem boxed_scan_gt_maxFields : maxFields < ElemKind.boxed.scan := by decide

theorem template_or_cls (k : ElemKind) {cls : Nat} (hcls : cls ≤ maxClass) :
    (k.template ||| (UInt64.ofNat cls <<< 8)) = k.header cls 1 := by
  have all : ∀ k : ElemKind, ∀ cls < 72,
      (k.template ||| (UInt64.ofNat cls <<< 8)) = k.header cls 1 := by
    intro k
    cases k with
    | boxed => decide
    | packed w => cases w <;> decide
  exact all k cls (by unfold maxClass at hcls; omega)

theorem header_fields (k : ElemKind) {cls refs : Nat}
    (hcls : cls ≤ maxClass) (hpos : 0 < refs) (hmax : refs ≤ maxCount) :
    ((k.header cls refs) &&& 0xFF).toNat = k.scan ∧
      (((k.header cls refs) >>> 8) &&& 0xFF).toNat = cls ∧
      (((k.header cls refs) >>> 16) &&& 0xFFFF).toNat = k.tag ∧
      ((k.header cls refs) >>> 32).toNat + 1 = refs := by
  have hs := k.scan_lt
  have ht := k.tag_lt
  have hc : cls < 256 := by unfold maxClass at hcls; omega
  have hrc : refs - 1 < 2 ^ 32 := by unfold maxCount at hmax; omega
  exact ⟨header_scan hs hc ht hrc, header_class hs hc ht hrc, header_tag hs hc ht hrc,
    dynamicHeader_count hs hc ht hpos hmax⟩

theorem staticHeader_eq_elfRodata (k : ElemKind) :
    k.staticHeader = X86.ELFRodata.staticHeader k.scan k.tag := by
  cases k with
  | boxed => rfl
  | packed w => cases w <;> rfl

theorem staticHeader_fields (k : ElemKind) :
    ((k.staticHeader) &&& 0xFF).toNat = k.scan ∧
      (((k.staticHeader) >>> 8) &&& 0xFF).toNat = 0 ∧
      (((k.staticHeader) >>> 16) &&& 0xFFFF).toNat = k.tag ∧
      ((k.staticHeader) >>> 32).toNat = immortalRc := by
  rw [staticHeader_eq_elfRodata]
  exact ⟨X86.ELFRodata.staticHeader_scan k.scan_lt k.tag_lt,
    X86.ELFRodata.staticHeader_cls k.scan_lt k.tag_lt,
    X86.ELFRodata.staticHeader_tag k.scan_lt k.tag_lt,
    X86.ELFRodata.staticHeader_rc k.scan_lt k.tag_lt⟩

theorem staticHeader_rc_signed_neg (k : ElemKind) :
    X86.Width.signedValue .w32 ((k.staticHeader) >>> 32) < 0 := by
  rw [staticHeader_eq_elfRodata]
  exact X86.ELFRodata.staticHeader_rc_signed_neg k.scan_lt k.tag_lt

/-! ## Capacity -/

theorem cellWords_ge_three (k : ElemKind) (cap : Nat) : 3 ≤ k.cellWords cap := by
  unfold cellWords arrayHeaderWords; omega

theorem maxCap_eq (k : ElemKind) : k.maxCap * k.bytes = 8 * maxWordCap := by
  unfold maxCap
  rw [Nat.mul_comm, ← Nat.mul_assoc, bytes_mul_perWord]

theorem cellWords_le_max (k : ElemKind) {cap : Nat} (h : cap ≤ k.maxCap) :
    k.cellWords cap ≤ maxCellWords := by
  have hm := maxCap_eq k
  have hb : k.bytes * cap ≤ 8 * maxWordCap := by
    rw [← hm, Nat.mul_comm]; exact Nat.mul_le_mul_right _ h
  have hmax : maxCellWords = 2 ^ 26 := IxCC.Rt.Rc.maxCellWords_eq
  unfold cellWords arrayHeaderWords
  unfold maxWordCap arrayHeaderWords at hb
  omega

/-- The bytes of `cap` elements fill at most the payload words of the class. -/
theorem capOfClass_bytes (k : ElemKind) (cls : Nat) :
    k.bytes * k.capOfClass cls = 8 * (classWords cls - arrayHeaderWords) := by
  unfold capOfClass
  rw [← Nat.mul_assoc, bytes_mul_perWord]

theorem payload_eq_classBytes (k : ElemKind) {cls : Nat} (h1 : minArrayClass ≤ cls)
    (h2 : cls ≤ maxClass) :
    arrayPayloadOffset + k.bytes * k.capOfClass cls = classBytes cls := by
  have h3 := classWords_ge_three h1 h2
  rw [capOfClass_bytes]
  unfold arrayPayloadOffset classBytes arrayHeaderWords
  omega

theorem capOfClass_le_maxCap (k : ElemKind) {cls : Nat} (h : cls ≤ maxClass) :
    k.capOfClass cls ≤ k.maxCap := by
  unfold capOfClass maxCap maxWordCap
  apply Nat.mul_le_mul_left
  have := classWords_le_max h
  omega

/-- The class of `cellWords cap` holds `cap` elements and is an array class. -/
theorem capOfClass_spec (k : ElemKind) {cap cls : Nat}
    (h : classFor (k.cellWords cap) = some cls) :
    minArrayClass ≤ cls ∧ cls ≤ maxClass ∧ cap ≤ k.capOfClass cls := by
  obtain ⟨h1, h2, hfit, _⟩ := classFor_spec h
  have hge3 : 3 ≤ classWords cls := by
    have := cellWords_ge_three k cap
    omega
  have hcls3 : minArrayClass ≤ cls := by
    rcases Nat.lt_or_ge cls minArrayClass with hlt | hge
    · have hle : cls ≤ 2 := by unfold minArrayClass at hlt; omega
      rw [classWords_small (by omega)] at hge3
      omega
    · exact hge
  refine ⟨hcls3, h2, ?_⟩
  have hb := capOfClass_bytes k cls
  have hpos := bytes_pos k
  have hw : k.bytes * cap ≤ 8 * (classWords cls - arrayHeaderWords) := by
    unfold cellWords arrayHeaderWords at hfit
    unfold arrayHeaderWords
    omega
  rw [← hb] at hw
  exact Nat.le_of_mul_le_mul_left hw hpos

end ElemKind

/-! ## The side path's three kinds -/

/-- The element kind of a side-path array kind. -/
def ArrayKind.elem : ArrayKind → ElemKind
  | .boxed => .boxed
  | .bytes => .packed .w8
  | .limbs => .packed .w64

theorem ArrayKind.elem_tag (k : ArrayKind) : k.elem.tag = k.tag := by cases k <;> rfl

theorem ArrayKind.elem_scan (k : ArrayKind) : k.elem.scan = k.scan := by cases k <;> rfl

theorem ArrayKind.elem_header (k : ArrayKind) (cls refs : Nat) :
    k.elem.header cls refs = arrayHeader k cls refs := by
  simp [ElemKind.header, arrayHeader, ArrayKind.elem_tag, ArrayKind.elem_scan]

theorem ArrayKind.elem_staticHeader (k : ArrayKind) :
    k.elem.staticHeader = staticArrayHeader k := by
  simp [ElemKind.staticHeader, staticArrayHeader, ArrayKind.elem_tag, ArrayKind.elem_scan]

theorem ElemKind.limbs_capOfClass (cls : Nat) :
    (ElemKind.packed .w64).capOfClass cls = wordCapOfClass cls := by
  simp [ElemKind.capOfClass, ElemKind.perWord, ElemKind.shift, ElemKind.width, wordCapOfClass]

theorem ElemKind.boxed_capOfClass (cls : Nat) :
    ElemKind.boxed.capOfClass cls = wordCapOfClass cls := by
  simp [ElemKind.capOfClass, ElemKind.perWord, ElemKind.shift, ElemKind.width, wordCapOfClass]

theorem ElemKind.bytes_capOfClass (cls : Nat) :
    (ElemKind.packed .w8).capOfClass cls = byteCapOfClass cls := by
  simp [ElemKind.capOfClass, ElemKind.perWord, ElemKind.shift, ElemKind.width, byteCapOfClass]

end IxCC.Rt.Rc.Array
