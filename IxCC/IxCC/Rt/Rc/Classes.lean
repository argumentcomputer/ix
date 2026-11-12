import IxCC.Rt.Rc.Layout

/-! # Size classes and cell layouts of the counted heap

A dynamic cell is a header word, `nobj` scanned fields (tagged words: immediates or pointers), then
`nscalar` raw 64-bit scalar words that the release never reads as pointers. Its storage is a *size
class*: classes `1 … 32` hold exactly that many words (the classes of every cell before general
layouts), classes `33 … 56` four per doubling from 40 to 2,048 words, classes `57 … 71` one per
doubling from 4,096 words to 2²⁶ words (512 MiB). The context block has a free-list head for each
of the 71 classes (`Rt.headClasses`), which `cx_init` zeroes. A cell of more than 2²⁶ words has no
class: its allocation is refused when the program is compiled.

The header's scan byte counts the scanned fields (at most `Rt.maxFields` = 254; `0xFF` stays
reserved for object kinds whose count is elsewhere); its class byte names the size class. -/

namespace IxCC.Rt.Rc

/-! ## Size classes -/

/-- The largest size class; the context block holds a free-list head for each of `1 … 71`. -/
def maxClass : Nat := 71

/-- The words (header included) of a cell of class `c`. -/
def classWords (c : Nat) : Nat :=
  if c ≤ 32 then c
  else if c ≤ 56 then 2 ^ ((c - 33) / 4) * (32 + 8 * ((c - 33) % 4 + 1))
  else 2 ^ (c - 57) * 4096

/-- The least class holding `w` words, if any. -/
def classFor (w : Nat) : Option Nat :=
  if w = 0 then none else (List.range' 1 maxClass).find? (fun c => decide (w ≤ classWords c))

/-- The bytes of a cell of class `c`. -/
def classBytes (c : Nat) : Nat := 8 * classWords c

/-- The largest cell, in words: 2²⁶ (512 MiB). -/
def maxCellWords : Nat := classWords maxClass

theorem maxCellWords_eq : maxCellWords = 2 ^ 26 := by decide

theorem classWords_small {c : Nat} (h : c ≤ 32) : classWords c = c := by
  simp [classWords, h]

theorem classWords_strictMono {a b : Nat} (h : a < b) (hb : b ≤ maxClass) :
    classWords a < classWords b := by
  have all : ∀ b < maxClass + 1, ∀ a < b, classWords a < classWords b := by decide
  exact all b (by unfold maxClass at hb ⊢; omega) a h

theorem classWords_pos {c : Nat} (h : 1 ≤ c) : 0 < classWords c := by
  unfold classWords
  split
  · omega
  · split <;> exact Nat.mul_pos (Nat.two_pow_pos _) (by omega)

theorem classWords_le_max {c : Nat} (h : c ≤ maxClass) : classWords c ≤ maxCellWords := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact Nat.le_of_lt (classWords_strictMono h (Nat.le_refl _))
  · rw [h]; exact Nat.le_refl _

/-- `classFor` picks the least class that fits. -/
theorem classFor_spec {w c : Nat} (h : classFor w = some c) :
    1 ≤ c ∧ c ≤ maxClass ∧ w ≤ classWords c ∧ ∀ c', 1 ≤ c' → c' < c → classWords c' < w := by
  unfold classFor at h
  split at h
  · cases h
  · rw [List.find?_range'_eq_some] at h
    obtain ⟨hp, hm, hmin⟩ := h
    rw [List.mem_range'_1] at hm
    refine ⟨hm.1, by unfold maxClass at hm ⊢; omega, by simpa using hp, ?_⟩
    intro c' h1 h2
    have := hmin c' h1 h2
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at this
    exact this

theorem classFor_total {w : Nat} (h1 : 1 ≤ w) (h2 : w ≤ maxCellWords) : (classFor w).isSome := by
  unfold classFor
  split
  · omega
  · rw [List.find?_isSome]
    exact ⟨maxClass, by simp [maxClass], by simpa [maxCellWords] using h2⟩

theorem classFor_none {w : Nat} (h : maxCellWords < w) : classFor w = none := by
  unfold classFor
  split
  · rfl
  · rw [List.find?_range'_eq_none]
    intro c h1 h2
    have := classWords_le_max (c := c) (by unfold maxClass at h2 ⊢; omega)
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le]
    omega

theorem classFor_zero : classFor 0 = none := rfl

/-- Internal fragmentation: under a quarter up to 2,048 words, under a half above. -/
theorem classFor_waste {w c : Nat} (h : classFor w = some c) :
    classWords c ≤ 2 * w ∧ (w ≤ 2048 → 4 * classWords c < 5 * w) := by
  obtain ⟨h1, h2, hfit, hmin⟩ := classFor_spec h
  have hw : 1 ≤ w := by
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · simp [classFor_zero] at h
    · exact hw
  have double : ∀ c < maxClass + 1, 2 ≤ c → classWords c ≤ 2 * (classWords (c - 1) + 1) := by
    decide
  have fifth : ∀ c < 57, 2 ≤ c → 4 * classWords c < 5 * (classWords (c - 1) + 1) := by
    decide
  rcases Nat.lt_or_eq_of_le h1 with h1 | h1
  · have below := hmin (c - 1) (by omega) (by omega)
    refine ⟨by have := double c (by unfold maxClass at h2 ⊢; omega) h1; omega, fun hs => ?_⟩
    have hc : c < 57 := by
      rcases Nat.lt_or_ge c 57 with hc | hc
      · exact hc
      · have h56 : classWords 56 = 2048 := by decide
        rcases Nat.lt_or_eq_of_le (show 56 ≤ c - 1 by omega) with hlt | heq
        · have := classWords_strictMono (a := 56) (b := c - 1) hlt
            (by unfold maxClass at h2 ⊢; omega)
          omega
        · rw [← heq] at below
          omega
    have := fifth c hc h1
    omega
  · subst h1
    have : classWords 1 = 1 := rfl
    omega

/-- Today's classes are kept: a cell of `w ≤ 32` words is in class `w`. -/
theorem classFor_small {w : Nat} (h1 : 1 ≤ w) (h2 : w ≤ 32) : classFor w = some w := by
  have all : ∀ w < 33, 1 ≤ w → classFor w = some w := by decide
  exact all w (by omega) h1

/-- `smallClass n = n + 1` (the class of every cell before general layouts) is `classFor` of an
`n`-field cell. -/
theorem classFor_smallClass {n : Nat} (h : n < 32) : classFor (1 + n) = some (smallClass n) := by
  have all : ∀ n < 32, classFor (1 + n) = some (smallClass n) := by decide
  exact all n h

/-- Every head slot is inside the context block. -/
theorem heads_inside : ctxOffset + 8 * maxClass + 8 = ctxBlockBytes := rfl

/-! ## Cell layouts -/

/-- A cell layout: `nobj` scanned fields, then `nscalar` raw 64-bit scalar words, and the tag. -/
structure CellLayout where
  nobj : Nat
  nscalar : Nat
  tag : Nat
  deriving DecidableEq, Repr

namespace CellLayout

/-- The words a cell of this layout needs: the header, the scanned fields, the scalar words. -/
def words (L : CellLayout) : Nat := 1 + L.nobj + L.nscalar

/-- Its size class, if it has one. -/
def cls? (L : CellLayout) : Option Nat := classFor L.words

/-- A layout the runtime allocates: at least one field (a field-less constructor is an immediate),
at most 254 scanned fields (`0xFF` stays reserved), a constructor tag, and a size class. -/
def ok (L : CellLayout) : Bool :=
  decide (0 < L.nobj + L.nscalar) && decide (L.nobj ≤ maxFields) && decide (L.tag ≤ maxTag) &&
    L.cls?.isSome

/-- The layouts of every cell before general layouts: `n` scanned fields, no scalar word. -/
def ofFields (n tag : Nat) : CellLayout := ⟨n, 0, tag⟩

theorem ofFields_cls {n tag : Nat} (h : n < 32) : (ofFields n tag).cls? = some (smallClass n) := by
  have := classFor_smallClass h
  simpa [cls?, words, ofFields] using this

theorem ofFields_ok {n tag : Nat} (h0 : 0 < n) (h : n < 32) (ht : tag ≤ maxTag) :
    (ofFields n tag).ok = true := by
  have hc := ofFields_cls (tag := tag) h
  simp only [ok, hc, Option.isSome_some, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  simp only [ofFields, maxFields]
  omega

theorem ok_cls {L : CellLayout} (h : L.ok = true) : ∃ cls, L.cls? = some cls := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact Option.isSome_iff_exists.mp h.2

theorem ok_bounds {L : CellLayout} (h : L.ok = true) :
    0 < L.nobj + L.nscalar ∧ L.nobj ≤ maxFields ∧ L.tag ≤ maxTag := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

/-- A layout's class has room for it, is a class of the table, and is at least 2 (a cell has a
field). -/
theorem cls_spec {L : CellLayout} {cls : Nat} (hL : L.ok = true) (hc : L.cls? = some cls) :
    2 ≤ cls ∧ cls ≤ maxClass ∧ L.words ≤ classWords cls := by
  obtain ⟨h1, h2, hfit, hmin⟩ := classFor_spec hc
  have := (ok_bounds hL).1
  refine ⟨?_, h2, hfit⟩
  rcases Nat.lt_or_ge cls 2 with hlt | hge
  · have : cls = 1 := by omega
    subst this
    have : classWords 1 = 1 := rfl
    simp only [words] at hfit
    omega
  · exact hge

/-- The header of a fresh cell of layout `L` in class `cls` with `refs` references reads back its
scan count, its class, its tag and its count. -/
theorem header_fields {L : CellLayout} {cls refs : Nat} (hL : L.ok = true)
    (hc : L.cls? = some cls) (hp : 0 < refs) (hr : refs ≤ maxCount) :
    ((dynamicHeader L.nobj cls L.tag refs) &&& 0xFF).toNat = L.nobj ∧
      (((dynamicHeader L.nobj cls L.tag refs) >>> 8) &&& 0xFF).toNat = cls ∧
      (((dynamicHeader L.nobj cls L.tag refs) >>> 16) &&& 0xFFFF).toNat = L.tag ∧
      ((dynamicHeader L.nobj cls L.tag refs) >>> 32).toNat + 1 = refs := by
  obtain ⟨_, hs, ht⟩ := ok_bounds hL
  obtain ⟨_, hcm, _⟩ := cls_spec hL hc
  unfold maxFields at hs
  unfold maxTag at ht
  unfold maxClass at hcm
  unfold maxCount at hr
  have hrc : refs - 1 < 2 ^ 32 := by omega
  exact ⟨header_scan (by omega) (by omega) (by omega) hrc,
    header_class (by omega) (by omega) (by omega) hrc,
    header_tag (by omega) (by omega) (by omega) hrc,
    dynamicHeader_count (by omega) (by omega) (by omega) hp (by unfold maxCount; omega)⟩

end CellLayout

end IxCC.Rt.Rc
