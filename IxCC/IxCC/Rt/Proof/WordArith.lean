import IxCC.Rt.Proof.Words
import IxCC.Rt.Lower

/-!
# Tagged-word arithmetic for the fixed-width words (stage W1)

The word-level facts behind `Rt.Lower.word`: on tagged words `2n + 1` (`natWord`) of numbers in
range, each expansion computes the word of `WordOp.eval`'s number, or (at width 64) takes its
overflow exit exactly when that number is at least `2^63`. Statements are about `UInt64` values
and `Nat` only; `Rt.Proof.OpsWord` runs the Lir statements and applies them.

* Below width 64 (`narrow_word`): a word congruent to `2X + 1` modulo `2^(w+1)`, masked with the
  tagged mask, is the word of `X mod 2^w`; each operation supplies its congruence.
* At width 64 (`wide_word`): the untagged 64-bit result is `eval`'s number, which has a word
  exactly when it is below `2^63`.
* Shift amounts: `(b >>> 1) &&& (bits − 1)` is the count modulo the width (`count_toNat`).
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower (tagMask)
open IxCC.Src (Width WordOp)

/-! ## Widths -/

theorem narrow_cases {w : Width} (hw : w ≠ .w64) : w = .w8 ∨ w = .w16 ∨ w = .w32 := by
  cases w <;> simp_all

theorem narrow_bits {w : Width} (hw : w ≠ .w64) : w.bits ≤ 32 := by
  rcases narrow_cases hw with rfl | rfl | rfl <;> decide

theorem narrow_size {w : Width} (hw : w ≠ .w64) : w.size ≤ 2 ^ 32 :=
  Nat.pow_le_pow_right (by decide) (narrow_bits hw)

theorem two_size (w : Width) : 2 * w.size = 2 ^ (w.bits + 1) := by
  simp only [Width.size, Nat.pow_succ, Nat.mul_comm]

theorem size_w64 : Width.size .w64 = 2 ^ 64 := rfl

/-! ## `Nat` facts -/

theorem two_mul_add_one_mod (X s : Nat) (hs : 0 < s) : (2 * X + 1) % (2 * s) = 2 * (X % s) + 1 := by
  have h := Nat.mod_add_div X s
  have hr := Nat.mod_lt X hs
  have hr' : 2 * (X % s) + 1 < 2 * s := by
    generalize X % s = r at hr ⊢
    omega
  have e : 2 * X + 1 = (2 * (X % s) + 1) + (2 * s) * (X / s) := by
    rw [Nat.mul_assoc]
    generalize X % s = r at h ⊢
    generalize s * (X / s) = m at h ⊢
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr']

theorem or_one_even {e : Nat} (h : e % 2 = 0) : e ||| 1 = e + 1 := by
  have : e = 2 * (e / 2) := by omega
  rw [this, even_or_one]

theorem tag_xor_even (p q : Nat) : (2 * p + 1) ^^^ (2 * q) = 2 * (p ^^^ q) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, testBit_two_mul_add_one, testBit_two_mul]
  split <;> simp

/-! ## Below width 64: the tagged mask -/

theorem tagMask_toNat {w : Width} (hw : w ≠ .w64) : (tagMask w).toNat = 2 * w.size - 1 := by
  have := narrow_size hw
  unfold tagMask
  exact toNat_ofNat_lt (by omega)

theorem and_tagMask {w : Width} (hw : w ≠ .w64) (t : Word) :
    (t &&& tagMask w).toNat = t.toNat % (2 * w.size) := by
  rw [UInt64.toNat_and, tagMask_toNat hw, two_size, Nat.and_two_pow_sub_one_eq_mod]

/-- **The narrow result**: a word congruent to `2X + 1` modulo `2 · 2^w`, masked, is the word of
`X mod 2^w`. -/
theorem narrow_word {w : Width} (hw : w ≠ .w64) {t : Word} {X : Nat}
    (h : t.toNat % (2 * w.size) = (2 * X + 1) % (2 * w.size)) :
    natWord (X % w.size) = some (t &&& tagMask w) := by
  have hs := narrow_size hw
  have hp := w.size_pos
  have hx : X % w.size < w.size := Nat.mod_lt _ hp
  refine natWord_iff.2 ⟨Nat.lt_of_lt_of_le hx (Nat.le_trans hs (by decide)), ?_⟩
  rw [and_tagMask hw, h, two_mul_add_one_mod X w.size hp]

/-! ## Shift amounts -/

/-- The shift amount the code computes, as the machine masks it: the count modulo the width. -/
theorem count_toNat (w : Width) {q : Nat} {b : Word} (hb : natWord q = some b) :
    (((b >>> 1) &&& UInt64.ofNat (w.bits - 1)) &&& 63).toNat = q % w.bits := by
  have hy := untag_toNat hb
  cases w <;>
  · simp only [Width.bits]
    rw [UInt64.toNat_and, UInt64.toNat_and, hy]
    first
    | (rw [show (UInt64.ofNat (8 - 1)).toNat = 2 ^ 3 - 1 from rfl])
    | (rw [show (UInt64.ofNat (16 - 1)).toNat = 2 ^ 4 - 1 from rfl])
    | (rw [show (UInt64.ofNat (32 - 1)).toNat = 2 ^ 5 - 1 from rfl])
    | (rw [show (UInt64.ofNat (64 - 1)).toNat = 2 ^ 6 - 1 from rfl])
    rw [Nat.and_two_pow_sub_one_eq_mod, show (UInt64.toNat 63) = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega

/-! ## Below width 64: each operation's congruence -/

section narrow

variable {w : Width} (hw : w ≠ .w64) {p q : Nat} {a b : Word} (ha : natWord p = some a)
  (hb : natWord q = some b)

include hw ha hb in
theorem narrowAdd_word (hp : p < w.size) (hq : q < w.size) :
    natWord (WordOp.eval w .add p q).val = some ((a + b - 1) &&& tagMask w) := by
  have hs := narrow_size hw
  have ha' := natWord_toNat ha
  have hb' := natWord_toNat hb
  refine narrow_word hw (X := p + q) (congrArg (· % (2 * w.size)) ?_)
  rw [UInt64.toNat_sub, UInt64.toNat_add, ha', hb']
  simp only [UInt64.toNat_one]
  omega

include hw ha hb in
theorem narrowSub_word (hp : p < w.size) (hq : q < w.size) :
    natWord (WordOp.eval w .sub p q).val = some (((a - b) ||| 1) &&& tagMask w) := by
  have ha' := natWord_toNat ha
  have hb' := natWord_toNat hb
  have hl := natWord_lt ha
  have hl' := natWord_lt hb
  refine narrow_word hw (X := w.size - q + p) ?_
  rw [UInt64.toNat_or, UInt64.toNat_sub, ha', hb', UInt64.toNat_one,
    or_one_even (by omega)]
  rcases narrow_cases hw with rfl | rfl | rfl <;> simp only [Width.size, Width.bits] at hp hq ⊢ <;> omega

include hw ha hb in
theorem narrowMul_word (hp : p < w.size) (hq : q < w.size) :
    natWord (WordOp.eval w .mul p q).val = some ((((a >>> 1) * (b - 1)) ||| 1) &&& tagMask w) := by
  refine narrow_word hw (X := p * q) ?_
  rw [UInt64.toNat_or, UInt64.toNat_mul, untag_toNat ha, sub_one_toNat hb, UInt64.toNat_one,
    show p * (2 * q) = 2 * (p * q) by rw [Nat.mul_left_comm]]
  generalize p * q = Y
  rw [or_one_even (by omega)]
  rcases narrow_cases hw with rfl | rfl | rfl <;> simp only [Width.size, Width.bits] <;> omega

include hw ha hb in
theorem narrowShl_word (hp : p < w.size) (hq : q < w.size) :
    natWord (WordOp.eval w .shiftLeft p q).val =
      some ((((a - 1) <<< (((b >>> 1) &&& UInt64.ofNat (w.bits - 1)) &&& 63)) ||| 1) &&& tagMask w) := by
  have hc := count_toNat w hb
  have hlt : q % w.bits < 64 := by
    have := narrow_bits hw
    have := Nat.mod_lt q (Nat.lt_of_lt_of_le (by decide) (show 1 ≤ w.bits by cases w <;> decide))
    omega
  have e : (WordOp.eval w .shiftLeft p q).val = (p * 2 ^ (q % w.bits)) % w.size := by
    simp only [WordOp.eval, Src.WordResult.val, Nat.shiftLeft_eq]
  rw [e]
  refine narrow_word hw (X := p * 2 ^ (q % w.bits)) ?_
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, sub_one_toNat ha, hc, UInt64.toNat_one,
    Nat.mod_eq_of_lt hlt, Nat.shiftLeft_eq, Nat.mul_assoc]
  generalize p * 2 ^ (q % w.bits) = Y
  rw [or_one_even (by omega)]
  rcases narrow_cases hw with rfl | rfl | rfl <;> simp only [Width.size, Width.bits] <;> omega

include hw ha in
theorem narrowComplement_word (hp : p < w.size) :
    natWord (WordOp.eval w .complement p 0).val = some ((a ^^^ (tagMask w - 1)) &&& tagMask w) := by
  have hs := narrow_size hw
  have hpos := w.size_pos
  have hm : (tagMask w - 1).toNat = 2 * (w.size - 1) := by
    rw [UInt64.toNat_sub, tagMask_toNat hw, UInt64.toNat_one]
    omega
  have hx : (w.size - 1) ^^^ p < w.size := by
    have := Nat.xor_lt_two_pow (n := w.bits) (show w.size - 1 < 2 ^ w.bits by have := w.size_pos; unfold Width.size at this ⊢; omega) hp
    exact this
  have e : (WordOp.eval w .complement p 0).val = ((w.size - 1) ^^^ p) % w.size := by
    simp only [WordOp.eval, Src.WordResult.val, Nat.mod_eq_of_lt hx]
  rw [e]
  refine narrow_word hw (X := (w.size - 1) ^^^ p) (congrArg (· % (2 * w.size)) ?_)
  rw [UInt64.toNat_xor, natWord_toNat ha, hm, tag_xor_even, Nat.xor_comm]

include hw ha in
theorem narrowNeg_word (hp : p < w.size) :
    natWord (WordOp.eval w .neg p 0).val = some ((2 - a) &&& tagMask w) := by
  have ha' := natWord_toNat ha
  refine narrow_word hw (X := w.size - p) ?_
  rw [UInt64.toNat_sub, ha', show (UInt64.toNat 2) = 2 from rfl]
  rcases narrow_cases hw with rfl | rfl | rfl <;> simp only [Width.size, Width.bits] at hp ⊢ <;> omega

include hw ha in
theorem narrowOfNat_word : natWord (WordOp.eval w .ofNat p 0).val = some (a &&& tagMask w) :=
  narrow_word hw (X := p) (by rw [natWord_toNat ha])

end narrow

/-- A conversion to a narrower width `w'` (the mask of `w'`). -/
theorem convertNarrow_word {w w' : Width} (hww : ¬ w.bits ≤ w'.bits) {p : Nat} {a : Word}
    (ha : natWord p = some a) : natWord (WordOp.eval w (.convert w') p 0).val = some (a &&& tagMask w') := by
  have hw' : w' ≠ .w64 := by
    rintro rfl
    cases w <;> simp [Width.bits] at hww
  have e : (WordOp.eval w (.convert w') p 0).val = p % w'.size := by
    simp only [WordOp.eval, hww, ↓reduceIte, Src.WordResult.val]
  rw [e]
  exact narrow_word hw' (X := p) (by rw [natWord_toNat ha])

/-- A conversion to a width at least as wide: the same word. -/
theorem convertWide_word {w w' : Width} (hww : w.bits ≤ w'.bits) {p : Nat} {a : Word}
    (ha : natWord p = some a) : natWord (WordOp.eval w (.convert w') p 0).val = some a := by
  simp only [WordOp.eval, hww, ↓reduceIte, Src.WordResult.val]
  exact ha

/-- `toNat`: the same word. -/
theorem toNat_word {w : Width} {p : Nat} {a : Word} (ha : natWord p = some a) :
    natWord (WordOp.eval w .toNat p 0).val = some a := ha

/-! ## Every width: `shiftRight` -/

theorem wordShr_word (w : Width) {p q : Nat} {a b : Word} (ha : natWord p = some a)
    (hb : natWord q = some b) :
    natWord (WordOp.eval w .shiftRight p q).val =
      some ((a >>> (((b >>> 1) &&& UInt64.ofNat (w.bits - 1)) &&& 63)) ||| 1) := by
  have hp := natWord_lt ha
  have hc := count_toNat w hb
  have hlt : q % w.bits < 64 := by
    have := Nat.mod_lt q (Nat.lt_of_lt_of_le (by decide) (show 1 ≤ w.bits by cases w <;> decide))
    have : w.bits ≤ 64 := by cases w <;> decide
    omega
  have e : (WordOp.eval w .shiftRight p q).val = p / 2 ^ (q % w.bits) := by
    simp only [WordOp.eval, Src.WordResult.val, Nat.shiftRight_eq_div_pow]
  rw [e]
  refine natWord_iff.2 ⟨Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hp, ?_⟩
  rw [UInt64.toNat_or, UInt64.toNat_shiftRight, hc, natWord_toNat ha, UInt64.toNat_one,
    Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow]
  exact shr_tag p (q % w.bits)

/-! ## Width 64: the untagged result -/

/-- **The wide result**: an untagged 64-bit result `r` equal to `eval`'s number `n` has the word
`2r + 1` when it is below `2^63`, and `n` has no word otherwise. -/
theorem wide_word {n : Nat} {r : Word} (hr : r.toNat = n) :
    (¬ r > 0x7fffffffffffffff → natWord n = some (r + r + 1)) ∧
      (r > 0x7fffffffffffffff → natWord n = none) := by
  constructor
  · intro hle
    simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, Nat.not_lt] at hle
    have : r.toNat < 2 ^ 63 := by
      rw [show (UInt64.toNat 0x7fffffffffffffff) = 2 ^ 63 - 1 from rfl] at hle
      omega
    exact natWord_iff.2 ⟨by omega, by rw [retag_toNat this, hr]⟩
  · intro hgt
    simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt] at hgt
    rw [show (UInt64.toNat 0x7fffffffffffffff) = 2 ^ 63 - 1 from rfl] at hgt
    unfold natWord natLimit
    rw [ite_eq_right (by omega)]

section wide

variable {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b)

include ha hb in
theorem wideAdd_toNat : ((a >>> 1) + (b >>> 1)).toNat = (WordOp.eval .w64 .add p q).val := by
  rw [UInt64.toNat_add, untag_toNat ha, untag_toNat hb]; rfl

include ha hb in
theorem wideSub_toNat : ((a >>> 1) - (b >>> 1)).toNat = (WordOp.eval .w64 .sub p q).val := by
  rw [UInt64.toNat_sub, untag_toNat ha, untag_toNat hb]; rfl

include ha hb in
theorem wideMul_toNat : ((a >>> 1) * (b >>> 1)).toNat = (WordOp.eval .w64 .mul p q).val := by
  rw [UInt64.toNat_mul, untag_toNat ha, untag_toNat hb]; rfl

include ha hb in
theorem wideShl_toNat :
    ((a >>> 1) <<< (((b >>> 1) &&& UInt64.ofNat (Width.bits .w64 - 1)) &&& 63)).toNat =
      (WordOp.eval .w64 .shiftLeft p q).val := by
  have hc := count_toNat .w64 hb
  rw [UInt64.toNat_shiftLeft, untag_toNat ha, hc]
  simp only [WordOp.eval, Src.WordResult.val, Width.bits, Width.size]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

include ha in
theorem wideComplement_toNat :
    ((a >>> 1) ^^^ 0xFFFFFFFFFFFFFFFF).toNat = (WordOp.eval .w64 .complement p 0).val := by
  rw [UInt64.toNat_xor, untag_toNat ha, show (UInt64.toNat 0xFFFFFFFFFFFFFFFF) = 2 ^ 64 - 1 from rfl,
    Nat.xor_comm]
  rfl

include ha in
theorem wideNeg_toNat : ((0 : Word) - (a >>> 1)).toNat = (WordOp.eval .w64 .neg p 0).val := by
  rw [UInt64.toNat_sub, untag_toNat ha]
  simp only [UInt64.toNat_zero, Nat.add_zero, WordOp.eval, Src.WordResult.val, Width.size, Width.bits]

include ha in
theorem wideOfNat_word : natWord (WordOp.eval .w64 .ofNat p 0).val = some a := by
  have hp := natWord_lt ha
  simp only [WordOp.eval, Src.WordResult.val, Width.size, Width.bits]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact ha

/-! ## Raw 64-bit arithmetic over full `[0, 2^64)` (DR2 Stage W2) -/

theorem rawAdd_toNat {p q : Nat} {a b : Word} (ha : a.toNat = p) (hb : b.toNat = q) :
    (a + b).toNat = (WordOp.eval .w64 .add p q).val := by
  rw [UInt64.toNat_add, ha, hb]; rfl

theorem rawSub_toNat {p q : Nat} {a b : Word} (ha : a.toNat = p) (hb : b.toNat = q) :
    (a - b).toNat = (WordOp.eval .w64 .sub p q).val := by
  rw [UInt64.toNat_sub, ha, hb]; rfl

theorem rawMul_toNat {p q : Nat} {a b : Word} (ha : a.toNat = p) (hb : b.toNat = q) :
    (a * b).toNat = (WordOp.eval .w64 .mul p q).val := by
  rw [UInt64.toNat_mul, ha, hb]; rfl

theorem rawDiv_toNat {p q : Nat} {a b : Word} (ha : a.toNat = p) (hb : b.toNat = q) :
    (if b == 0 then (0 : Word) else a / b).toNat = (WordOp.eval .w64 .div p q).val := by
  by_cases hq : b = 0
  · subst hq
    have hp0 : q = 0 := hb.symm
    subst hp0
    simp [WordOp.eval, Src.WordResult.val]
  · have hne : (b == 0) = false := beq_false_of_ne hq
    simp only [hne, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_div, ha, hb]
    rfl

theorem rawMod_toNat {p q : Nat} {a b : Word} (ha : a.toNat = p) (hb : b.toNat = q) :
    (if b == 0 then a else a % b).toNat = (WordOp.eval .w64 .mod p q).val := by
  by_cases hq : b = 0
  · subst hq
    have hp0 : q = 0 := hb.symm
    subst hp0
    simp [ha, WordOp.eval, Src.WordResult.val]
  · have hne : (b == 0) = false := beq_false_of_ne hq
    simp only [hne, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_mod, ha, hb]
    rfl

theorem rawLand_toNat {p q : Nat} {a b : Word} (ha : a.toNat = p) (hb : b.toNat = q) :
    (a &&& b).toNat = (WordOp.eval .w64 .land p q).val := by
  rw [UInt64.toNat_and, ha, hb]; rfl

theorem rawLor_toNat {p q : Nat} {a b : Word} (ha : a.toNat = p) (hb : b.toNat = q) :
    (a ||| b).toNat = (WordOp.eval .w64 .lor p q).val := by
  rw [UInt64.toNat_or, ha, hb]; rfl

theorem rawXor_toNat {p q : Nat} {a b : Word} (ha : a.toNat = p) (hb : b.toNat = q) :
    (a ^^^ b).toNat = (WordOp.eval .w64 .xor p q).val := by
  rw [UInt64.toNat_xor, ha, hb]; rfl

theorem rawShl_toNat {p q : Nat} {a b : Word} (ha : a.toNat = p) (hb : b.toNat = q) :
    (a <<< ((b &&& 63) &&& 63)).toNat = (WordOp.eval .w64 .shiftLeft p q).val := by
  have hc : ((b &&& 63) &&& 63).toNat = q % 64 := by
    rw [UInt64.toNat_and, UInt64.toNat_and, hb, show (UInt64.toNat 63) = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [UInt64.toNat_shiftLeft, ha, hc]
  simp only [WordOp.eval, Src.WordResult.val, Width.bits, Width.size]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

theorem rawShr_toNat {p q : Nat} {a b : Word} (ha : a.toNat = p) (hb : b.toNat = q) :
    (a >>> ((b &&& 63) &&& 63)).toNat = (WordOp.eval .w64 .shiftRight p q).val := by
  have hc : ((b &&& 63) &&& 63).toNat = q % 64 := by
    rw [UInt64.toNat_and, UInt64.toNat_and, hb, show (UInt64.toNat 63) = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [UInt64.toNat_shiftRight, ha, hc]
  simp only [WordOp.eval, Src.WordResult.val, Width.bits]
  rw [Nat.mod_eq_of_lt (Nat.mod_lt q (by decide))]

theorem rawComplement_toNat {p : Nat} {a : Word} (ha : a.toNat = p) :
    (a ^^^ 0xFFFFFFFFFFFFFFFF).toNat = (WordOp.eval .w64 .complement p 0).val := by
  rw [UInt64.toNat_xor, ha, show (UInt64.toNat 0xFFFFFFFFFFFFFFFF) = 2 ^ 64 - 1 from rfl,
    Nat.xor_comm]
  rfl

theorem rawNeg_toNat {p : Nat} {a : Word} (ha : a.toNat = p) :
    ((0 : Word) - a).toNat = (WordOp.eval .w64 .neg p 0).val := by
  rw [UInt64.toNat_sub, ha]
  simp only [UInt64.toNat_zero, Nat.add_zero, WordOp.eval, Src.WordResult.val, Width.size, Width.bits]

theorem rawConvertNarrow_toNat {w' : Width} (hw' : w' ≠ .w64) {p : Nat} {a : Word}
    (ha : a.toNat = p) :
    (a &&& UInt64.ofNat (w'.size - 1)).toNat = (WordOp.eval .w64 (.convert w') p 0).val := by
  have hle : ¬ (Width.bits .w64 ≤ w'.bits) := by
    rcases narrow_cases hw' with rfl | rfl | rfl <;> decide
  have hm : (UInt64.ofNat (w'.size - 1)).toNat = 2 ^ w'.bits - 1 := by
    have := narrow_size hw'
    exact toNat_ofNat_lt (by omega)
  rw [UInt64.toNat_and, ha, hm, Nat.and_two_pow_sub_one_eq_mod]
  simp only [WordOp.eval, hle, ↓reduceIte, Src.WordResult.val, Width.size]

/-! ## Hardware 64-bit Limb Primitive Arithmetic (both raw `[0, 2^64)` and tagged W1) -/

theorem rawClz64_zero : ((64 : Word).toNat) = (WordOp.eval .w64 .clz64 0 0).val := rfl

theorem rawClz64_nz {p : Nat} {a : Word} (ha : a.toNat = p) (hnz : a ≠ 0) :
    ((63 : Word) - UInt64.ofNat a.toNat.log2).toNat = (WordOp.eval .w64 .clz64 p 0).val := by
  have hp0 : p ≠ 0 := fun h => hnz (UInt64.toNat_inj.mp (by rw [ha, h]; rfl))
  have hbeq : (p == 0) = false := beq_false_of_ne hp0
  have hlog : a.toNat.log2 < 64 := IxCC.BigNat.log2_uint64_lt_64 a
  rw [ha] at hlog
  have hof : (UInt64.ofNat a.toNat.log2).toNat = p.log2 := by
    rw [ha]; exact toNat_ofNat_lt (by omega)
  rw [UInt64.toNat_sub, hof, show (UInt64.toNat 63) = 63 from rfl]
  simp only [WordOp.eval, Src.WordResult.val, hbeq, Bool.false_eq_true, ↓reduceIte]
  omega

theorem wideClz64_zero : natWord (WordOp.eval .w64 .clz64 0 0).val = some 129 := by
  refine natWord_iff.2 ⟨by decide, rfl⟩

theorem wideClz64_nz {p : Nat} {a : Word} (ha : a.toNat = p) (hnz : a ≠ 0) :
    let r : Word := 63 - UInt64.ofNat a.toNat.log2
    natWord (WordOp.eval .w64 .clz64 p 0).val = some (r + r + 1) := by
  intro r
  have hr := rawClz64_nz ha hnz
  have hp0 : p ≠ 0 := fun h => hnz (UInt64.toNat_inj.mp (by rw [ha, h]; rfl))
  have hbeq : (p == 0) = false := beq_false_of_ne hp0
  have hlt : r.toNat < 2 ^ 63 := by
    rw [hr]
    simp only [WordOp.eval, Src.WordResult.val, hbeq, Bool.false_eq_true, ↓reduceIte]
    omega
  exact natWord_iff.2 ⟨by rw [← hr]; exact hlt, by rw [retag_toNat hlt, hr]⟩

theorem rawMulWideLo_toNat {p q : Nat} {a b : Word} (ha : a.toNat = p) (hb : b.toNat = q) :
    (a * b).toNat = (WordOp.eval .w64 .mulWideLo p q).val := by
  rw [UInt64.toNat_mul, ha, hb]; rfl

theorem rawMulWideHi_toNat {p q : Nat} {a b : Word} (ha : a.toNat = p) (hb : b.toNat = q) :
    (UInt64.ofNat (a.toNat * b.toNat / 2 ^ 64)).toNat = (WordOp.eval .w64 .mulWideHi p q).val := by
  have ha' := a.toNat_lt_size
  have hb' := b.toNat_lt_size
  simp only [UInt64.size] at ha' hb'
  have hdiv : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64)]
    have h1 := Nat.mul_le_mul (show a.toNat ≤ 2 ^ 64 - 1 by omega) (show b.toNat ≤ 2 ^ 64 - 1 by omega)
    omega
  rw [toNat_ofNat_lt hdiv, ha, hb]; rfl

theorem rawDivWideQ_toNat {hi lo d : Nat} {whi wlo wd : Word}
    (hhi : whi.toNat = hi) (hlo : wlo.toNat = lo) (hd : wd.toNat = d) (hlt : hi < d) :
    (UInt64.ofNat ((whi.toNat * 2 ^ 64 + wlo.toNat) / wd.toNat)).toNat =
      ((hi * Width.size .w64 + lo) / d) := by
  have hlt' : whi < wd := UInt64.lt_iff_toNat_lt.mpr (by omega)
  have hq := IxCC.BigNat.divWide64_div_lt whi wlo wd hlt'
  rw [toNat_ofNat_lt hq, hhi, hlo, hd]; rfl

theorem rawDivWideR_toNat {hi lo d : Nat} {whi wlo wd : Word}
    (hhi : whi.toNat = hi) (hlo : wlo.toNat = lo) (hd : wd.toNat = d) (hlt : hi < d) :
    (UInt64.ofNat ((whi.toNat * 2 ^ 64 + wlo.toNat) % wd.toNat)).toNat =
      ((hi * Width.size .w64 + lo) % d) := by
  have hdlt := wd.toNat_lt_size
  simp only [UInt64.size] at hdlt
  have hmod : (whi.toNat * 2 ^ 64 + wlo.toNat) % wd.toNat < 2 ^ 64 :=
    Nat.lt_trans (Nat.mod_lt _ (by omega)) hdlt
  rw [toNat_ofNat_lt hmod, hhi, hlo, hd]; rfl

theorem rawAddCarryLo_toNat {p q c : Nat} {a b wc : Word}
    (ha : a.toNat = p) (hb : b.toNat = q) (hc : wc.toNat = c) :
    let cin : Nat := if wc == 0 then 0 else 1
    (a + b + UInt64.ofNat cin).toNat = ((p + q + (if c == 0 then 0 else 1)) % Width.size .w64) := by
  intro cin
  have hcin : cin = if c == 0 then 0 else 1 := by
    by_cases h0 : c = 0
    · have hw0 : wc = 0 := UInt64.toNat_inj.mp (by rw [hc, h0]; rfl)
      simp [cin, hw0, h0]
    · have hw0 : wc ≠ 0 := fun h => h0 (by rw [← hc, h]; rfl)
      simp [cin, beq_false_of_ne hw0, beq_false_of_ne h0]
  have hcinlt : cin < 2 ^ 64 := by dsimp [cin]; split <;> decide
  rw [UInt64.toNat_add, UInt64.toNat_add, toNat_ofNat_lt hcinlt, ha, hb, hcin]
  simp only [Width.size, Width.bits]
  rw [Nat.mod_add_mod]

theorem rawAddCarryOut_toNat {p q c : Nat} {a b wc : Word}
    (ha : a.toNat = p) (hb : b.toNat = q) (hc : wc.toNat = c) :
    let cin : Nat := if wc == 0 then 0 else 1
    ((if a.toNat + b.toNat + cin ≥ 2 ^ 64 then (1 : Word) else 0)).toNat =
      (if Width.size .w64 ≤ p + q + (if c == 0 then 0 else 1) then 1 else 0) := by
  intro cin
  have hcin : cin = if c == 0 then 0 else 1 := by
    by_cases h0 : c = 0
    · have hw0 : wc = 0 := UInt64.toNat_inj.mp (by rw [hc, h0]; rfl)
      simp [cin, hw0, h0]
    · have hw0 : wc ≠ 0 := fun h => h0 (by rw [← hc, h]; rfl)
      simp [cin, beq_false_of_ne hw0, beq_false_of_ne h0]
  rw [ha, hb, hcin]
  simp only [Width.size, Width.bits, ge_iff_le]
  split <;> split <;> rfl

theorem rawSubBorrowLo_toNat {p q c : Nat} {a b wc : Word}
    (ha : a.toNat = p) (hb : b.toNat = q) (hc : wc.toNat = c) :
    let bin : Nat := if wc == 0 then 0 else 1
    (a - b - UInt64.ofNat bin).toNat =
      (let b0 := if c == 0 then 0 else 1
       if p < q + b0 then Width.size .w64 + p - (q + b0) else p - (q + b0)) := by
  intro bin
  have hbin : bin = if c == 0 then 0 else 1 := by
    by_cases h0 : c = 0
    · have hw0 : wc = 0 := UInt64.toNat_inj.mp (by rw [hc, h0]; rfl)
      simp [bin, hw0, h0]
    · have hw0 : wc ≠ 0 := fun h => h0 (by rw [← hc, h]; rfl)
      simp [bin, beq_false_of_ne hw0, beq_false_of_ne h0]
  have ha' := a.toNat_lt_size
  have hb' := b.toNat_lt_size
  simp only [UInt64.size] at ha' hb'
  have hbinlt : bin < 2 ^ 64 := by dsimp [bin]; split <;> decide
  rw [UInt64.toNat_sub, UInt64.toNat_sub, toNat_ofNat_lt hbinlt, ha, hb]
  rw [ha] at ha'; rw [hb] at hb'
  simp only [Width.size, Width.bits]
  rw [← hbin]
  have hble : bin ≤ 1 := by dsimp [bin]; split <;> decide
  split <;> omega

theorem rawSubBorrowOut_toNat {p q c : Nat} {a b wc : Word}
    (ha : a.toNat = p) (hb : b.toNat = q) (hc : wc.toNat = c) :
    let bin : Nat := if wc == 0 then 0 else 1
    ((if a.toNat < b.toNat + bin then (1 : Word) else 0)).toNat =
      (if p < q + (if c == 0 then 0 else 1) then 1 else 0) := by
  intro bin
  have hbin : bin = if c == 0 then 0 else 1 := by
    by_cases h0 : c = 0
    · have hw0 : wc = 0 := UInt64.toNat_inj.mp (by rw [hc, h0]; rfl)
      simp [bin, hw0, h0]
    · have hw0 : wc ≠ 0 := fun h => h0 (by rw [← hc, h]; rfl)
      simp [bin, beq_false_of_ne hw0, beq_false_of_ne h0]
  rw [ha, hb, hbin]
  split <;> split <;> rfl

theorem bit_word {b : Word} (h : b = 0 ∨ b = 1) : natWord b.toNat = some (b + b + 1) := by
  rcases h with rfl | rfl
  · exact natWord_iff.2 ⟨by decide, rfl⟩
  · exact natWord_iff.2 ⟨by decide, rfl⟩

end wide

end IxCC.Rt.Proof
