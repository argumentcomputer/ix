import Compilatrix.Rt.Layout
import Compilatrix.Lir.Semantics
import Compilatrix.Src.Prim

/-!
# Tagged-word arithmetic (04 §2)

The word-level facts behind each primitive's Lir expansion in `Rt.lower`
(`Rt.Lower.primitive`): on tagged words `2n + 1` (`natWord`), each
expansion computes the word of the exact `Nat` result whenever it does not
take its overflow exit. The statements are about `UInt64` values only; the
per-operation simulation lemmas (`Rt.Proof.Ops`) run the Lir statements and
apply them.

* `natAdd`: `(2p) + (2q + 1)` without a carry is `2(p + q) + 1`.
* `natSub`, `natPred`: truncated subtraction by a `select` on `a < b`
  (`a = 1`).
* `natMul`: `p · 2q` checked by division is exact when the check passes.
* `natDiv`, `natMod`: on untagged values with a nonzero divisor, retagged.
* comparisons: tagging is monotone.
* `natLand`, `natLor`, `natXor`: the tag bit survives `and`/`or`, and `xor`
  restores it.
* `natShr`: `(2p + 1) >>> q ||| 1` is `2(p >>> q) + 1`; `natShl`: `2p <<< q`
  shifted back to `2p` is exact.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word)

/-! ## Basics -/

theorem two64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
theorem two63 : (2 : Nat) ^ 63 = 9223372036854775808 := rfl
theorem natLimit_eq : natLimit = 2 ^ 63 := rfl

theorem natWord_iff {n : Nat} {w : Word} :
    natWord n = some w ↔ n < 2 ^ 63 ∧ w.toNat = 2 * n + 1 := by
  constructor
  · intro h
    exact ⟨by unfold natWord natLimit at h; split at h <;> simp_all, natWord_toNat h⟩
  · rintro ⟨hn, hw⟩
    unfold natWord natLimit
    rw [if_pos hn]
    congr 1
    apply UInt64.toNat_inj.mp
    rw [hw, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)

theorem natWord_lt {n : Nat} {w : Word} (h : natWord n = some w) : n < 2 ^ 63 :=
  (natWord_iff.1 h).1

theorem natWord_of_lt {n : Nat} (h : n < 2 ^ 63) : natWord n = some (UInt64.ofNat (2 * n + 1)) := by
  unfold natWord natLimit
  rw [if_pos h]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem word_lt (w : Word) : w.toNat < 2 ^ 64 := w.toNat_lt_size

theorem sub_toNat_of_le {a b : Word} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  have := word_lt a
  have := word_lt b
  rw [UInt64.toNat_sub]
  omega

theorem sub_one_toNat {p : Nat} {a : Word} (ha : natWord p = some a) : (a - 1).toNat = 2 * p := by
  have := natWord_toNat ha
  rw [sub_toNat_of_le (by simp; omega)]
  simp
  omega

/-- `Width.truncate .w64` is the identity. -/
@[simp] theorem truncate_w64 (x : Word) : X86.Width.truncate .w64 x = x := by
  apply UInt64.toNat_inj.mp
  simp only [X86.Width.truncate, X86.Width.mask, UInt64.toNat_and]
  rw [show (UInt64.toNat 0xffffffffffffffff) = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (word_lt x)

@[simp] theorem shiftMask_w64 : Lir.shiftMask .w64 = 63 := rfl

theorem toNat_and63 (y : Word) : (y &&& 63).toNat = y.toNat % 64 := by
  rw [UInt64.toNat_and, show (UInt64.toNat 63) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-! ## Bits of tagged numbers -/

theorem testBit_two_mul_add_one (p : Nat) (i : Nat) :
    (2 * p + 1).testBit i = if i = 0 then true else p.testBit (i - 1) := by
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    rw [Nat.testBit_succ]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    congr 1
    omega

theorem testBit_two_mul (p : Nat) (i : Nat) :
    (2 * p).testBit i = if i = 0 then false else p.testBit (i - 1) := by
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    rw [Nat.testBit_succ]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    congr 1
    omega

theorem tag_and (p q : Nat) : (2 * p + 1) &&& (2 * q + 1) = 2 * (p &&& q) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, testBit_two_mul_add_one]
  split <;> simp

theorem tag_or (p q : Nat) : (2 * p + 1) ||| (2 * q + 1) = 2 * (p ||| q) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, testBit_two_mul_add_one]
  split <;> simp

theorem tag_xor (p q : Nat) : (2 * p + 1) ^^^ (2 * q + 1) = 2 * (p ^^^ q) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, testBit_two_mul_add_one, testBit_two_mul]
  split <;> simp

/-- `x ||| 1` on an odd or even number. -/
theorem or_one (x : Nat) : x ||| 1 = 2 * (x / 2) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i => simp [Nat.testBit_succ] <;> (congr 1; omega)

theorem even_or_one (d : Nat) : (2 * d) ||| 1 = 2 * d + 1 := by
  rw [or_one]
  congr 2
  omega

/-! ## Words as tagged numbers -/

/-- The word of `n` (when `n < 2^63`), as a raw word. -/
abbrev tagged (n : Nat) : Word := UInt64.ofNat (2 * n + 1)

theorem tagged_toNat {n : Nat} (h : n < 2 ^ 63) : (tagged n).toNat = 2 * n + 1 :=
  toNat_ofNat_lt (by omega)

theorem natWord_tagged {n : Nat} (h : n < 2 ^ 63) : natWord n = some (tagged n) :=
  natWord_of_lt h

/-! ## Addition (`brOvf addC`) -/

/-- An unsigned add carries exactly when the sum leaves 64 bits. -/
theorem add_carry_iff (x y : Word) : (x + y < x) ↔ 2 ^ 64 ≤ x.toNat + y.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  have hx := word_lt x
  have hy := word_lt y
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat
  · have : (x.toNat + y.toNat) % 2 ^ 64 = x.toNat + y.toNat - 2 ^ 64 := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [this]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem add_toNat_of_not_carry {x y : Word} (h : ¬ (x + y < x)) : (x + y).toNat = x.toNat + y.toNat := by
  rw [add_carry_iff] at h
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]

/-- `natAdd`'s sum: operands whose word sum is `2(p + q) + 1` and no
carry give the word of `p + q`. -/
theorem natAdd_word {p q : Nat} {x y : Word} (hxy : x.toNat + y.toNat = 2 * (p + q) + 1)
    (hc : ¬ (x + y < x)) : natWord (p + q) = some (x + y) := by
  have := add_toNat_of_not_carry hc
  have hlt := word_lt (x + y)
  exact natWord_iff.2 ⟨by omega, by omega⟩

/-- The operands of `natAdd`'s `brOvf`: `a − 1` and `b`. -/
theorem natAdd_operands {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b) :
    (a - 1).toNat + b.toNat = 2 * (p + q) + 1 ∧ a.toNat + (b - 1).toNat = 2 * (p + q) + 1 := by
  have h1 := sub_one_toNat ha
  have h2 := sub_one_toNat hb
  have ha' := natWord_toNat ha
  have hb' := natWord_toNat hb
  omega

/-! ## Subtraction and predecessor -/

theorem natSub_word {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b) :
    natWord (p - q) = some (if a < b then 1 else (a - b) ||| 1) := by
  have ha' := natWord_toNat ha
  have hb' := natWord_toNat hb
  have hp := natWord_lt ha
  split
  · rename_i hlt
    rw [UInt64.lt_iff_toNat_lt] at hlt
    exact natWord_iff.2 ⟨by omega, by simp; omega⟩
  · rename_i hge
    rw [UInt64.lt_iff_toNat_lt] at hge
    have hd : (a - b).toNat = 2 * (p - q) := by rw [sub_toNat_of_le (Nat.le_of_not_lt hge)]; omega
    refine natWord_iff.2 ⟨by omega, ?_⟩
    rw [UInt64.toNat_or, hd]
    exact even_or_one _

theorem natPred_word {p : Nat} {a : Word} (ha : natWord p = some a) :
    natWord (p - 1) = some (if a = 1 then 1 else a - 2) := by
  have ha' := natWord_toNat ha
  have hp := natWord_lt ha
  split
  · rename_i h1
    subst h1
    exact natWord_iff.2 ⟨by omega, by simp at ha'; simp; omega⟩
  · rename_i h1
    have hne : a.toNat ≠ 1 := fun h => h1 (UInt64.toNat_inj.mp (by simpa using h))
    refine natWord_iff.2 ⟨by omega, ?_⟩
    rw [sub_toNat_of_le (by simp; omega)]
    simp
    omega

/-! ## Multiplication, checked by division -/

/-- A product that wraps is detected: dividing it by one factor does not
give back the other. -/
theorem mul_check {u t : Nat} (hu : 0 < u) (h : u * t % 2 ^ 64 / u = t) :
    u * t < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hge => ?_
  have hmod : u * t % 2 ^ 64 ≤ u * t - 2 ^ 64 := by
    rw [Nat.mod_eq_sub_mod hge]
    exact Nat.mod_le _ _
  have : u * t % 2 ^ 64 / u ≤ (u * t - 2 ^ 64) / u := Nat.div_le_div_right hmod
  have h2 : (u * t - 2 ^ 64) / u < t := by
    rw [Nat.div_lt_iff_lt_mul hu]
    rw [Nat.mul_comm t u]
    omega
  omega

/-- `natMul`'s expansion: `prod = p · (b − 1)`, `u1 = if p = 0 then 1 else
p`; when `prod / u1 = b − 1` or `p = 0`, `prod ||| 1` is the word of
`p · q`. -/
theorem natMul_word {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b)
    (hok : (a >>> (1 : Word)) * (b - (1 : Word)) / (if a >>> (1 : Word) = 0 then (1 : Word) else a >>> (1 : Word)) =
      b - (1 : Word) ∨ a >>> (1 : Word) = 0) :
    natWord (p * q) = some (((a >>> (1 : Word)) * (b - (1 : Word))) ||| 1) := by
  have ha' := natWord_toNat ha
  have hb' := natWord_toNat hb
  have hp := natWord_lt ha
  have hq := natWord_lt hb
  have hu : (a >>> 1).toNat = p := by
    rw [UInt64.toNat_shiftRight, ha']; simp [Nat.shiftRight_eq_div_pow]; omega
  have ht : (b - 1).toNat = 2 * q := sub_one_toNat hb
  by_cases hp0 : p = 0
  · subst hp0
    have h0 : a >>> 1 = 0 := UInt64.toNat_inj.mp (by simpa using hu)
    refine natWord_iff.2 ⟨by simp, ?_⟩
    rw [h0]
    simp
  · have hne : a >>> 1 ≠ 0 := fun h => hp0 (by rw [← hu, h]; rfl)
    have hdiv : (a >>> (1 : Word)) * (b - (1 : Word)) / (a >>> (1 : Word)) = b - (1 : Word) := by
      rcases hok with h | h
      · simpa [hne] using h
      · exact absurd h hne
    have hdiv' := congrArg UInt64.toNat hdiv
    rw [UInt64.toNat_div, UInt64.toNat_mul, hu, ht] at hdiv'
    have hlt := mul_check (by omega) hdiv'
    have hprod : ((a >>> (1 : Word)) * (b - (1 : Word))).toNat = 2 * (p * q) := by
      rw [UInt64.toNat_mul, hu, ht, Nat.mod_eq_of_lt hlt]
      rw [Nat.mul_left_comm]
    refine natWord_iff.2 ⟨?_, ?_⟩
    · rw [Nat.mul_left_comm] at hlt
      omega
    · rw [UInt64.toNat_or, hprod]
      exact even_or_one _

/-! ## Division and remainder -/

theorem untag_toNat {p : Nat} {a : Word} (ha : natWord p = some a) : (a >>> 1).toNat = p := by
  have ha' := natWord_toNat ha
  rw [UInt64.toNat_shiftRight, ha']; simp [Nat.shiftRight_eq_div_pow]; omega

theorem retag_toNat {q : Word} (hq : q.toNat < 2 ^ 63) : (q + q + 1).toNat = 2 * q.toNat + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_add]
  simp
  omega

/-- `natDiv` on words with a nonzero divisor `q`. -/
theorem natDiv_word {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b)
    (hq : q ≠ 0) : natWord (p / q) = some ((a >>> 1) / (b >>> 1) + (a >>> 1) / (b >>> 1) + 1) := by
  have hp := natWord_lt ha
  have hd : ((a >>> 1) / (b >>> 1)).toNat = p / q := by
    rw [UInt64.toNat_div, untag_toNat ha, untag_toNat hb]
  have hlt : p / q < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hp
  exact natWord_iff.2 ⟨hlt, by rw [retag_toNat (by omega), hd]⟩

theorem natMod_word {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b)
    (hq : q ≠ 0) : natWord (p % q) = some ((a >>> 1) % (b >>> 1) + (a >>> 1) % (b >>> 1) + 1) := by
  have hp := natWord_lt ha
  have hd : ((a >>> 1) % (b >>> 1)).toNat = p % q := by
    rw [UInt64.toNat_mod, untag_toNat ha, untag_toNat hb]
  have hlt : p % q < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.mod_le _ _) hp
  exact natWord_iff.2 ⟨hlt, by rw [retag_toNat (by omega), hd]⟩

/-- A word is `1` exactly when it is the word of zero. -/
theorem natWord_eq_one {q : Nat} {b : Word} (hb : natWord q = some b) : b = 1 ↔ q = 0 := by
  have hb' := natWord_toNat hb
  constructor
  · intro h; subst h; simp at hb'; omega
  · intro h; subst h; exact UInt64.toNat_inj.mp (by simpa using hb')

/-! ## Comparisons -/

theorem natWord_lt_iff {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b) :
    a < b ↔ p < q := by
  rw [UInt64.lt_iff_toNat_lt, natWord_toNat ha, natWord_toNat hb]; omega

theorem natWord_le_iff {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b) :
    a ≤ b ↔ p ≤ q := by
  rw [UInt64.le_iff_toNat_le, natWord_toNat ha, natWord_toNat hb]; omega

theorem natWord_eq_iff {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b) :
    a = b ↔ p = q := by
  rw [← UInt64.toNat_inj, natWord_toNat ha, natWord_toNat hb]; omega

/-! ## Bitwise operations -/

theorem natLand_word {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b) :
    natWord (p &&& q) = some (a &&& b) := by
  have hp := natWord_lt ha
  refine natWord_iff.2 ⟨Nat.lt_of_le_of_lt Nat.and_le_left hp, ?_⟩
  rw [UInt64.toNat_and, natWord_toNat ha, natWord_toNat hb, tag_and]

theorem natLor_word {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b) :
    natWord (p ||| q) = some (a ||| b) := by
  refine natWord_iff.2 ⟨Nat.or_lt_two_pow (natWord_lt ha) (natWord_lt hb), ?_⟩
  rw [UInt64.toNat_or, natWord_toNat ha, natWord_toNat hb, tag_or]

theorem natXor_word {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b) :
    natWord (p ^^^ q) = some ((a ^^^ b) ||| 1) := by
  refine natWord_iff.2 ⟨Nat.xor_lt_two_pow (natWord_lt ha) (natWord_lt hb), ?_⟩
  rw [UInt64.toNat_or, UInt64.toNat_xor, natWord_toNat ha, natWord_toNat hb, tag_xor]
  exact even_or_one _

/-! ## Shifts -/

/-- `Src`'s `shiftRight` is division by a power of two. -/
theorem shiftRight_eval (p q : Nat) :
    (if p.log2 < q then 0 else p / 2 ^ q) = p / 2 ^ q := by
  split
  · rename_i h
    by_cases hp : p = 0
    · subst hp; simp
    · rw [Nat.log2_lt hp] at h
      exact (Nat.div_eq_of_lt h).symm
  · rfl

theorem shr_tag (p y : Nat) : ((2 * p + 1) / 2 ^ y) ||| 1 = 2 * (p / 2 ^ y) + 1 := by
  rw [or_one]
  congr 2
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ y) 2, ← Nat.div_div_eq_div_mul]
  congr 1
  omega

/-- `natShr`'s expansion: `y` the untagged count, `s = a >>> (y & 63)`. -/
theorem natShr_word {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b) :
    natWord (p / 2 ^ q) = some (if b >>> (1 : Word) > 63 then (1 : Word) else (a >>> ((b >>> (1 : Word)) &&& 63)) ||| 1) := by
  have hp := natWord_lt ha
  have hy := untag_toNat hb
  have hlt : p / 2 ^ q < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hp
  split
  · rename_i hgt
    simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, hy] at hgt
    have : p / 2 ^ q = 0 := by
      apply Nat.div_eq_of_lt
      exact Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by omega) (by simp at hgt; omega))
    rw [this]
    rfl
  · rename_i hle
    simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, hy] at hle
    have hq : q ≤ 63 := by simp at hle; omega
    refine natWord_iff.2 ⟨hlt, ?_⟩
    rw [UInt64.toNat_or, UInt64.toNat_shiftRight, toNat_and63, hy, natWord_toNat ha,
      Nat.mod_eq_of_lt (show q % 64 < 64 by omega), Nat.mod_eq_of_lt (show q < 64 by omega),
      Nat.shiftRight_eq_div_pow]
    exact shr_tag p q

/-- A left shift that shifts back to its operand lost no bits. -/
theorem shl_check {t y : Nat} (h : t * 2 ^ y % 2 ^ 64 / 2 ^ y = t) :
    t * 2 ^ y < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hge => ?_
  have hpos : 0 < 2 ^ y := Nat.two_pow_pos y
  have hmod : t * 2 ^ y % 2 ^ 64 ≤ t * 2 ^ y - 2 ^ 64 := by
    rw [Nat.mod_eq_sub_mod hge]
    exact Nat.mod_le _ _
  have : t * 2 ^ y % 2 ^ 64 / 2 ^ y ≤ (t * 2 ^ y - 2 ^ 64) / 2 ^ y := Nat.div_le_div_right hmod
  have h2 : (t * 2 ^ y - 2 ^ 64) / 2 ^ y < t := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    have : 0 < 2 ^ 64 := by decide
    omega
  omega

/-- `natShl`'s expansion: `t = a − 1`, `s = t <<< (y & 63)`, checked by
shifting back; when the check passes (or `t = 0`), `s ||| 1` is the word
of `p · 2^q`. -/
theorem natShl_word {p q : Nat} {a b : Word} (ha : natWord p = some a) (hb : natWord q = some b)
    (hok : ((a - (1 : Word)) <<< ((b >>> (1 : Word)) &&& 63)) >>> ((b >>> (1 : Word)) &&& 63) = a - 1 ∧
      ¬ (b >>> (1 : Word) > 63) ∨ a - (1 : Word) = 0) :
    natWord (p * 2 ^ q) = some (((a - (1 : Word)) <<< ((b >>> (1 : Word)) &&& 63)) ||| 1) := by
  have ha' := natWord_toNat ha
  have hp := natWord_lt ha
  have hy := untag_toNat hb
  have ht : (a - 1).toNat = 2 * p := sub_one_toNat ha
  rcases hok with ⟨hback, hle⟩ | h0
  · simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, hy] at hle
    have hq : q ≤ 63 := by simp at hle; omega
    have hs : ((a - 1) <<< ((b >>> 1) &&& 63)).toNat = 2 * p * 2 ^ q % 2 ^ 64 := by
      rw [UInt64.toNat_shiftLeft, toNat_and63, hy, ht, Nat.mod_eq_of_lt (show q % 64 < 64 by omega),
        Nat.mod_eq_of_lt (show q < 64 by omega), Nat.shiftLeft_eq]
    have hback' := congrArg UInt64.toNat hback
    rw [UInt64.toNat_shiftRight, hs, toNat_and63, hy, ht,
      Nat.mod_eq_of_lt (show q % 64 < 64 by omega), Nat.mod_eq_of_lt (show q < 64 by omega),
      Nat.shiftRight_eq_div_pow] at hback'
    have hlt := shl_check hback'
    rw [Nat.mod_eq_of_lt hlt] at hs
    refine natWord_iff.2 ⟨?_, ?_⟩
    · rw [Nat.mul_assoc] at hlt; omega
    · rw [UInt64.toNat_or, hs, Nat.mul_assoc]
      exact even_or_one _
  · have hp0 : p = 0 := by rw [h0] at ht; simp at ht; omega
    subst hp0
    rw [h0]
    refine natWord_iff.2 ⟨by simp, ?_⟩
    simp

end Compilatrix.Rt.Proof
