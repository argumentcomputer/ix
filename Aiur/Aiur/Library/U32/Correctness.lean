import Aiur.Library.U32
import Aiur.Library.Carry
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Algebraic lemmas about the assertions in the ordinary Aiur word library.
These lemmas add no operation or trusted semantic rule. They establish what the
range checks and equations imply; the existing compiler correctness theorems
apply to the library's source just as they do to any other Aiur program.
-/
namespace Aiur.Library.U32

def pack (a b c d : Nat) : Nat := a + 256*b + 65536*c + 16777216*d

theorem pack_lt {a b c d : Nat} (ha : a < 256) (hb : b < 256)
    (hc : c < 256) (hd : d < 256) : pack a b c d < base := by
  unfold pack base
  omega

variable {F : Type} [Field F]

theorem base_ne_zero (large : Compatible F) : (base : F) ≠ 0 := by
  intro equal
  have := large (x₁ := base) (x₂ := 0) (by norm_num [base]) (by norm_num [base])
    (by simpa using equal)
  norm_num [base] at this

theorem binary_carry (carry : F) : carry * (carry - 1) = 0 ↔ carry = 0 ∨ carry = 1 := by
  simp [mul_eq_zero, sub_eq_zero]

theorem ternary_carry (carry : F) :
    carry * (carry - 1) * (carry - 2) = 0 ↔ carry = 0 ∨ carry = 1 ∨ carry = 2 := by
  simp [mul_eq_zero, sub_eq_zero, or_assoc]

/-- The packed carry relation has a unique, correct low word. This is the
integer-lifting step: a field equality is not enough without the field bound. -/
theorem sum_sound (large : Compatible F) {sum result k : Nat}
    (hs : sum < 3 * base) (hr : result < base) (hk : k < 3)
    (equal : (sum : F) = (result : F) + (base : F) * (k : F)) :
    result = sum % base := by
  have bound : result + base * k < 3 * base := by unfold base at *; omega
  have lifted : sum = result + base * k := large hs bound (by simpa using equal)
  rw [lifted, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- The cubic used by `add3`, with the carry derived from the hinted result. -/
theorem add3_check_iff (large : Compatible F) {sum result : Nat}
    (hs : sum < 3 * base) (hr : result < base) :
    let carry := ((sum : F) - (result : F)) / (base : F)
    carry * (carry - 1) * (carry - 2) = 0 ↔ result = sum % base := by
  dsimp
  constructor
  · intro valid
    rcases (ternary_carry _).1 valid with h | h | h
    · have h := (div_eq_iff (base_ne_zero large)).1 h
      apply sum_sound large hs hr (k := 0) (by norm_num)
      simpa [sub_eq_iff_eq_add, add_comm] using h
    · have h := (div_eq_iff (base_ne_zero large)).1 h
      apply sum_sound large hs hr (k := 1) (by norm_num)
      simpa [sub_eq_iff_eq_add, add_comm] using h
    ·
      have h := (div_eq_iff (base_ne_zero large)).1 h
      apply sum_sound large hs hr (k := 2) (by norm_num)
      linear_combination h
  · intro equal
    rw [equal, Carry.recover base sum (base_ne_zero large)]
    have hk : sum / base < 3 := (Nat.div_lt_iff_lt_mul (by norm_num [base])).2
      (by simpa [mul_comm] using hs)
    have small : ∀ n : Nat, n < 3 → n = 0 ∨ n = 1 ∨ n = 2 := by omega
    have cases := small _ hk
    rcases cases with h | h | h <;> simp [h]

theorem add_check_iff (large : Compatible F) {sum result : Nat}
    (hs : sum < 2 * base) (hr : result < base) :
    let carry := ((sum : F) - (result : F)) / (base : F)
    carry * (carry - 1) = 0 ↔ result = sum % base := by
  dsimp
  constructor
  · intro valid
    apply (add3_check_iff large (by omega) hr).1
    simp [valid]
  · intro equal
    rw [equal, Carry.recover base sum (base_ne_zero large)]
    have hk : sum / base < 2 := (Nat.div_lt_iff_lt_mul (by norm_num [base])).2
      (by simpa [mul_comm] using hs)
    have small : ∀ n : Nat, n < 2 → n = 0 ∨ n = 1 := by omega
    rcases small _ hk with h | h <;> simp [h]

/-- Packed operands already satisfy the word bound; range-checking the
result and constraining the derived carry suffice for wrapping addition. -/
theorem add_words_check_iff (large : Compatible F) {a b result : Nat}
    (ha : a < base) (hb : b < base) (hr : result < base) :
    let carry := ((a : F) + (b : F) - (result : F)) / (base : F)
    carry * (carry - 1) = 0 ↔ result = (a + b) % base := by
  simpa only [Nat.cast_add] using
    (add_check_iff large (sum := a + b) (by omega) hr)

theorem add3_words_check_iff (large : Compatible F) {a b c result : Nat}
    (ha : a < base) (hb : b < base) (hc : c < base) (hr : result < base) :
    let carry := ((a : F) + (b : F) + (c : F) - (result : F)) / (base : F)
    carry * (carry - 1) * (carry - 2) = 0 ↔ result = (a + b + c) % base := by
  simpa only [Nat.cast_add] using
    (add3_check_iff large (sum := a + b + c) (by omega) hr)

/-- The reconstructed boolean borrow determines comparison and wrapping
subtraction simultaneously. The only range checks needed are the result bytes,
because both input compact words were already constructed through the API. -/
theorem sub_sound (large : Compatible F) {a b result : Nat}
    (ha : a < base) (hb : b < base) (hr : result < base)
    (valid : let borrow := ((result : F) + (b : F) - (a : F)) / (base : F)
      borrow * (borrow - 1) = 0) :
    result = (a + base - b) % base ∧
      ((result : F) + (b : F) - (a : F)) / (base : F) = if a < b then 1 else 0 := by
  dsimp at valid
  rcases (binary_carry _).1 valid with h | h
  · have equation := (div_eq_iff (base_ne_zero large)).1 h
    have lifted : result + b = a := large (x₁ := result + b) (x₂ := a)
      (by change result + b < 3 * base; omega) (by change a < 3 * base; omega)
      (by push_cast; linear_combination equation)
    have order : ¬a < b := by omega
    constructor
    · have : a + base - b = result + base := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
    · simpa [order] using h
  · have equation := (div_eq_iff (base_ne_zero large)).1 h
    have lifted : result + b = a + base := large (x₁ := result + b) (x₂ := a + base)
      (by change result + b < 3 * base; omega) (by change a + base < 3 * base; omega)
      (by push_cast; linear_combination equation)
    have order : a < b := by omega
    constructor
    · have : a + base - b = result := by omega
      rw [this, Nat.mod_eq_of_lt hr]
    · simpa [order] using h

theorem joined_nibbles_lt {x y : Nat} (hx : x < 256) (_hy : y < 256) :
    x / 16 + (y % 16) * 16 < 256 := by omega

theorem joined_seven_bits_lt {x y : Nat} (hx : x < 256) (_hy : y < 256) :
    x / 128 + (y % 128) * 2 < 256 := by omega

/-- The three checked byte decompositions establish operand and difference
bounds (`pack_lt`). Recomposition ties the raw fields to those bounded words,
so the boolean borrow is exactly unsigned less-than, including at equality. -/
theorem compare_fields_sound (large : Compatible F) (a b : F)
    {leftWord rightWord difference : Nat}
    (ha : leftWord < base) (hb : rightWord < base) (hd : difference < base)
    (left : a = (leftWord : F)) (right : b = (rightWord : F))
    (valid : let borrow := ((difference : F) + b - a) / (base : F)
      borrow * (borrow - 1) = 0) :
    ((difference : F) + b - a) / (base : F) =
      if leftWord < rightWord then 1 else 0 := by
  subst a; subst b
  exact (sub_sound large ha hb hd valid).2

#print axioms add_check_iff
#print axioms add3_check_iff
#print axioms sub_sound
#print axioms add_words_check_iff
#print axioms add3_words_check_iff
#print axioms compare_fields_sound

end Aiur.Library.U32
