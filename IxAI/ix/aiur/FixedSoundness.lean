import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# Soundness of the fixed-point gadgets in `FixedStep.lean`

The Aiur step takes its rounding quotients, signs and inverses as hints, so its correctness rests
on the checks that constrain those hints. These theorems show that, over the Goldilocks field,
the checks admit only the intended values, for the magnitudes the model uses (`|s| < 2^55`).
Together with Aiur's verified compiler (circuit to Aiur semantics) they reduce the step's
correctness to exact integer arithmetic on the hinted values.
-/

namespace IxAIAiur.Soundness

/-- The Goldilocks prime. -/
abbrev p : ℕ := 18446744069414584321

/-- An integer whose image in the field is zero, and whose magnitude is below the
characteristic, is zero. -/
theorem eq_zero_of_cast_eq_zero {x : ℤ} (hx : |x| < p) (h : ((x : ℤ) : ZMod p) = 0) : x = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact Int.eq_zero_of_abs_lt_dvd h hx

/-- `shr8`: if the circuit's check `256 q + r = s` holds in the field, with the remainder a byte
and the quotient within the six range-checked bytes, then `q` is the integer floor of `s / 256`. -/
theorem shr8_sound {s q r : ℤ} (hs : |s| < 2 ^ 55)
    (hr0 : 0 ≤ r) (hr1 : r < 256) (hq0 : -2 ^ 47 ≤ q) (hq1 : q < 2 ^ 47)
    (h : ((256 * q + r : ℤ) : ZMod p) = (s : ZMod p)) : q = s / 256 := by
  have hz : (((256 * q + r - s : ℤ)) : ZMod p) = 0 := by
    push_cast at h ⊢; rw [h]; exact sub_self _
  have hb : |256 * q + r - s| < (p : ℤ) := by
    rw [abs_lt] at hs ⊢; constructor <;> norm_num [p] at * <;> omega
  have he : 256 * q + r = s := by have := eq_zero_of_cast_eq_zero hb hz; omega
  rw [← he]
  omega

/-- The sign gadget: if the seven range-checked bytes reconstruct `v + 2^55` in the field, they
reconstruct it exactly as integers, so bit 55 of the offset is `v ≥ 0`. -/
theorem sign_offset_sound {v off : ℤ} (hv : |v| < 2 ^ 55) (h0 : 0 ≤ off) (h1 : off < 2 ^ 56)
    (h : ((off : ℤ) : ZMod p) = ((v + 2 ^ 55 : ℤ) : ZMod p)) :
    off = v + 2 ^ 55 ∧ (2 ^ 55 ≤ off ↔ 0 ≤ v) := by
  have hz : (((off - (v + 2 ^ 55) : ℤ)) : ZMod p) = 0 := by
    push_cast at h ⊢; rw [h]; exact sub_self _
  have hb : |off - (v + 2 ^ 55 : ℤ)| < (p : ℤ) := by
    rw [abs_lt] at hv ⊢; constructor <;> norm_num [p] at * <;> omega
  have he : off = v + 2 ^ 55 := by have := eq_zero_of_cast_eq_zero hb hz; omega
  exact ⟨he, by omega⟩

/-- `bound`: if two range-checked bytes `lo`, `hi` satisfy the circuit's check
`lo + 32 hi = x + 4096` in the field, then `x` is the image of the integer `lo + 32 hi - 4096`,
which lies in `[-4096, 4320)`. This holds for every field element `x`, whatever the prover
supplies as the hinted words. -/
theorem bound_field_sound {x : ZMod p} {lo hi : ℤ}
    (hlo0 : 0 ≤ lo) (hlo1 : lo < 256) (hhi0 : 0 ≤ hi) (hhi1 : hi < 256)
    (h : ((lo + 32 * hi : ℤ) : ZMod p) = x + 4096) :
    ∃ v : ℤ, -4096 ≤ v ∧ v < 4320 ∧ x = (v : ZMod p) := by
  refine ⟨lo + 32 * hi - 4096, by omega, by omega, ?_⟩
  push_cast at h ⊢
  linear_combination -h

/-- `bound` on an integer: for `|v| < 2^55`, the check `lo + 32 hi = v + 4096` in the field
holds as integers, so `-4096 ≤ v < 4320`. -/
theorem bound_sound {v lo hi : ℤ} (hv : |v| < 2 ^ 55)
    (hlo0 : 0 ≤ lo) (hlo1 : lo < 256) (hhi0 : 0 ≤ hi) (hhi1 : hi < 256)
    (h : ((lo + 32 * hi : ℤ) : ZMod p) = ((v + 4096 : ℤ) : ZMod p)) :
    lo + 32 * hi = v + 4096 ∧ -4096 ≤ v ∧ v < 4320 := by
  have hz : (((lo + 32 * hi - (v + 4096) : ℤ)) : ZMod p) = 0 := by
    push_cast at h ⊢; rw [h]; exact sub_self _
  have hb : |lo + 32 * hi - (v + 4096)| < (p : ℤ) := by
    rw [abs_lt] at hv ⊢; constructor <;> norm_num [p] at * <;> omega
  have he := eq_zero_of_cast_eq_zero hb hz
  omega

/-- The zero test: with `nz = v · inv` and the check `v · (1 − nz) = 0`, `nz` is `1` exactly when
`v ≠ 0` and `0` when `v = 0`, whatever inverse the prover supplies. -/
theorem zero_test_sound {F : Type} [Field F] (v inv : F) (h : v * (1 - v * inv) = 0) :
    (v ≠ 0 → v * inv = 1) ∧ (v = 0 → v * inv = 0) := by
  constructor
  · intro hv
    have := (mul_eq_zero.mp h).resolve_left hv
    exact (sub_eq_zero.mp this).symm
  · intro hv; simp [hv]

end IxAIAiur.Soundness

