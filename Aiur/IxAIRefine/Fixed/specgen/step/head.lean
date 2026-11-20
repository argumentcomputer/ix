import IxAIRefine.Fixed.Obs
import Mathlib.Tactic
import Mathlib.Algebra.Order.Group.Int

/-! # Specs of the leaf functions of `Fixed`

Every observed derivation (`ObsFn`) of a leaf function of the formal `Fixed` program computes
the intended integer fixed-point operation of `IxAICore.Fx`. A fixed-point number is represented
by its raw integer cast into the Goldilocks field (`fxVal`, which is `IxAIAiur.fx`).

* `UInt8` library: `UInt8::to_field` is the identity (`toField_spec`); `UInt8::from_fields`
  returns its two arguments, and they are bytes, because its `range_pair` lookup succeeds only
  on rows of the pair table (`rangePair_spec`, `fromFields_spec`); `UInt8::bit_decomposition`
  of a byte is its row of the bit table (`bitDecomposition_spec`).
* `shr8_spec`: for `|s| < 2^55`, `Fixed::shr8 s` is `⌊s / 256⌋`, which is `s >>> 8`
  (`shr8_eq`). The hinted quotient and remainder are pinned down by the range-checked bytes and
  `256 q + r = s`: both sides are integers far below the characteristic (`int_eq_of_cast_eq`).
* `sign_split_spec`: for `|v| < 2^55`, the flags are `[v ≥ 0]` and `[v ≠ 0]`.
* `mul_spec`, `relu_spec`, `pos_spec`: `Fx.mul`, `Fx.relu` and `Fx.pos`.
* `dot8_spec`, `dot16_spec`, `dot11_spec`, `dot20_spec`: `Fx.dot`, the exact integer sum of
  products rounded once, when that sum is below `2^55` in magnitude; `sum20_spec`: `Fx.sum`.

The magnitude bounds are hypotheses here; they follow from bounds on the model's weights and
data. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxAIStep.Fixed.Specs

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxAIStep.Fixed.Obs

/-- A fixed-point number as a field value: its raw integer, cast into the field. -/
def fxVal (x : IxAICore.Fx) : SourceValue F := .field ((x.raw : ℤ) : F)

theorem fxVal_eq_fx (x : IxAICore.Fx) : fxVal x = IxAIAiur.fx x := rfl

/-! ## Integers in the field -/

/-- Two integers closer than the characteristic are equal when their images in the field
are. -/
theorem int_eq_of_cast_eq {a b : ℤ} (hab : |a - b| < 18446744069414584321)
    (h : (a : F) = (b : F)) : a = b := by
  have h0 : ((a - b : ℤ) : F) = 0 := by rw [Int.cast_sub, h, sub_self]
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b)
    Aiur.Library.U32.Goldilocks.modulus).mp h0
  -- unverified: `exact_mod_cast` reads `((modulus : ℕ) : ℤ)` as the literal (the abbrev unfolds).
  have h2 : (18446744069414584321 : ℤ) ∣ a - b := by
    first | exact_mod_cast h1 | exact h1 | simpa using h1
  have := Int.eq_zero_of_abs_lt_dvd h2 hab
  omega

/-- `>>> 8` on integers is floor division by `256`. -/
theorem shr8_eq (x : ℤ) : x >>> (8 : ℕ) = x / 256 := by
  first
    | (rw [Int.shiftRight_eq_div_pow]; norm_num)
    | simp [Int.shiftRight_eq_div_pow]

/-! ## Field operations and projections -/

-- unverified (the three lemmas below): `evalBinOp` on two fields reduces by `whnf` or `simp`.
theorem add_ff {x y : F} {c : SourceValue F}
    (h : evalBinOp .add (.field x : SourceValue F) (.field y) = .ok c) : c = .field (x + y) := by
  first
    | exact (Except.ok.inj h).symm
    | (simp only [evalBinOp, Except.ok.injEq] at h; exact h.symm)
    | (simp [evalBinOp] at h; exact h.symm)

theorem sub_ff {x y : F} {c : SourceValue F}
    (h : evalBinOp .sub (.field x : SourceValue F) (.field y) = .ok c) : c = .field (x - y) := by
  first
    | exact (Except.ok.inj h).symm
    | (simp only [evalBinOp, Except.ok.injEq] at h; exact h.symm)
    | (simp [evalBinOp] at h; exact h.symm)

theorem mul_ff {x y : F} {c : SourceValue F}
    (h : evalBinOp .mul (.field x : SourceValue F) (.field y) = .ok c) : c = .field (x * y) := by
  first
    | exact (Except.ok.inj h).symm
    | (simp only [evalBinOp, Except.ok.injEq] at h; exact h.symm)
    | (simp [evalBinOp] at h; exact h.symm)

/-- A successful product with a field on the left has a field on the right. -/
theorem mul_right_field {x : F} {b c : SourceValue F}
    (h : evalBinOp .mul (.field x : SourceValue F) b = .ok c) : ∃ y, b = .field y := by
  cases b
  case field y => exact ⟨y, rfl⟩
  all_goals simp [evalBinOp] at h

theorem proj_ok {items : List (SourceValue F)} {i : ℕ} {v : SourceValue F}
    (h : projectValue (.tuple items : SourceValue F) i = .ok v) : items[i]? = some v := by
  -- unverified: `simp` unfolds the `do` block of `projectValue` over `Except`.
  cases found : items[i]? with
  | none => simp [projectValue, found] at h <;> cases h
  | some w =>
    simp [projectValue, found, pure, Except.pure] at h
    simp [h]

theorem mem_zip_map {α β γ : Type} {l : List α} {f : α → β} {g : α → γ} {b : β} {c : γ}
    (hm : (b, c) ∈ (l.map f).zip (l.map g)) : ∃ a ∈ l, f a = b ∧ g a = c := by
  rw [List.zip_map'] at hm
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  exact ⟨a, ha, he.1, he.2⟩

theorem dotRaw_cons (a b : IxAICore.Fx) (xs ys : List IxAICore.Fx) :
    IxAICore.Fx.dotRaw (a :: xs) (b :: ys) = a.raw * b.raw + IxAICore.Fx.dotRaw xs ys := by
  first | rfl | simp [IxAICore.Fx.dotRaw]

theorem dotRaw_nil : IxAICore.Fx.dotRaw [] [] = 0 := by
  first | rfl | simp [IxAICore.Fx.dotRaw]

theorem sumRaw_cons (a : IxAICore.Fx) (xs : List IxAICore.Fx) :
    IxAICore.Fx.sumRaw (a :: xs) = a.raw + IxAICore.Fx.sumRaw xs := by
  first | rfl | simp [IxAICore.Fx.sumRaw]

theorem sumRaw_nil : IxAICore.Fx.sumRaw [] = 0 := by
  first | rfl | simp [IxAICore.Fx.sumRaw]

