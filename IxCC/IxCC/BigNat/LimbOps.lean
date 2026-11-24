/-! # Hardware 64-bit Limb Primitives (`IxCC.BigNat.LimbOps`)

Clean-room specification and pure-Lean reference definitions of the five 64-bit
hardware limb primitives used by `IxCC.BigNat`:

1. `addCarry64 (a b : UInt64) (c : Bool) : UInt64 × Bool` — 64-bit add with carry (`adc`)
2. `subBorrow64 (a b : UInt64) (bIn : Bool) : UInt64 × Bool` — 64-bit subtract with borrow (`sbb`)
3. `mulWide64 (a b : UInt64) : UInt64 × UInt64` — full 64×64 → 128-bit product returning `(lo, hi)` (`mul`)
4. `divWide64 (hi lo d : UInt64) (h : hi < d) : UInt64 × UInt64` — 128/64 division returning `(q, r)` (`div`)
5. `clz64 (x : UInt64) : UInt64` — count leading zeros, `clz64 0 = 64` (`lzcnt` / `bsr`)

## Conventions & Bootstrap Contract

- **Pair order:** `mulWide64` returns `(lo, hi)` (little-endian, matching `(lo, carry)`
  in `addCarry64`, `(lo, borrow)` in `subBorrow64`, little-endian limb arrays, and
  x86-64 `mul` `(RAX = lo, RDX = hi)`). `divWide64` returns `(q, r)` (matching x86-64
  `div r/m64` `(RAX = q, RDX = r)`).
- **Bootstrap pinning:** These five definitions intentionally pass through `Nat` so
  their Lean bodies ARE their exact mathematical specifications (`docs/bignum-design.md`,
  "What the library needs from earlier phases"). Wave 2 (`word-w2`) pins these five
  definitions to single x86-64 instructions; every other runtime function in `IxCC.BigNat`
  operates exclusively on `UInt64`, these five primitives, and small `Nat` indices `< 2^63`.
- **Ownership contract:** All arguments are raw scalar words (`UInt64` / `Bool`), requiring
  no heap allocation or reference-count operations.

## References

- Donald E. Knuth, *The Art of Computer Programming*, Vol. 2: *Seminumerical Algorithms*,
  §4.3.1 (Multiple-Precision Arithmetic).
- Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone, *Handbook of Applied Cryptography*,
  Ch. 14 (Efficient Implementation).
- Richard P. Brent and Paul Zimmermann, *Modern Computer Arithmetic*, §1.3–1.4.
- `IxCC/docs/bignum-design.md` (Scope, Representation, Proof obligation Layer 1).
-/

namespace IxCC.BigNat

/-- The limb radix `2 ^ 64`, used only in specifications and proofs (never in runtime code). -/
abbrev BASE : Nat := 2 ^ 64

/-- All-ones 64-bit word (`2^64 - 1`), constructed without any `Nat` literal `≥ 2^63`. -/
@[inline] def maxWord64 : UInt64 := (0 : UInt64) - 1

/-- 64-bit unsigned addition with carry-in, returning `(lo, carryOut)`.
Intended x86-64 lowering: `adc`. -/
@[inline] def addCarry64 (a b : UInt64) (c : Bool) : UInt64 × Bool :=
  let s : Nat := a.toNat + b.toNat + c.toNat
  (UInt64.ofNat s, decide (2 ^ 64 ≤ s))

/-- 64-bit unsigned subtraction with borrow-in, returning `(lo, borrowOut)`.
`borrowOut = true` iff `a < b + bIn`. Intended x86-64 lowering: `sbb`. -/
@[inline] def subBorrow64 (a b : UInt64) (bIn : Bool) : UInt64 × Bool :=
  let sub : Nat := b.toNat + bIn.toNat
  let borrow : Bool := decide (a.toNat < sub)
  let diff : Nat := if a.toNat < sub then 2 ^ 64 + a.toNat - sub else a.toNat - sub
  (UInt64.ofNat diff, borrow)

/-- Full 64×64 → 128-bit unsigned multiplication returning `(lo, hi)` (little-endian:
`lo` is bits `[0..63]`, `hi` is bits `[64..127]`, matching x86-64 `mul` `(RAX, RDX)`). -/
@[inline] def mulWide64 (a b : UInt64) : UInt64 × UInt64 :=
  let p : Nat := a.toNat * b.toNat
  (UInt64.ofNat (p % 2 ^ 64), UInt64.ofNat (p / 2 ^ 64))

/-- 128-by-64 unsigned division `(hi * 2^64 + lo) / d` returning `(q, r)` under the
no-overflow precondition `hi < d` (which ensures `0 < d` and `q < 2^64`, matching
x86-64 `div r/m64` `(RAX = q, RDX = r)`). -/
@[inline] def divWide64 (hi lo d : UInt64) (_h : hi < d) : UInt64 × UInt64 :=
  let num : Nat := hi.toNat * 2 ^ 64 + lo.toNat
  (UInt64.ofNat (num / d.toNat), UInt64.ofNat (num % d.toNat))

/-- Count leading zeros in a 64-bit unsigned word, with `clz64 0 = 64`.
Intended x86-64 lowering: `lzcnt` (or `bsr` with zero guard). -/
@[inline] def clz64 (x : UInt64) : UInt64 :=
  if x == 0 then 64 else UInt64.ofNat (63 - Nat.log2 x.toNat)

/-- Derived runtime helper: compute `a * b + acc + carry` as `(lo, hi)` using only
`mulWide64`, `addCarry64 _ _ false`, and raw 64-bit word additions (zero `Nat` arithmetic
and zero intermediate `Prod` allocations under ANF shrinking). Since
`(2^64 - 1)^2 + 2*(2^64 - 1) = 2^128 - 1 < 2^128`, the high word never overflows. -/
@[inline] def mulAddCarry64 (a b acc carry : UInt64) : UInt64 × UInt64 :=
  let p := mulWide64 a b
  let r1 := addCarry64 p.1 acc false
  let r2 := addCarry64 r1.1 carry false
  let c1 : UInt64 := if r1.2 then 1 else 0
  let c2 : UInt64 := if r2.2 then 1 else 0
  (r2.1, p.2 + c1 + c2)

/-! ### Exact Algebraic Specifications -/

theorem uint64_toNat_lt (x : UInt64) : x.toNat < 2 ^ 64 := x.toBitVec.isLt

theorem maxWord64_toNat : maxWord64.toNat = 2 ^ 64 - 1 := by
  unfold maxWord64
  rw [UInt64.toNat_sub]
  rfl

theorem bool_toNat_le_one (b : Bool) : b.toNat ≤ 1 := by
  cases b <;> decide

theorem addCarry64_spec (a b : UInt64) (c : Bool) :
    (addCarry64 a b c).1.toNat + (addCarry64 a b c).2.toNat * 2 ^ 64 =
      a.toNat + b.toNat + c.toNat := by
  unfold addCarry64
  have ha : a.toNat < 2 ^ 64 := uint64_toNat_lt a
  have hb : b.toNat < 2 ^ 64 := uint64_toNat_lt b
  have hc : c.toNat ≤ 1 := bool_toNat_le_one c
  simp only [UInt64.toNat_ofNat']
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat
  · simp only [h, decide_true, Bool.toNat_true, Nat.one_mul]
    have hmod : (a.toNat + b.toNat + c.toNat) % 2 ^ 64 = a.toNat + b.toNat + c.toNat - 2 ^ 64 := by
      omega
    omega
  · simp only [h, decide_false, Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
    exact Nat.mod_eq_of_lt (by omega)

theorem subBorrow64_spec (a b : UInt64) (bIn : Bool) :
    (subBorrow64 a b bIn).1.toNat + b.toNat + bIn.toNat =
      a.toNat + (subBorrow64 a b bIn).2.toNat * 2 ^ 64 := by
  unfold subBorrow64
  have ha : a.toNat < 2 ^ 64 := uint64_toNat_lt a
  have hb : b.toNat < 2 ^ 64 := uint64_toNat_lt b
  have hbi : bIn.toNat ≤ 1 := bool_toNat_le_one bIn
  simp only [UInt64.toNat_ofNat']
  by_cases h : a.toNat < b.toNat + bIn.toNat
  · simp only [h, ↓reduceIte, decide_true, Bool.toNat_true, Nat.one_mul]
    have hlt : 2 ^ 64 + a.toNat - (b.toNat + bIn.toNat) < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega
  · simp only [h, ↓reduceIte, decide_false, Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
    have hlt : a.toNat - (b.toNat + bIn.toNat) < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

theorem mulWide64_spec (a b : UInt64) :
    (mulWide64 a b).1.toNat + (mulWide64 a b).2.toNat * 2 ^ 64 = a.toNat * b.toNat := by
  unfold mulWide64
  have ha : a.toNat < 2 ^ 64 := uint64_toNat_lt a
  have hb : b.toNat < 2 ^ 64 := uint64_toNat_lt b
  have hdiv : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64)]
    have h1 : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  simp only [UInt64.toNat_ofNat']
  rw [Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), Nat.mod_eq_of_lt hdiv]
  have hdm := Nat.div_add_mod (a.toNat * b.toNat) (2 ^ 64)
  omega

theorem divWide64_div_lt (hi lo d : UInt64) (h : hi < d) :
    (hi.toNat * 2 ^ 64 + lo.toNat) / d.toNat < 2 ^ 64 := by
  have hlt : hi.toNat < d.toNat := UInt64.lt_iff_toNat_lt.mp h
  have hd : 0 < d.toNat := by omega
  have hlo : lo.toNat < 2 ^ 64 := uint64_toNat_lt lo
  rw [Nat.div_lt_iff_lt_mul hd]
  have hle : hi.toNat + 1 ≤ d.toNat := hlt
  have hmul : (hi.toNat + 1) * 2 ^ 64 ≤ d.toNat * 2 ^ 64 := Nat.mul_le_mul_right _ hle
  omega

theorem divWide64_fst (hi lo d : UInt64) (h : hi < d) :
    (divWide64 hi lo d h).1.toNat = (hi.toNat * 2 ^ 64 + lo.toNat) / d.toNat := by
  unfold divWide64
  simp only [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (divWide64_div_lt hi lo d h)

theorem divWide64_snd (hi lo d : UInt64) (h : hi < d) :
    (divWide64 hi lo d h).2.toNat = (hi.toNat * 2 ^ 64 + lo.toNat) % d.toNat := by
  unfold divWide64
  have hlt : hi.toNat < d.toNat := UInt64.lt_iff_toNat_lt.mp h
  have hd : 0 < d.toNat := by omega
  have hdlt : d.toNat < 2 ^ 64 := uint64_toNat_lt d
  simp only [UInt64.toNat_ofNat']
  have hmod : (hi.toNat * 2 ^ 64 + lo.toNat) % d.toNat < d.toNat := Nat.mod_lt _ hd
  exact Nat.mod_eq_of_lt (Nat.lt_trans hmod hdlt)

theorem divWide64_snd_lt (hi lo d : UInt64) (h : hi < d) :
    (divWide64 hi lo d h).2 < d := by
  rw [UInt64.lt_iff_toNat_lt, divWide64_snd]
  have hlt : hi.toNat < d.toNat := UInt64.lt_iff_toNat_lt.mp h
  exact Nat.mod_lt _ (by omega)

theorem divWide64_spec (hi lo d : UInt64) (h : hi < d) :
    (divWide64 hi lo d h).1.toNat * d.toNat + (divWide64 hi lo d h).2.toNat =
      hi.toNat * 2 ^ 64 + lo.toNat ∧
    (divWide64 hi lo d h).2.toNat < d.toNat := by
  rw [divWide64_fst, divWide64_snd]
  have hlt : hi.toNat < d.toNat := UInt64.lt_iff_toNat_lt.mp h
  have hd : 0 < d.toNat := by omega
  constructor
  · have hdm := Nat.div_add_mod (hi.toNat * 2 ^ 64 + lo.toNat) d.toNat
    rw [Nat.mul_comm]
    exact hdm
  · exact Nat.mod_lt _ hd

theorem clz64_zero : clz64 0 = 64 := by decide

theorem clz64_toNat_of_ne_zero (x : UInt64) (hx : x ≠ 0) :
    (clz64 x).toNat = 63 - Nat.log2 x.toNat := by
  unfold clz64
  have hbeq : (x == 0) = false := beq_false_of_ne hx
  simp only [hbeq, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem clz64_lt_64 (x : UInt64) (hx : x ≠ 0) : (clz64 x).toNat < 64 := by
  rw [clz64_toNat_of_ne_zero x hx]
  omega

theorem clz64_le_64 (x : UInt64) : (clz64 x).toNat ≤ 64 := by
  by_cases hx : x = 0
  · subst hx; decide
  · exact Nat.le_of_lt (clz64_lt_64 x hx)

theorem log2_uint64_lt_64 (x : UInt64) : Nat.log2 x.toNat < 64 := by
  by_cases hx : x.toNat = 0
  · rw [hx]; decide
  · exact (Nat.log2_lt hx).mpr (uint64_toNat_lt x)

theorem clz64_spec (x : UInt64) (hx : x ≠ 0) :
    2 ^ (63 - (clz64 x).toNat) ≤ x.toNat ∧ x.toNat < 2 ^ (64 - (clz64 x).toNat) := by
  have hx0 : x.toNat ≠ 0 := by
    intro h0
    apply hx
    exact UInt64.toNat_inj.mp (by simpa using h0)
  have hlog : Nat.log2 x.toNat < 64 := log2_uint64_lt_64 x
  have hclz : (clz64 x).toNat = 63 - Nat.log2 x.toNat := clz64_toNat_of_ne_zero x hx
  have h1 : 63 - (clz64 x).toNat = Nat.log2 x.toNat := by omega
  have h2 : 64 - (clz64 x).toNat = Nat.log2 x.toNat + 1 := by omega
  rw [h1, h2]
  constructor
  · exact (Nat.le_log2 hx0).mp (Nat.le_refl _)
  · exact (Nat.log2_lt hx0).mp (Nat.lt_succ_self _)

theorem clz64_shift_norm (x : UInt64) (hx : x ≠ 0) :
    2 ^ 63 ≤ x.toNat * 2 ^ (clz64 x).toNat ∧ x.toNat * 2 ^ (clz64 x).toNat < 2 ^ 64 := by
  have ⟨hlo, hhi⟩ := clz64_spec x hx
  have hlt : (clz64 x).toNat < 64 := clz64_lt_64 x hx
  have hpos : 0 < 2 ^ (clz64 x).toNat := Nat.two_pow_pos _
  constructor
  · have h1 := Nat.mul_le_mul_right (2 ^ (clz64 x).toNat) hlo
    rw [← Nat.pow_add] at h1
    have heq : 63 - (clz64 x).toNat + (clz64 x).toNat = 63 := by omega
    rw [heq] at h1
    exact h1
  · have h2 := Nat.mul_lt_mul_of_pos_right hhi hpos
    rw [← Nat.pow_add] at h2
    have heq : 64 - (clz64 x).toNat + (clz64 x).toNat = 64 := by omega
    rw [heq] at h2
    exact h2

private theorem mulAddCarry64_hi_lt {B a b acc carry pLo pHi s1 c1 s2 c2 : Nat}
    (hbound : a * b + acc + carry < B * B)
    (hmul : pLo + pHi * B = a * b)
    (hs1 : s1 + c1 * B = pLo + acc)
    (hs2 : s2 + c2 * B = s1 + carry) :
    s2 + (pHi + c1 + c2) * B = a * b + acc + carry ∧ pHi + c1 + c2 < B := by
  have htot : s2 + (pHi + c1 + c2) * B = a * b + acc + carry := by
    rw [Nat.add_mul, Nat.add_mul]; omega
  have hlt : (pHi + c1 + c2) * B < B * B := by omega
  have hhi : pHi + c1 + c2 < B :=
    match Nat.lt_or_ge (pHi + c1 + c2) B with
    | Or.inl h => h
    | Or.inr h => False.elim ((Nat.not_le_of_gt hlt) (Nat.mul_le_mul_right B h))
  exact ⟨htot, hhi⟩

theorem mulAddCarry64_spec (a b acc carry : UInt64) :
    (mulAddCarry64 a b acc carry).1.toNat + (mulAddCarry64 a b acc carry).2.toNat * 2 ^ 64 =
      a.toNat * b.toNat + acc.toNat + carry.toNat := by
  unfold mulAddCarry64
  dsimp only
  have ha : a.toNat < 2 ^ 64 := uint64_toNat_lt a
  have hb : b.toNat < 2 ^ 64 := uint64_toNat_lt b
  have hacc : acc.toNat < 2 ^ 64 := uint64_toNat_lt acc
  have hcar : carry.toNat < 2 ^ 64 := uint64_toNat_lt carry
  have hbound : a.toNat * b.toNat + acc.toNat + carry.toNat < 2 ^ 64 * 2 ^ 64 := by
    have hprod : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hmul := mulWide64_spec a b
  have hs1 := addCarry64_spec (mulWide64 a b).1 acc false
  have hs2 := addCarry64_spec (addCarry64 (mulWide64 a b).1 acc false).1 carry false
  have hf : false.toNat = 0 := rfl
  rw [hf, Nat.add_zero] at hs1 hs2
  have ⟨htot, hlt⟩ := mulAddCarry64_hi_lt hbound hmul hs1 hs2
  have hc : ∀ x : Bool, (if x then (1 : UInt64) else 0).toNat = x.toNat := by
    intro x; cases x <;> rfl
  have hc1 := hc (addCarry64 (mulWide64 a b).1 acc false).2
  have hc2 := hc (addCarry64 (addCarry64 (mulWide64 a b).1 acc false).1 carry false).2
  have hadd : ∀ (x y : UInt64), x.toNat + y.toNat < 2 ^ 64 → (x + y).toNat = x.toNat + y.toNat := by
    intro x y hxy
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt hxy
  have h1 := hadd (mulWide64 a b).2 (if (addCarry64 (mulWide64 a b).1 acc false).2 then 1 else 0)
    (by rw [hc1]; exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt)
  have h2 := hadd ((mulWide64 a b).2 + if (addCarry64 (mulWide64 a b).1 acc false).2 then 1 else 0)
    (if (addCarry64 (addCarry64 (mulWide64 a b).1 acc false).1 carry false).2 then 1 else 0)
    (by rw [h1, hc1, hc2]; exact hlt)
  rw [h2, h1, hc1, hc2]
  exact htot

end IxCC.BigNat
