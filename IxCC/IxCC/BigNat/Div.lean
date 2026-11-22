import IxCC.BigNat.Linear

/-! # BigNat Division and Remainder (`IxCC.BigNat.Div`)

Single-limb division (`divMod1`) and Knuth's Algorithm D normalized multi-limb
division (`divMod`, `div`, `mod`) over canonical little-endian `Array UInt64`,
matching Lean's `Nat.div`/`Nat.mod` total semantics (`n / 0 = 0`, `n % 0 = n`).

## Algorithms

- **Single-limb division (`divMod1`):** Top-down single pass calling `divWide64`
  per limb with carried remainder `rem < d` (erased proof witness; zero runtime cost).
- **Multi-limb division (`divModKnuth`, Knuth Algorithm D):**
  1. **D1 (Normalize):** Shift divisor `v` and dividend `u` left by `s = clz64 v[n-1]`
     so the normalized top divisor limb satisfies `vn[n-1] ≥ 2^63` (`B / 2`). Pad the
     normalized dividend `un` to exact length `m + n + 1`.
  2. **D3 (Trial quotient `q̂`):** Compute 2-by-1 trial quotient `divWide64 u2 u1 vn1`
     (or `2^64 - 1` when `u2 = vn1`), followed by the two-word refinement check
     `q̂ * vn2 > r̂ * B + u0` (at most 2 iterations since `vn1 ≥ B / 2`). By Knuth's
     Theorem B, `q_true ≤ q̂ ≤ q_true + 1`.
  3. **D4 (Multiply and subtract):** Subtract `q̂ * vn * B^j` from `rem[j .. j+n]` in place.
  4. **D5–D6 (Add-back):** In the rare case (`≤ 2/B`) where Step D4 borrows,
     decrement `q̂` by 1 and add `vn * B^j` back into `rem[j .. j+n]` in place.
  5. **D8 (Unnormalize):** Shift final remainder right by `s` bits and normalize `q`.

## Ownership & Bootstrap Contract

- Monomorphic, first-order, tail-recursive loops; zero `Nat` literals `≥ 2^63`.
- Quotient array `q` and working remainder `rem` are allocated once and mutated
  `@unique` in place; input operands `u`, `v`, `vn` are `@borrowed`.

## References

- Donald E. Knuth, *The Art of Computer Programming*, Vol. 2, §4.3.1
  (Algorithm D: Division of nonnegative integers; Theorem B).
- Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone, *Handbook of Applied
  Cryptography*, Ch. 14 (Algorithm 14.20 multiple-precision division).
- Richard P. Brent and Paul Zimmermann, *Modern Computer Arithmetic*, §1.4.
-/

namespace IxCC.BigNat

/-! ### Fast Single-Limb Division (`divMod1`) -/

/-- Top-down single-limb division loop processing limbs `k - 1` down to `0`
(`@borrowed a`, `@unique q`, erased proof `hrem : rem < d`). -/
def divMod1Loop (a : Array UInt64) (d : UInt64) :
    (k : Nat) → (rem : UInt64) → (rem < d) → Array UInt64 → Array UInt64 × UInt64
  | 0, rem, _, q => (normalize q, rem)
  | k + 1, rem, hrem, q =>
    let res := divWide64 rem (getLimb a k) d hrem
    have hrem' : res.2 < d := divWide64_snd_lt rem (getLimb a k) d hrem
    divMod1Loop a d k res.2 hrem' (setLimb q k res.1)

/-- Fast 1-limb division returning `(quotient, remainder)` for `d ≠ 0`.
When `d = 0`, returns `(#[] , 0)`. (`@borrowed a`). -/
def divMod1 (a : Array UInt64) (d : UInt64) : Array UInt64 × UInt64 :=
  if h : d = 0 then
    (#[] , 0)
  else
    have h0 : (0 : UInt64) < d := by
      rw [UInt64.lt_iff_toNat_lt]
      have hd : d.toNat ≠ 0 := fun hz => h (UInt64.toNat_inj.mp (by simpa using hz))
      have : (0 : UInt64).toNat = 0 := rfl
      omega
    divMod1Loop a d a.size 0 h0 (mkZeros a.size)

/-! ### Knuth Algorithm D Multi-Limb Division (`divMod`) -/

/-- Test whether the 128-bit value `(hi1, lo1)` is strictly greater than `(hi2, lo2)`. -/
@[inline] def cmpWideGt (hi1 lo1 hi2 lo2 : UInt64) : Bool :=
  hi1 > hi2 || (hi1 == hi2 && lo1 > lo2)

/-- Knuth D3 two-word quotient refinement: while `r̂ < B` and `q̂ * vn2 > r̂ * B + u0`,
decrement `q̂` and add `vn1` to `r̂`. Because `vn1 ≥ 2^63`, at most two decrements
can occur before `r̂` overflows `2^64`. -/
@[inline] def refineQhat (qh rh vn1 vn2 u0 : UInt64) : UInt64 :=
  let (pLo, pHi) := mulWide64 qh vn2
  if cmpWideGt pHi pLo rh u0 then
    let qh1 := qh - 1
    let (rh1, ov1) := addCarry64 rh vn1 false
    if ov1 then qh1
    else
      let (pLo1, pHi1) := mulWide64 qh1 vn2
      if cmpWideGt pHi1 pLo1 rh1 u0 then qh1 - 1 else qh1
  else qh

/-- Knuth D3 trial quotient estimate `q̂` from top 3 dividend limbs `(u2, u1, u0)`
and top 2 normalized divisor limbs `(vn1, vn2)`. -/
@[inline] def trialQhat (u2 u1 u0 vn1 vn2 : UInt64) : UInt64 :=
  if h : u2 < vn1 then
    let (qh, rh) := divWide64 u2 u1 vn1 h
    refineQhat qh rh vn1 vn2 u0
  else
    let (rh, ov) := addCarry64 u1 vn1 false
    if ov then maxWord64 else refineQhat maxWord64 rh vn1 vn2 u0

/-- Knuth D4 multiply-and-subtract in place: computes
`rem[j .. j+n] -= qhat * vn[0 .. n-1]`, returning `(rem', borrowOut)`
(`@unique rem`, `@borrowed vn`). -/
def subMulShiftLoop (rem vn : Array UInt64) (j n k : Nat) (qhat mulCarry : UInt64)
    (borrow : Bool) : Array UInt64 × Bool :=
  if _h : k < n then
    let (pLo, pHi) := mulWide64 qhat (getLimb vn k)
    let (prod, c1) := addCarry64 pLo mulCarry false
    let (nextMulCarry, _) := addCarry64 pHi 0 c1
    let (diff, borrow') := subBorrow64 (getLimb rem (j + k)) prod borrow
    subMulShiftLoop (setLimb rem (j + k) diff) vn j n (k + 1) qhat nextMulCarry borrow'
  else
    let (diffTop, finalBorrow) := subBorrow64 (getLimb rem (j + n)) mulCarry borrow
    (setLimb rem (j + n) diffTop, finalBorrow)
termination_by n - k

/-- Knuth D6 add-back in place: adds `vn[0 .. n-1]` into `rem[j .. j+n]`
(`@unique rem`, `@borrowed vn`). -/
def addShiftLoop (rem vn : Array UInt64) (j n k : Nat) (carry : Bool) : Array UInt64 :=
  if _h : k < n then
    let (s, c') := addCarry64 (getLimb rem (j + k)) (getLimb vn k) carry
    addShiftLoop (setLimb rem (j + k) s) vn j n (k + 1) c'
  else
    let (sTop, _) := addCarry64 (getLimb rem (j + n)) 0 carry
    setLimb rem (j + n) sTop
termination_by n - k

/-- One Knuth Algorithm D iteration at quotient position `j` (`@unique rem`, `@borrowed vn`, `@unique q`). -/
def knuthStep (rem vn q : Array UInt64) (j n : Nat) (vn1 vn2 : UInt64) :
    Array UInt64 × Array UInt64 :=
  let u2 := getLimb rem (j + n)
  let u1 := getLimb rem (j + n - 1)
  let u0 := getLimb rem (j + n - 2)
  let qhat := trialQhat u2 u1 u0 vn1 vn2
  let (rem1, borrow) := subMulShiftLoop rem vn j n 0 qhat 0 false
  if borrow then
    let rem2 := addShiftLoop rem1 vn j n 0 false
    (setLimb q j (qhat - 1), rem2)
  else
    (setLimb q j qhat, rem1)

/-- Main Knuth Algorithm D descending loop (`steps` = `m + 1` runs `j = m, m - 1, ..., 0`). -/
def knuthLoop (rem vn q : Array UInt64) (n : Nat) (vn1 vn2 : UInt64) :
    Nat → Array UInt64 × Array UInt64
  | 0 => (q, rem)
  | j + 1 =>
    let (q', rem') := knuthStep rem vn q j n vn1 vn2
    knuthLoop rem' vn q' n vn1 vn2 j

/-- Core Knuth Algorithm D for normalized `u`, `v` with `2 ≤ v.size ≤ u.size`. -/
def divModKnuth (u v : Array UInt64) : Array UInt64 × Array UInt64 :=
  let n := v.size
  let m := u.size - n
  let s := (clz64 (getLimb v (n - 1))).toNat
  let vn := shiftLeft v s
  let un := padZeros (shiftLeft u s) (m + n + 1)
  let vn1 := getLimb vn (n - 1)
  let vn2 := getLimb vn (n - 2)
  let (q, rem) := knuthLoop un vn (mkZeros (m + 1)) n vn1 vn2 (m + 1)
  (normalize q, shiftRight rem s)

/-- Total multi-precision Euclidean division returning `(u / v, u % v)`.
Matches Lean's `Nat.div` / `Nat.mod` on zero divisor: `divMod u 0 = (0, normalize u)`.
(`@borrowed u`, `@borrowed v`). -/
def divMod (u v : Array UInt64) : Array UInt64 × Array UInt64 :=
  let u' := normalize u
  let v' := normalize v
  if v'.size == 0 then
    (#[] , u')
  else if cmp u' v' == .lt then
    (#[] , u')
  else if v'.size == 1 then
    let (q, r) := divMod1 u' (getLimb v' 0)
    (q, ofUInt64 r)
  else
    divModKnuth u' v'

/-- Multi-precision quotient matching `Nat.div` (`@borrowed u`, `@borrowed v`). -/
@[inline] def div (u v : Array UInt64) : Array UInt64 :=
  (divMod u v).1

/-- Multi-precision remainder matching `Nat.mod` (`@borrowed u`, `@borrowed v`). -/
@[inline] def mod (u v : Array UInt64) : Array UInt64 :=
  (divMod u v).2

end IxCC.BigNat
