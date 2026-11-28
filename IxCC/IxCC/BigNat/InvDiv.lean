import IxCC.BigNat.Linear

/-! # Möller–Granlund 2-by-1 Precomputed-Reciprocal Division (`IxCC.BigNat.InvDiv`)

Replaces inner-loop hardware 128/64 `divWide64` instructions (~35–90 cycles on x86-64)
with 64×64 `mulWide64`-based reciprocal division (~10 cycles) following Niels Möller
and Torbjörn Granlund, *Improved Division by Invariant Integers*, IEEE Trans. Comput.
60(2):165–175, 2011 (Algorithm 4):

- `invert21 d hd`: computes `v = ⌊(2^128 - 1) / d⌋ - 2^64` for normalized `d ≥ 2^63`
  via ONE `divWide64 (maxWord64 - d) maxWord64 d`.
- `divRem21 u1 u0 d v`: computes exact `(q, r) = ((u1 * 2^64 + u0) / d, % d)` for
  `u1 < d`, `d ≥ 2^63`, `v = invert21 d` using ZERO hardware `div` instructions!
- `divMod1Inv a d`: fast single-limb multi-precision division using `invert21` +
  `divRem21` with on-the-fly bit shifting (zero temporary shifted array allocation).

## Bootstrap Contract

Monomorphic, first-order, structural recursion on `Nat` (zero `WellFounded.fix`),
zero `Nat` literals `≥ 2^63`, all inner loops `≤ 7` parameters. -/

namespace IxCC.BigNat

/-- Möller–Granlund 2-by-1 reciprocal `v = ⌊(2^128 - 1) / d⌋ - 2^64` for normalized
`d ≥ 2^63` (erased proof witness `hd`, single hardware `divWide64`). -/
@[inline] def invert21 (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) : UInt64 :=
  have hlt : maxWord64 - d < d := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le]
    · rw [maxWord64_toNat]; omega
    · rw [UInt64.le_iff_toNat_le, maxWord64_toNat]
      have := uint64_toNat_lt d
      omega
  (divWide64 (maxWord64 - d) maxWord64 d hlt).1

/-- Möller–Granlund Algorithm 4: exact 2-by-1 division `(u1 * 2^64 + u0) / d` returning
`(q, r)` for normalized `d ≥ 2^63`, `u1 < d`, and `v = invert21 d`. Uses ONLY
`mulWide64`, `UInt64.mul`, `addCarry64`, and comparisons — ZERO hardware `div`! -/
@[inline] def divRem21 (u1 u0 d v : UInt64) : UInt64 × UInt64 :=
  let (pLo, pHi) := mulWide64 v u1
  let (q0, c0) := addCarry64 pLo u0 false
  let (q1, _) := addCarry64 pHi u1 c0
  let q1 := q1 + 1
  let r := u0 - q1 * d
  let (q1, r) := if r > q0 then (q1 - 1, r + d) else (q1, r)
  if r ≥ d then (q1 + 1, r - d) else (q1, r)

/-- Normalized single-limb division loop (`d ≥ 2^63`, `v = invert21 d`), processing
limbs `k - 1` down to `0` (`@borrowed a`, `@unique q`). -/
def divMod1NormLoop (a : Array UInt64) (d v : UInt64) :
    Nat → UInt64 → Array UInt64 → Array UInt64 × UInt64
  | 0, rem, q => (normalize q, rem)
  | k + 1, rem, q =>
    let res := divRem21 rem (getLimb a k) d v
    divMod1NormLoop a d v k res.2 (setLimb q k res.1)

/-- On-the-fly shifted single-limb division loop (`0 < s < 64`, `dn = d <<< s ≥ 2^63`,
`v = invert21 dn`), processing limbs `k - 1` down to `0` with zero temporary buffer. -/
def divMod1ShiftLoop (a : Array UInt64) (dn v s : UInt64) :
    Nat → UInt64 → Array UInt64 → Array UInt64 × UInt64
  | 0, rem, q => (normalize q, rem >>> s)
  | k + 1, rem, q =>
    let invS := (64 : UInt64) - s
    let cur := getLimb a k
    let lo := if k == 0 then cur <<< s else (cur <<< s) ||| (getLimb a (k - 1) >>> invS)
    let res := divRem21 rem lo dn v
    divMod1ShiftLoop a dn v s k res.2 (setLimb q k res.1)

/-- Proof helper: shifting a nonzero `UInt64` left by `clz64 d` produces a word `≥ 2^63`. -/
theorem shiftLeft_clz64_ge (d : UInt64) (hd : d ≠ 0) :
    2 ^ 63 ≤ (d <<< clz64 d).toNat := by
  have hlt := clz64_lt_64 d hd
  have hnorm := clz64_shift_norm d hd
  rw [UInt64.toNat_shiftLeft]
  have hmod64 : (clz64 d).toNat % 64 = (clz64 d).toNat := Nat.mod_eq_of_lt hlt
  rw [hmod64, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt hnorm.2]
  exact hnorm.1

/-- Fast Möller–Granlund single-limb division returning `(a / d, a % d)` for `d ≠ 0`
(and `(#[] , 0)` for `d = 0`). Fast-paths `a.size = 0` and `a.size = 1`, and uses
`invert21` + `divRem21` with on-the-fly normalization for `a.size ≥ 2`. -/
def divMod1Inv (a : Array UInt64) (d : UInt64) : Array UInt64 × UInt64 :=
  if h : d = 0 then
    (#[] , 0)
  else if a.size == 0 then
    (#[] , 0)
  else if a.size == 1 then
    let v0 := getLimb a 0
    (ofUInt64 (v0 / d), v0 % d)
  else
    let s := clz64 d
    let dn := d <<< s
    let v := invert21 dn (shiftLeft_clz64_ge d h)
    if s == 0 then
      divMod1NormLoop a dn v a.size 0 (mkZeros a.size)
    else
      let invS := (64 : UInt64) - s
      let rem0 := getLimb a (a.size - 1) >>> invS
      divMod1ShiftLoop a dn v s a.size rem0 (mkZeros a.size)

end IxCC.BigNat
