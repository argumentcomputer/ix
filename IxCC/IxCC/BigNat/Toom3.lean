import IxCC.BigNat.Linear

/-! # Toom-Cook 3-Way Building Blocks (`IxCC.BigNat.Toom3`)

Formally verified building blocks for balanced Toom-Cook 3-way multiplication and
squaring (`mulToom3`, `sqrToom3`):
- **`divExact3`:** Linear-time exact division by `3` using the modular inverse
  `inv3_64 = (2 * 2^64 + 1) / 3 = 0xAAAAAAAAAAAAAAAB` (0 hardware `div`s; 1 `imul` +
  1 `mulWide64` per limb).
- **`signedSub`:** Unsigned magnitude and sign of `a - b` (`(a < b, |a - b|)`).
- **`toom3Combine`:** Single-allocation, in-place recombination of the 5 Toom-3 output
  coefficients `c0 + c1·B^k + c2·B^(2k) + c3·B^(3k) + c4·B^(4k)` using `copyIntoZeros`
  and `addAtInPlace` (zero `shiftLimbs` allocations).
- **`toom3Interp`:** Exact 5-point Toom-3 interpolation over `{0, 1, -1, 2, ∞}` where
  EVERY intermediate value (`t024, c2, t13, u, u - t13, c3, c1`) is strictly
  nonnegative (`≥ 0`), mutating freshly owned intermediates in place via `subAtInPlace`
  and `subMul1InPlace`.

## Ownership & Bootstrap Contract

- All loops use structural recursion on `Nat`, with `≤ 5` runtime parameters.
- No `Nat` literal `≥ 2^63` (`inv3_64` is built via 32-bit halves).
- `toom3Interp` consumes freshly allocated evaluation results `r2` (and fresh
  intermediates `hi`, `lo`, `u`) linearly in place; `r0`, `r1`, `rm1`, `rInf` are
  `@borrowed`.

## References

- Marco Bodrato, *Towards Optimal Toom-Cook Multiplication for Univariate and
  Multivariate Polynomials in Characteristic 2 and 0*, WAIFI 2007 / LNCS 4547.
- Richard P. Brent and Paul Zimmermann, *Modern Computer Arithmetic*, §1.3.3.
- Torbjörn Granlund and Peter L. Montgomery, *Division by Invariant Integers using
  Multiplication*, PLDI 1994.
-/

namespace IxCC.BigNat

/-! ### Exact Division by 3 (`divExact3`) -/

/-- Modular multiplicative inverse of `3` modulo `2^64`: `0xAAAAAAAAAAAAAAAB`,
satisfying `3 * inv3_64 = 2 * 2^64 + 1 ≡ 1 (mod 2^64)`. Constructed from 32-bit halves
so no `Nat` literal `≥ 2^63` appears. -/
@[inline] def inv3_64 : UInt64 :=
  ((0xAAAAAAAA : UInt64) <<< 32) ||| (0xAAAAAAAB : UInt64)

/-- Linear exact-division-by-3 loop (`@borrowed a`, `@unique acc`, structural recursion
on `rem`, 0 hardware `div`s). Maintains `carry ≤ 2`. -/
def divExact3Loop (a : Array UInt64) (i : Nat) (carry : UInt64) (acc : Array UInt64) :
    Nat → Array UInt64
  | 0 => acc
  | rem + 1 =>
    let (diff, borrow) := subBorrow64 (getLimb a i) carry false
    let q := diff * inv3_64
    let (_, pHi) := mulWide64 q 3
    let carry' := if borrow then pHi + 1 else pHi
    divExact3Loop a (i + 1) carry' (acc.push q) rem

/-- Exact division by `3` (`@borrowed a`): whenever `3 ∣ toNat a`, returns canonical
`WF` quotient with `toNat (divExact3 a) * 3 = toNat a` (zero hardware `div`s). -/
def divExact3 (a : Array UInt64) : Array UInt64 :=
  if a.size == 0 then #[]
  else normalize (divExact3Loop a 0 0 (Array.mkEmpty a.size) a.size)

/-! ### Signed Difference (`signedSub`) & Size Bounds -/

/-- Return `(isNeg, |a - b|)` for canonical `a`, `b` (`@borrowed a`, `@borrowed b`),
where `isNeg = true` iff `toNat a < toNat b`. -/
def signedSub (a b : Array UInt64) : Bool × Array UInt64 :=
  match cmp a b with
  | .lt => (true, subRaw b a)
  | .eq => (false, #[])
  | .gt => (false, subRaw a b)

/-- Shared Toom-3 3-way slice & evaluation helper: extracts `(a0, a1, a2)` at radix `B^k`
in 3 structural steps (single `slice` site) and returns `(a0, a2, p1, pm1Neg, pm1, p2)`
where `p1 = a0+a1+a2`, `(pm1Neg, pm1) = signedSub (a0+a2) a1`, `p2 = a0+2a1+4a2`. -/
def toom3EvalLoop (a : Array UInt64) (k : Nat) (a0 a1 a2 : Array UInt64) :
    Nat → Array UInt64 × Array UInt64 × Array UInt64 × Bool × Array UInt64 × Array UInt64
  | 0 =>
    let p02 := add a0 a2
    let p1  := add p02 a1
    let pm1 := signedSub p02 a1
    let p2  := add (shiftLeft1 (add (shiftLeft1 a2) a1)) a0
    (a0, a2, p1, pm1.1, pm1.2, p2)
  | step + 1 =>
    let (lo, hi) :=
      if step == 2 then (0, k)
      else if step == 1 then (k, 2 * k)
      else (2 * k, a.size)
    let chunk := normalize (slice a lo hi)
    let (a0', a1', a2') :=
      if step == 2 then (chunk, a1, a2)
      else if step == 1 then (a0, chunk, a2)
      else (a0, a1, chunk)
    toom3EvalLoop a k a0' a1' a2' step

/-! ### In-Place Karatsuba Recombination (`karatsubaCombine`) -/

/-- In-place Karatsuba middle-term subtraction and shifted recombination
`z0 + (z1Full - z0 - z2) * B^m + z2 * B^(2m)`, mutating freshly owned `z1Full`
in place and allocating a single `outSize`-limb output buffer (`@borrowed z0`,
`@borrowed z2`, `@unique z1Full`). -/
def karatsubaCombine (z0 z2 z1Full : Array UInt64) (m outSize : Nat) : Array UInt64 :=
  let z1a := (subAtInPlace z1Full z0 0).1
  let z1b := (subAtInPlace z1a z2 0).1
  let z1 := normalize z1b
  let acc0 := copyIntoZeros z0 outSize
  let acc1 := addAtInPlace acc0 z1 m
  let acc2 := addAtInPlace acc1 z2 (2 * m)
  normalize acc2

/-! ### Toom-3 In-Place Recombination & 5-Point Nonnegative Interpolation -/

/-- Tail-recursive shifted recombination loop adding `c1·B^k + c2·B^(2k) + c3·B^(3k) + c4·B^(4k)`
into `@unique acc` via a single `addAtInPlace` site (keeps ANF globals compact). -/
def toom3CombineLoop (c1 c2 c3 c4 : Array UInt64) (k : Nat) (acc : Array UInt64) :
    Nat → Array UInt64
  | 0 => normalize acc
  | step + 1 =>
    let (term, mult) :=
      if step == 3 then (c1, 1)
      else if step == 2 then (c2, 2)
      else if step == 1 then (c3, 3)
      else (c4, 4)
    toom3CombineLoop c1 c2 c3 c4 k (addAtInPlace acc term (mult * k)) step

/-- Recombine the 5 Toom-3 coefficients `c0 + c1·B^k + c2·B^(2k) + c3·B^(3k) + c4·B^(4k)`
into a single pre-sized buffer via in-place `addAtInPlace` (`@borrowed c0..c4`). -/
def toom3Combine (c0 c1 c2 c3 c4 : Array UInt64) (k outSize : Nat) : Array UInt64 :=
  toom3CombineLoop c1 c2 c3 c4 k (copyIntoZeros c0 outSize) 4

/-- Tail-recursive in-place linear subtraction loop subtracting up to 3 scaled terms from
`@unique acc` and normalizing (single `subAtInPlace` + single `subMul1InPlace` site). -/
def subMul3Loop (a b c : Array UInt64) (m1 m2 m3 : UInt64) (acc : Array UInt64) :
    Nat → Array UInt64
  | 0 => normalize acc
  | step + 1 =>
    let (term, mult) :=
      if step == 2 then (a, m1)
      else if step == 1 then (b, m2)
      else (c, m3)
    let next :=
      if mult == 0 then acc
      else if mult == 1 then (subAtInPlace acc term 0).1
      else (subMul1InPlace acc term mult).1
    subMul3Loop a b c m1 m2 m3 next step

/-- Exact 5-point Toom-3 interpolation over `{0, 1, -1, 2, ∞}`:
- `r0   = C(0)  = c0` (`@borrowed`)
- `r1   = C(1)  = c0 + c1 + c2 + c3 + c4` (`@borrowed`)
- `rm1  = |C(-1)|` with sign `rm1Neg` (`@borrowed`)
- `r2   = C(2)  = c0 + 2·c1 + 4·c2 + 8·c3 + 16·c4` (`@unique`, mutated in place!)
- `rInf = C(∞)  = c4` (`@borrowed`)

Every intermediate (`hi, lo, c2, u, diff3, c3, c1`) is nonnegative (`≥ 0`), avoiding
signed limb arithmetic completely. -/
def toom3Interp (r0 r1 rm1 r2 rInf : Array UInt64) (rm1Neg : Bool) (k outSize : Nat) :
    Array UInt64 :=
  -- Step 1: hi = max(c0+c2+c4, c1+c3) = (r1 + rm1) / 2, lo = hi - rm1 = min(...)
  let hi := shiftRight1 (add r1 rm1)
  let lo := subRaw hi rm1
  let t024 := if rm1Neg then lo else hi
  let t13  := if rm1Neg then hi else lo
  -- Step 2: c2 = t024 - c0 - c4 (t024 is linearly owned now!)
  let c2 := subMul3Loop #[] r0 rInf 0 1 1 t024 2
  -- Step 3: u = c1 + 4*c3 = (r2 - c0 - 4*c2 - 16*c4) / 2 (r2 is linearly owned!)
  let u := shiftRight1 (subMul3Loop r0 c2 rInf 1 4 16 r2 3)
  -- Step 4: c3 = (u - t13) / 3 (u is linearly owned; 3 divides u - t13 exactly!)
  let c3 := divExact3 (subMul3Loop #[] #[] t13 0 0 1 u 1)
  -- Step 5: c1 = t13 - c3 (t13 is linearly owned now!)
  let c1 := subMul3Loop #[] #[] c3 0 0 1 t13 1
  -- Step 6: Recombine c0 + c1*B^k + c2*B^(2k) + c3*B^(3k) + c4*B^(4k)
  toom3Combine r0 c1 c2 c3 rInf k outSize

end IxCC.BigNat
