import IxCC.BigNat.Linear
import IxCC.BigNat.Toom3

/-! # BigNat Multiplication, Squaring, Karatsuba, and Exponentiation (`IxCC.BigNat.Mul`)

Multi-precision multiplication (`mulSchoolbook`, `mulKaratsuba`, `mul`), dedicated
squaring (`sqrSchoolbook`, `sqrKaratsuba`, `sqr`), and left-to-right binary
exponentiation (`pow`) over canonical little-endian `Array UInt64`.

## Algorithms & Complexity

- **Schoolbook multiplication (`mulSchoolbook`):** Standard `O(m·n)` row-by-row
  multiply-accumulate using `mulAddCarry64` (`mulWide64` + `addCarry64`), mutating
  the pre-allocated product array in place.
- **Dedicated squaring (`sqrSchoolbook`):** Three-pass symmetric squaring:
  (1) accumulate strictly upper-triangular cross terms `∑_{i < j} a_i · a_j · B^{i+j}`
  (`n(n-1)/2` products), (2) double in place via `addCarry64 v v c`, (3) add diagonal
  squares `∑_i a_i^2 · B^{2i}` in a single linear carry sweep. Avoids 129-bit inner-loop
  carry overflow while cutting products nearly in half.
- **Karatsuba (`mulKaratsuba`, `sqrKaratsuba`, threshold `K = 32` limbs):**
  Unsigned three-product Karatsuba identity
  `z₁ = (a₀ + a₁)(b₀ + b₁) - z₀ - z₂` (nonnegative by construction, requiring no
  signed limb arithmetic), terminating structurally on `max a.size b.size`.
- **Exponentiation (`pow`):** Left-to-right binary squaring using `sqr` and `mul`.

## Ownership & Bootstrap Contract

- All functions are monomorphic, first-order, and tail-recursive (except the
  structurally terminating Karatsuba recursion of depth `O(log n)`).
- No `Nat` literal or intermediate value `≥ 2^63` is constructed.
- Operands `a`, `b`, `base` are `@borrowed`; product accumulators `acc` are
  allocated once and mutated `@unique` in place.

## References

- Donald E. Knuth, *The Art of Computer Programming*, Vol. 2, §4.3.1 (Algorithm M),
  §4.3.3 (Karatsuba's method), §4.6.3 (Evaluation of powers, binary method).
- Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone, *Handbook of Applied
  Cryptography*, Ch. 14 (Algorithm 14.12 multiplication; Algorithm 14.16 squaring;
  Algorithm 14.79 left-to-right binary exponentiation).
- Richard P. Brent and Paul Zimmermann, *Modern Computer Arithmetic*, §1.3.1–1.3.2.
-/

namespace IxCC.BigNat

/-- Karatsuba limb threshold (`K = 32` limbs = 2048 bits). Any value `≥ 5` is valid
and proved unconditionally correct. -/
def karatsubaThreshold : Nat := 32

/-- Toom-Cook 3-way limb threshold (`T = 96` limbs = 6144 bits). Any value `≥ 12` is
valid and proved unconditionally correct. -/
def toom3Threshold : Nat := 96

/-! ### Schoolbook Multiplication (`mulSchoolbook`) -/

/-- Inner multiply-accumulate row: adds `a_i * b[j..b.size) * B^i + carry * B^(i+j)`
into `acc` in place (`@borrowed b`, `@unique acc`). -/
def mulAddRow (a_i : UInt64) (b : Array UInt64) (i j : Nat) (carry : UInt64)
    (acc : Array UInt64) : Array UInt64 :=
  if h : j < b.size then
    let (lo, carry') := mulAddCarry64 a_i b[j] (getLimb acc (i + j)) carry
    mulAddRow a_i b i (j + 1) carry' (setLimb acc (i + j) lo)
  else
    setLimb acc (i + b.size) carry
termination_by b.size - j

/-- Outer loop of schoolbook multiplication (`@borrowed a`, `@borrowed b`, `@unique acc`). -/
def mulOuterLoop (a b : Array UInt64) (i : Nat) (acc : Array UInt64) : Array UInt64 :=
  if h : i < a.size then
    let acc' := mulAddRow a[i] b i 0 0 acc
    mulOuterLoop a b (i + 1) acc'
  else
    acc
termination_by a.size - i

/-- Schoolbook `O(m·n)` multiplication (`@borrowed a`, `@borrowed b`). -/
def mulSchoolbook (a b : Array UInt64) : Array UInt64 :=
  if a.size == 0 || b.size == 0 then #[]
  else normalize (mulOuterLoop a b 0 (mkZeros (a.size + b.size)))

/-! ### Dedicated Squaring (`sqrSchoolbook`) -/

/-- Accumulate off-diagonal products `a_i * a[j..a.size)` into `acc` (`@borrowed a`, `@unique acc`). -/
def sqrOffRow (a : Array UInt64) (a_i : UInt64) (i j : Nat) (carry : UInt64)
    (acc : Array UInt64) : Array UInt64 :=
  if h : j < a.size then
    let (lo, carry') := mulAddCarry64 a_i a[j] (getLimb acc (i + j)) carry
    sqrOffRow a a_i i (j + 1) carry' (setLimb acc (i + j) lo)
  else
    setLimb acc (i + a.size) carry
termination_by a.size - j

/-- Outer loop for off-diagonal terms `∑_{i < j} a[i] * a[j] * B^(i+j)` (`@borrowed a`, `@unique acc`). -/
def sqrOffOuter (a : Array UInt64) (i : Nat) (acc : Array UInt64) : Array UInt64 :=
  if h : i < a.size then
    let acc' := sqrOffRow a a[i] i (i + 1) 0 acc
    sqrOffOuter a (i + 1) acc'
  else
    acc
termination_by a.size - i

/-- Double a limb array in place using `addCarry64 v v carry` (`@unique acc`). -/
def doubleInPlaceLoop (acc : Array UInt64) (i : Nat) (carry : Bool) : Array UInt64 :=
  if h : i < acc.size then
    let v := acc[i]
    let (lo, c') := addCarry64 v v carry
    have : (acc.set i lo).size - (i + 1) < acc.size - i := by simp; omega
    doubleInPlaceLoop (acc.set i lo) (i + 1) c'
  else
    acc
termination_by acc.size - i

/-- Add diagonal squares `∑_{i < a.size} a[i]^2 * B^(2*i)` into `acc` in place
(`@borrowed a`, `@unique acc`). -/
def sqrAddDiagLoop (a : Array UInt64) (i : Nat) (carry : Bool)
    (acc : Array UInt64) : Array UInt64 :=
  if h : i < a.size then
    let ai := a[i]
    let (lo, hi) := mulWide64 ai ai
    let (s0, c0) := addCarry64 (getLimb acc (2 * i)) lo carry
    let (s1, c1) := addCarry64 (getLimb acc (2 * i + 1)) hi c0
    let acc1 := setLimb acc (2 * i) s0
    let acc2 := setLimb acc1 (2 * i + 1) s1
    sqrAddDiagLoop a (i + 1) c1 acc2
  else
    acc
termination_by a.size - i

/-- Dedicated schoolbook squaring (`@borrowed a`). -/
def sqrSchoolbook (a : Array UInt64) : Array UInt64 :=
  if a.size == 0 then #[]
  else
    let acc0 := mkZeros (2 * a.size)
    let acc1 := sqrOffOuter a 0 acc0
    let acc2 := doubleInPlaceLoop acc1 0 false
    let acc3 := sqrAddDiagLoop a 0 false acc2
    normalize acc3

/-! ### Karatsuba Multiplication & Squaring (`K = 32` limbs) -/

/-- Karatsuba multiplication loop with structural recursion on `fuel`
(threshold `karatsubaThreshold = 32` limbs; `@borrowed a`, `@borrowed b`). -/
def mulKaratsubaLoop (a b : Array UInt64) : Nat → Array UInt64
  | 0 => mulSchoolbook a b
  | fuel + 1 =>
    if a.size < karatsubaThreshold || b.size < karatsubaThreshold then
      mulSchoolbook a b
    else
      let n := if a.size ≤ b.size then b.size else a.size
      let m := n / 2
      let a0 := normalize (slice a 0 m)
      let a1 := normalize (slice a m a.size)
      let b0 := normalize (slice b 0 m)
      let b1 := normalize (slice b m b.size)
      let sA := add a0 a1
      let sB := add b0 b1
      let z0 := mulKaratsubaLoop a0 b0 fuel
      let z2 := mulKaratsubaLoop a1 b1 fuel
      let z1Full := mulKaratsubaLoop sA sB fuel
      karatsubaCombine z0 z2 z1Full m (a.size + b.size)

/-- Karatsuba multiplication with threshold `karatsubaThreshold = 32` limbs (`@borrowed a`, `@borrowed b`). -/
def mulKaratsuba (a b : Array UInt64) : Array UInt64 :=
  mulKaratsubaLoop a b (if a.size ≤ b.size then b.size else a.size)

/-- Karatsuba squaring loop with structural recursion on `fuel` (`@borrowed a`). -/
def sqrKaratsubaLoop (a : Array UInt64) : Nat → Array UInt64
  | 0 => sqrSchoolbook a
  | fuel + 1 =>
    if a.size < karatsubaThreshold then
      sqrSchoolbook a
    else
      let m := a.size / 2
      let a0 := normalize (slice a 0 m)
      let a1 := normalize (slice a m a.size)
      let sA := add a0 a1
      let z0 := sqrKaratsubaLoop a0 fuel
      let z2 := sqrKaratsubaLoop a1 fuel
      let z1Full := sqrKaratsubaLoop sA fuel
      karatsubaCombine z0 z2 z1Full m (2 * a.size)

/-- Karatsuba squaring with threshold `karatsubaThreshold = 32` limbs (`@borrowed a`). -/
def sqrKaratsuba (a : Array UInt64) : Array UInt64 :=
  sqrKaratsubaLoop a a.size

/-! ### Toom-Cook 3-Way Multiplication & Squaring (`T = 96` limbs) -/

/-- Balanced Toom-Cook 3-way multiplication loop (`O(n^1.465)`) over `{0, 1, -1, 2, ∞}`
with structural recursion on `fuel` and unbalanced 2-way splitting, delegating below
`toom3Threshold` to recursive `mulKaratsubaLoop` (keeping ANF globals lean). -/
def mulToom3Loop (a b : Array UInt64) : Nat → Array UInt64
  | 0 => mulKaratsuba a b
  | fuel + 1 =>
    if a.size < toom3Threshold || b.size < toom3Threshold then
      mulKaratsuba a b
    else
      let (x, y) := if a.size < b.size then (b, a) else (a, b)
      let n := x.size
      let m := n / 2
      if y.size ≤ m then
        let x0 := normalize (slice x 0 m)
        let x1 := normalize (slice x m n)
        let z0 := mulToom3Loop x0 y fuel
        let z1 := mulToom3Loop x1 y fuel
        let acc0 := copyIntoZeros z0 (n + y.size)
        normalize (addAtInPlace acc0 z1 m)
      else
        let k := (n + 2) / 3
        let (x0, x2, p1, pm1Neg, pm1, p2) := toom3EvalLoop x k #[] #[] #[] 3
        let (y0, y2, q1, qm1Neg, qm1, q2) := toom3EvalLoop y k #[] #[] #[] 3
        let r0   := mulToom3Loop x0 y0 fuel
        let r1   := mulToom3Loop p1 q1 fuel
        let rm1  := mulToom3Loop pm1 qm1 fuel
        let r2   := mulToom3Loop p2 q2 fuel
        let rInf := mulToom3Loop x2 y2 fuel
        toom3Interp r0 r1 rm1 r2 rInf (pm1Neg != qm1Neg) k (n + y.size)

/-- Balanced Toom-Cook 3-way multiplication (`O(n^1.465)`), falling back to `mulKaratsuba`
below `toom3Threshold` (`@borrowed a`, `@borrowed b`). -/
def mulToom3 (a b : Array UInt64) : Array UInt64 :=
  mulToom3Loop a b (if a.size ≤ b.size then b.size else a.size)

/-- Dedicated Toom-Cook 3-way squaring loop (`O(n^1.465)`) with structural recursion on
`fuel`, delegating below `toom3Threshold` to recursive `sqrKaratsubaLoop` (`@borrowed a`). -/
def sqrToom3Loop (a : Array UInt64) : Nat → Array UInt64
  | 0 => sqrKaratsuba a
  | fuel + 1 =>
    if a.size < toom3Threshold then
      sqrKaratsuba a
    else
      let k := (a.size + 2) / 3
      let (a0, a2, p1, _, pm1, p2) := toom3EvalLoop a k #[] #[] #[] 3
      let r0   := sqrToom3Loop a0 fuel
      let r1   := sqrToom3Loop p1 fuel
      let rm1  := sqrToom3Loop pm1 fuel
      let r2   := sqrToom3Loop p2 fuel
      let rInf := sqrToom3Loop a2 fuel
      toom3Interp r0 r1 rm1 r2 rInf false k (2 * a.size)

/-- Dedicated Toom-Cook 3-way squaring (`O(n^1.465)`), falling back to `sqrKaratsuba`
below `toom3Threshold` (`@borrowed a`). -/
def sqrToom3 (a : Array UInt64) : Array UInt64 :=
  sqrToom3Loop a a.size

/-- Primary multi-precision multiplication: routes `a == b` (`≥ 16` limbs) to dedicated
`sqrToom3`, otherwise schoolbook → Karatsuba (`≥ 32`) → Toom-3 (`≥ 96`). -/
def mul (a b : Array UInt64) : Array UInt64 :=
  if a.size == b.size && a.size ≥ 16 && beq a b then sqrToom3 a
  else mulToom3 a b

/-- Primary multi-precision squaring: schoolbook → Karatsuba (`≥ 32`) → Toom-3 (`≥ 96`). -/
@[inline] def sqr (a : Array UInt64) : Array UInt64 :=
  sqrToom3 a

/-! ### Left-to-Right Binary Exponentiation (`pow`) -/

/-- Tail-recursive bit-length helper for small `Nat` exponents (`n < 2^63` ⇒ `≤ 63`). -/
def natBitLenLoop (n acc : Nat) : Nat :=
  if h : n = 0 then acc
  else
    have : n >>> 1 < n := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
    natBitLenLoop (n >>> 1) (acc + 1)
termination_by n

/-- Bit length of `n`: `0` if `n = 0`, else the unique `k` with `2^(k-1) ≤ n < 2^k`. -/
def natBitLen (n : Nat) : Nat :=
  natBitLenLoop n 0

/-- Left-to-right binary squaring loop processing bits `i - 1` down to `0` (`@borrowed base`). -/
def powLoop (base : Array UInt64) (exp : Nat) : Nat → Array UInt64 → Array UInt64
  | 0, acc => acc
  | i + 1, acc =>
    let sq := sqr acc
    let next := if ((exp >>> i) &&& 1) == 1 then mul sq base else sq
    powLoop base exp i next

/-- Multi-precision exponentiation by left-to-right binary squaring (`@borrowed base`). -/
def pow (base : Array UInt64) (exp : Nat) : Array UInt64 :=
  if exp == 0 then one
  else
    let b := normalize base
    if b.size == 0 then zero
    else if b.size == 1 && getLimb b 0 == 1 then one
    else
      let bits := natBitLen exp
      powLoop b exp (bits - 1) b

end IxCC.BigNat
