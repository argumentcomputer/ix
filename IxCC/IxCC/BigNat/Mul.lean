import IxCC.BigNat.Linear

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

/-- Karatsuba multiplication with threshold `karatsubaThreshold = 32` limbs (`@borrowed a`, `@borrowed b`). -/
def mulKaratsuba (a b : Array UInt64) : Array UInt64 :=
  if hbase : a.size < karatsubaThreshold ∨ b.size < karatsubaThreshold then
    mulSchoolbook a b
  else
    let n := max a.size b.size
    let m := n / 2
    let a0 := normalize (slice a 0 m)
    let a1 := normalize (slice a m a.size)
    let b0 := normalize (slice b 0 m)
    let b1 := normalize (slice b m b.size)
    let sA := add a0 a1
    let sB := add b0 b1
    have hge : karatsubaThreshold ≤ a.size ∧ karatsubaThreshold ≤ b.size := by
      exact ⟨Nat.not_lt.mp (fun h => hbase (Or.inl h)),
             Nat.not_lt.mp (fun h => hbase (Or.inr h))⟩
    have ha0 : a0.size ≤ m := by
      have h1 := size_normalize_le (slice a 0 m)
      have h2 := size_slice a 0 m
      change (normalize (slice a 0 m)).size ≤ m; omega
    have ha1 : a1.size ≤ n - m := by
      have h1 := size_normalize_le (slice a m a.size)
      have h2 := size_slice a m a.size
      change (normalize (slice a m a.size)).size ≤ n - m; omega
    have hb0 : b0.size ≤ m := by
      have h1 := size_normalize_le (slice b 0 m)
      have h2 := size_slice b 0 m
      change (normalize (slice b 0 m)).size ≤ m; omega
    have hb1 : b1.size ≤ n - m := by
      have h1 := size_normalize_le (slice b m b.size)
      have h2 := size_slice b m b.size
      change (normalize (slice b m b.size)).size ≤ n - m; omega
    have hsA : sA.size ≤ max a0.size a1.size + 1 := size_add_le a0 a1
    have hsB : sB.size ≤ max b0.size b1.size + 1 := size_add_le b0 b1
    have hlt0 : max a0.size b0.size < max a.size b.size := by
      unfold karatsubaThreshold at hge; omega
    have hlt1 : max a1.size b1.size < max a.size b.size := by
      unfold karatsubaThreshold at hge; omega
    have hltS : max sA.size sB.size < max a.size b.size := by
      unfold karatsubaThreshold at hge; omega
    let z0 := mulKaratsuba a0 b0
    let z2 := mulKaratsuba a1 b1
    let z1Full := mulKaratsuba sA sB
    let z1 := subRaw z1Full (add z0 z2)
    add (add z0 (shiftLimbs z1 m)) (shiftLimbs z2 (2 * m))
termination_by max a.size b.size

/-- Primary multi-precision multiplication: schoolbook below 32 limbs, Karatsuba at `≥ 32` limbs. -/
@[inline] def mul (a b : Array UInt64) : Array UInt64 :=
  mulKaratsuba a b

/-- Karatsuba squaring with threshold `karatsubaThreshold = 32` limbs (`@borrowed a`). -/
def sqrKaratsuba (a : Array UInt64) : Array UInt64 :=
  if hbase : a.size < karatsubaThreshold then
    sqrSchoolbook a
  else
    let m := a.size / 2
    let a0 := normalize (slice a 0 m)
    let a1 := normalize (slice a m a.size)
    let sA := add a0 a1
    have hge : karatsubaThreshold ≤ a.size := Nat.not_lt.mp hbase
    have ha0 : a0.size ≤ m := by
      have h1 := size_normalize_le (slice a 0 m)
      have h2 := size_slice a 0 m
      change (normalize (slice a 0 m)).size ≤ m; omega
    have ha1 : a1.size ≤ a.size - m := by
      have h1 := size_normalize_le (slice a m a.size)
      have h2 := size_slice a m a.size
      change (normalize (slice a m a.size)).size ≤ a.size - m; omega
    have hsA : sA.size ≤ max a0.size a1.size + 1 := size_add_le a0 a1
    have hlt0 : a0.size < a.size := by unfold karatsubaThreshold at hge; omega
    have hlt1 : a1.size < a.size := by unfold karatsubaThreshold at hge; omega
    have hltS : sA.size < a.size := by unfold karatsubaThreshold at hge; omega
    let z0 := sqrKaratsuba a0
    let z2 := sqrKaratsuba a1
    let z1Full := sqrKaratsuba sA
    let z1 := subRaw z1Full (add z0 z2)
    add (add z0 (shiftLimbs z1 m)) (shiftLimbs z2 (2 * m))
termination_by a.size

/-- Primary multi-precision squaring: dedicated schoolbook below 32 limbs, Karatsuba at `≥ 32` limbs. -/
@[inline] def sqr (a : Array UInt64) : Array UInt64 :=
  sqrKaratsuba a

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
