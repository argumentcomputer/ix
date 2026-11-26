import IxCC.BigNat.LimbOps

/-! # BigNat Representation and Canonical Normal Form (`IxCC.BigNat.Basic`)

Little-endian multi-precision unsigned integer representation over `Array UInt64`,
together with its canonical normal-form invariant `WF`, mathematical denotation
`toNat`, in-place normalization `normalize`, and boundary conversions (`ofUInt64`,
`ofSmall`, `ofNat`, `toSmall?`).

## Representation & Ownership Contract

- **Representation:** Little-endian base-`2^64` limb array `xs : Array UInt64`,
  representing `∑_{i < xs.size} xs[i].toNat * (2^64)^i`. Zero is `#[]`.
- **Normal form (`WF`):** `xs.size = 0 ∨ xs[xs.size - 1] ≠ 0` (no trailing zero limbs).
- **Bootstrap compilability:** All runtime routines (`zero`, `one`, `isZero`,
  `getLimb`, `setLimb`, `mkZeros`, `slice`, `padZeros`, `normalize`, `ofUInt64`,
  `ofSmall`, `toSmall?`) are monomorphic, first-order, tail-recursive, and never
  construct or manipulate `Nat` values `≥ 2^63`. `toNat` and `toNatPrefix` are
  specification functions (proof/test only).
- **Ownership contract (for Wave 3 `@unique` / `@borrowed` compilation):**
  - `normalize (@unique xs : Array UInt64) : Array UInt64` — trims trailing zeros in place via `Array.pop`.
  - `setLimb (@unique xs : Array UInt64) (i : Nat) (v : UInt64) : Array UInt64` — updates in place via `Array.set`.
  - `padZeros (@unique xs : Array UInt64) (target : Nat) : Array UInt64` — extends in place via `Array.push`.
  - `getLimb`, `isZero`, `slice`, `toSmall?` — `@borrowed xs`.

## References

- Donald E. Knuth, *The Art of Computer Programming*, Vol. 2, §4.3.1 (Positional radix-`b` representation).
- Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone, *Handbook of Applied Cryptography*, Ch. 14 (§14.2.1).
- Richard P. Brent and Paul Zimmermann, *Modern Computer Arithmetic*, §1.2.
- `IxCC/docs/bignum-design.md` (Representation, Normal form, Promotion and demotion).
-/

namespace IxCC.BigNat

/-- Canonical representation of `0`. -/
def zero : Array UInt64 := #[]

/-- Canonical representation of `1`. -/
def one : Array UInt64 := #[1]

/-- Test whether a canonical `BigNat` is zero (`@borrowed xs`). -/
@[inline] def isZero (xs : Array UInt64) : Bool := xs.size == 0

/-- Total, bounds-safe limb read returning `0` past the end (`@borrowed xs`). -/
@[inline] def getLimb (xs : Array UInt64) (i : Nat) : UInt64 :=
  if h : i < xs.size then xs[i] else 0

/-- Total, bounds-safe in-place limb write (`@unique xs`). -/
@[inline] def setLimb (xs : Array UInt64) (i : Nat) (v : UInt64) : Array UInt64 :=
  if h : i < xs.size then xs.set i v else xs

/-- Canonical normal-form invariant: empty array or nonzero most-significant limb. -/
def WF (xs : Array UInt64) : Prop :=
  xs.size = 0 ∨ getLimb xs (xs.size - 1) ≠ 0

/-- Specification function: value of the lowest `k` limbs of `xs` in base `2^64`.
Specification/proof only — never called by runtime routines. -/
def toNatPrefix (xs : Array UInt64) : Nat → Nat
  | 0 => 0
  | k + 1 => toNatPrefix xs k + (getLimb xs k).toNat * (2 ^ 64) ^ k

/-- Specification function: exact `Nat` value denoted by a little-endian limb array.
Specification/proof only — never called by runtime routines. -/
def toNat (xs : Array UInt64) : Nat :=
  toNatPrefix xs xs.size

/-- Tail-recursive helper building `n` zero limbs (`@unique acc`). -/
def mkZerosLoop (rem : Nat) (acc : Array UInt64) : Array UInt64 :=
  match rem with
  | 0 => acc
  | k + 1 => mkZerosLoop k (acc.push 0)

/-- Allocate an array of `n` zero limbs. -/
def mkZeros (n : Nat) : Array UInt64 :=
  mkZerosLoop n (Array.mkEmpty n)

/-- Tail-recursive helper extending `xs` with zero limbs to at least `target` limbs (`@unique xs`). -/
def padZerosLoop (rem : Nat) (xs : Array UInt64) : Array UInt64 :=
  match rem with
  | 0 => xs
  | k + 1 => padZerosLoop k (xs.push 0)

/-- Extend `xs` with trailing zeros until `xs.size ≥ target` (`@unique xs`).
Allocates a fresh zero array when `xs` is empty so empty constants are never mutated. -/
def padZeros (xs : Array UInt64) (target : Nat) : Array UInt64 :=
  if xs.size == 0 then mkZeros target
  else if xs.size < target then padZerosLoop (target - xs.size) xs else xs

/-- Tail-recursive helper copying `rem` limbs starting at `idx` (`@borrowed xs`, `@unique acc`). -/
def sliceLoop (xs : Array UInt64) (idx rem : Nat) (acc : Array UInt64) : Array UInt64 :=
  match rem with
  | 0 => acc
  | k + 1 => sliceLoop xs (idx + 1) k (acc.push (getLimb xs idx))

/-- Copy limbs `[lo, min hi xs.size)` into a fresh array (`@borrowed xs`). -/
def slice (xs : Array UInt64) (lo hi : Nat) : Array UInt64 :=
  let hi' := if hi ≤ xs.size then hi else xs.size
  if lo < hi' then
    let len := hi' - lo
    sliceLoop xs lo len (Array.mkEmpty len)
  else #[]

/-- Trim trailing zero limbs in place via `Array.pop` (`@unique xs`). -/
def normalize (xs : Array UInt64) : Array UInt64 :=
  if h : 0 < xs.size then
    if xs[xs.size - 1] == 0 then
      have : xs.pop.size < xs.size := by simp [Nat.sub_lt h Nat.one_pos]
      normalize xs.pop
    else xs
  else xs
termination_by xs.size

/-- Promote a single `UInt64` word to canonical `BigNat`. -/
@[inline] def ofUInt64 (x : UInt64) : Array UInt64 :=
  if x == 0 then #[] else #[x]

/-- Promote a small runtime `Nat` (`n < 2^63`) to canonical `BigNat`. -/
@[inline] def ofSmall (n : Nat) : Array UInt64 :=
  ofUInt64 (UInt64.ofNat n)

/-- Tail-recursive general `Nat → BigNat` conversion (specification/test helper; on
small inputs `n < 2^63`, terminates in ≤ 1 step without constructing `2^64`). -/
def ofNatLoop (n : Nat) (acc : Array UInt64) : Array UInt64 :=
  if h : n = 0 then acc
  else
    have hlt : n >>> 64 < n := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)
    ofNatLoop (n >>> 64) (acc.push (UInt64.ofNat n))
termination_by n

/-- Convert any `Nat` to its canonical `BigNat` representation (spec/test conversion). -/
def ofNat (n : Nat) : Array UInt64 :=
  ofNatLoop n #[]

/-- Demote a canonical `BigNat` to `some n` iff its value is `< 2^63`, else `none`.
Uses `(v >>> 63) == 0` so no `Nat` literal `≥ 2^63` is constructed (`@borrowed xs`). -/
def toSmall? (xs : Array UInt64) : Option Nat :=
  if h : xs.size = 0 then
    some 0
  else if xs.size == 1 then
    let v := xs[0]'(Nat.pos_of_ne_zero h)
    if (v >>> 63) == 0 then some v.toNat else none
  else
    none

/-! ### Lightweight Size Lemmas (used by downstream termination proofs) -/

@[simp] theorem size_mkEmpty (n : Nat) : (Array.mkEmpty (α := UInt64) n).size = 0 := rfl

@[simp] theorem size_setLimb (xs : Array UInt64) (i : Nat) (v : UInt64) :
    (setLimb xs i v).size = xs.size := by
  unfold setLimb
  split <;> simp

theorem size_mkZerosLoop (rem : Nat) (acc : Array UInt64) :
    (mkZerosLoop rem acc).size = acc.size + rem := by
  induction rem generalizing acc with
  | zero => simp [mkZerosLoop]
  | succ k ih =>
    simp only [mkZerosLoop, ih, Array.size_push]
    omega

@[simp] theorem size_mkZeros (n : Nat) : (mkZeros n).size = n := by
  simp [mkZeros, size_mkZerosLoop]

theorem size_padZerosLoop (rem : Nat) (xs : Array UInt64) :
    (padZerosLoop rem xs).size = xs.size + rem := by
  induction rem generalizing xs with
  | zero => simp [padZerosLoop]
  | succ k ih =>
    simp only [padZerosLoop, ih, Array.size_push]
    omega

theorem size_padZeros (xs : Array UInt64) (target : Nat) :
    (padZeros xs target).size = max xs.size target := by
  unfold padZeros
  split
  · rename_i h0
    have hz : xs.size = 0 := eq_of_beq h0
    rw [size_mkZeros]; omega
  · split
    · rw [size_padZerosLoop]; omega
    · omega

theorem size_sliceLoop (xs : Array UInt64) (idx rem : Nat) (acc : Array UInt64) :
    (sliceLoop xs idx rem acc).size = acc.size + rem := by
  induction rem generalizing idx acc with
  | zero => simp [sliceLoop]
  | succ k ih =>
    simp only [sliceLoop, ih, Array.size_push]
    omega

theorem size_slice (xs : Array UInt64) (lo hi : Nat) :
    (slice xs lo hi).size = min hi xs.size - lo := by
  unfold slice
  dsimp only
  split <;> split <;> simp only [size_sliceLoop, size_mkEmpty, Array.size_empty, Nat.zero_add] <;> omega

theorem size_normalize_le (xs : Array UInt64) : (normalize xs).size ≤ xs.size := by
  induction h : xs.size generalizing xs with
  | zero =>
    unfold normalize
    simp [h]
  | succ n ih =>
    unfold normalize
    have hpos : 0 < xs.size := by omega
    simp only [hpos, ↓reduceDIte]
    split
    · have hpop : xs.pop.size = n := by simp [h]
      have := ih xs.pop hpop
      omega
    · omega

end IxCC.BigNat
