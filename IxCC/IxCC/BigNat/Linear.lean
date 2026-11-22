import IxCC.BigNat.Basic

/-! # Linear-Time BigNat Operations (`IxCC.BigNat.Linear`)

Comparison, addition, truncating subtraction, predecessor, bitwise logic,
bit/limb shifts, and base-2 logarithm on canonical little-endian `Array UInt64`.

## Ownership & Bootstrap Contract

- **Bootstrap compilability:** Monomorphic, first-order, tail-recursive loops
  over `Array UInt64` using exclusively `LimbOps` (`addCarry64`, `subBorrow64`,
  `clz64`), `UInt64` word ops, and small `Nat` indices `< 2^63`. Zero `Nat`
  literals `≥ 2^63`, zero `toNat` calls in runtime code.
- **Ownership contract (for Wave 3 `@unique` / `@borrowed` compilation):**
  - `cmp`, `beq`, `ble`, `blt`, `add`, `sub`, `subRaw`, `land`, `lor`, `xor`,
    `shiftLeft`, `shiftRight`, `shiftLimbs`, `log2` — `@borrowed` operands;
    freshly allocated output accumulators are threaded `@unique` through
    tail-recursive loops.
  - `pred (@unique a : Array UInt64) : Array UInt64` — updates limbs in place
    via `Array.set` / `Array.pop`.

## References

- Donald E. Knuth, *The Art of Computer Programming*, Vol. 2, §4.3.1
  (Algorithm A: Addition of nonnegative integers; Algorithm S: Subtraction of
  nonnegative integers).
- Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone, *Handbook of
  Applied Cryptography*, Ch. 14 (Algorithm 14.7 multi-precision addition;
  Algorithm 14.9 multi-precision subtraction).
- Richard P. Brent and Paul Zimmermann, *Modern Computer Arithmetic*, §1.3.
-/

namespace IxCC.BigNat

/-! ### Comparison (`cmp`, `beq`, `ble`, `blt`) -/

/-- Compare limbs `k - 1` down to `0` lexicographically (`@borrowed a`, `@borrowed b`). -/
def cmpLoop (a b : Array UInt64) : Nat → Ordering
  | 0 => .eq
  | k + 1 =>
    let va := getLimb a k
    let vb := getLimb b k
    if va < vb then .lt
    else if va > vb then .gt
    else cmpLoop a b k

/-- Compare two canonical (`WF`) `BigNat`s (`@borrowed a`, `@borrowed b`). -/
def cmp (a b : Array UInt64) : Ordering :=
  if a.size < b.size then .lt
  else if a.size > b.size then .gt
  else cmpLoop a b a.size

/-- Canonical equality (`@borrowed a`, `@borrowed b`). -/
@[inline] def beq (a b : Array UInt64) : Bool :=
  match cmp a b with
  | .eq => true
  | _ => false

/-- Canonical `≤` (`@borrowed a`, `@borrowed b`). -/
@[inline] def ble (a b : Array UInt64) : Bool :=
  match cmp a b with
  | .gt => false
  | _ => true

/-- Canonical `<` (`@borrowed a`, `@borrowed b`). -/
@[inline] def blt (a b : Array UInt64) : Bool :=
  match cmp a b with
  | .lt => true
  | _ => false

/-! ### Addition (`add`) -/

/-- Tail-recursive carry-propagation loop over `n` limbs (`@borrowed a`, `@borrowed b`, `@unique acc`). -/
def addLoop (a b : Array UInt64) (n i : Nat) (carry : Bool) (acc : Array UInt64) : Array UInt64 :=
  if _h : i < n then
    let (lo, c') := addCarry64 (getLimb a i) (getLimb b i) carry
    addLoop a b n (i + 1) c' (acc.push lo)
  else
    if carry then acc.push 1 else acc
termination_by n - i

/-- Multi-precision addition (`toNat (add a b) = toNat a + toNat b`, always `WF`). -/
def add (a b : Array UInt64) : Array UInt64 :=
  let n := if a.size ≤ b.size then b.size else a.size
  normalize (addLoop a b n 0 false (Array.mkEmpty (n + 1)))

/-! ### Truncating Subtraction (`subRaw`, `sub`) and Predecessor (`pred`) -/

/-- Tail-recursive borrow-propagation loop over `n` limbs (`@borrowed a`, `@borrowed b`, `@unique acc`). -/
def subLoop (a b : Array UInt64) (n i : Nat) (borrow : Bool) (acc : Array UInt64) :
    Array UInt64 × Bool :=
  if _h : i < n then
    let (lo, b') := subBorrow64 (getLimb a i) (getLimb b i) borrow
    subLoop a b n (i + 1) b' (acc.push lo)
  else
    (acc, borrow)
termination_by n - i

/-- Unconditional truncating subtraction valid on arbitrary (even non-`WF`) limb arrays. -/
def subRaw (a b : Array UInt64) : Array UInt64 :=
  let n := if a.size ≤ b.size then b.size else a.size
  let (acc, borrow) := subLoop a b n 0 false (Array.mkEmpty n)
  if borrow then #[] else normalize acc

/-- Truncating subtraction on canonical (`WF`) `BigNat`s, with zero-allocation fast
exit when `a ≤ b` (`@borrowed a`, `@borrowed b`). -/
def sub (a b : Array UInt64) : Array UInt64 :=
  match cmp a b with
  | .lt => #[]
  | .eq => #[]
  | .gt =>
    let (acc, borrow) := subLoop a b a.size 0 false (Array.mkEmpty a.size)
    if borrow then #[] else normalize acc

/-- In-place borrow chain for `pred` (`@unique a`). -/
def predLoop (a : Array UInt64) (i : Nat) : Array UInt64 :=
  if h : i < a.size then
    let v := a[i]
    if v == 0 then
      have : (a.set i maxWord64).size - (i + 1) < a.size - i := by simp; omega
      predLoop (a.set i maxWord64) (i + 1)
    else
      normalize (a.set i (v - 1))
  else
    #[]
termination_by a.size - i

/-- Truncating predecessor (`pred 0 = 0`, in-place on `@unique a`). -/
def pred (a : Array UInt64) : Array UInt64 :=
  if a.size == 0 then #[] else predLoop a 0

/-! ### Bitwise Operations (`land`, `lor`, `xor`) -/

def landLoop (a b : Array UInt64) (n i : Nat) (acc : Array UInt64) : Array UInt64 :=
  if _h : i < n then
    landLoop a b n (i + 1) (acc.push (getLimb a i &&& getLimb b i))
  else acc
termination_by n - i

/-- Bitwise AND (`@borrowed a`, `@borrowed b`). -/
def land (a b : Array UInt64) : Array UInt64 :=
  let n := if a.size ≤ b.size then a.size else b.size
  normalize (landLoop a b n 0 (Array.mkEmpty n))

def lorLoop (a b : Array UInt64) (n i : Nat) (acc : Array UInt64) : Array UInt64 :=
  if _h : i < n then
    lorLoop a b n (i + 1) (acc.push (getLimb a i ||| getLimb b i))
  else acc
termination_by n - i

/-- Bitwise OR (`@borrowed a`, `@borrowed b`). -/
def lor (a b : Array UInt64) : Array UInt64 :=
  let n := if a.size ≤ b.size then b.size else a.size
  normalize (lorLoop a b n 0 (Array.mkEmpty n))

def xorLoop (a b : Array UInt64) (n i : Nat) (acc : Array UInt64) : Array UInt64 :=
  if _h : i < n then
    xorLoop a b n (i + 1) (acc.push (getLimb a i ^^^ getLimb b i))
  else acc
termination_by n - i

/-- Bitwise XOR (`@borrowed a`, `@borrowed b`). -/
def xor (a b : Array UInt64) : Array UInt64 :=
  let n := if a.size ≤ b.size then b.size else a.size
  normalize (xorLoop a b n 0 (Array.mkEmpty n))

/-! ### Shifts (`shiftLimbs`, `shiftLeft`, `shiftRight`) and `log2` -/

/-- Copy `a[0 .. a.size)` onto the end of `acc` (`@borrowed a`, `@unique acc`). -/
def copyAppendLoop (a : Array UInt64) (i : Nat) (acc : Array UInt64) : Array UInt64 :=
  if h : i < a.size then
    copyAppendLoop a (i + 1) (acc.push a[i])
  else acc
termination_by a.size - i

/-- Multiply by `(2^64)^k` by prepending `k` zero limbs (`@borrowed a`). -/
def shiftLimbs (a : Array UInt64) (k : Nat) : Array UInt64 :=
  let a' := normalize a
  if a'.size == 0 then #[]
  else if k == 0 then a'
  else
    let acc := mkZerosLoop k (Array.mkEmpty (k + a'.size))
    normalize (copyAppendLoop a' 0 acc)

/-- Shift left by `0 < bitShift < 64` bits (`b = UInt64.ofNat bitShift`, `invB = 64 - b`). -/
def shiftLeftBitLoop (a : Array UInt64) (b invB : UInt64) (i : Nat)
    (carry : UInt64) (acc : Array UInt64) : Array UInt64 :=
  if h : i < a.size then
    let v := a[i]
    let out := (v <<< b) ||| carry
    let carry' := v >>> invB
    shiftLeftBitLoop a b invB (i + 1) carry' (acc.push out)
  else
    if carry == 0 then acc else acc.push carry
termination_by a.size - i

/-- Left shift by `s` bits (`toNat (shiftLeft a s) = toNat a <<< s`, `@borrowed a`). -/
def shiftLeft (a : Array UInt64) (s : Nat) : Array UInt64 :=
  let a' := normalize a
  if a'.size == 0 then #[]
  else if s == 0 then a'
  else
    let wordShift := s / 64
    let bitShift := s % 64
    let acc := mkZerosLoop wordShift (Array.mkEmpty (wordShift + a'.size + 1))
    if bitShift == 0 then
      normalize (copyAppendLoop a' 0 acc)
    else
      let b := UInt64.ofNat bitShift
      let invB := (64 : UInt64) - b
      normalize (shiftLeftBitLoop a' b invB 0 0 acc)

/-- Copy limbs `a[wordShift + i]` for `i < outLen` (`@borrowed a`, `@unique acc`). -/
def shiftRightWordLoop (a : Array UInt64) (wordShift outLen i : Nat)
    (acc : Array UInt64) : Array UInt64 :=
  if _h : i < outLen then
    shiftRightWordLoop a wordShift outLen (i + 1) (acc.push (getLimb a (wordShift + i)))
  else acc
termination_by outLen - i

/-- Shift right by `wordShift * 64 + bitShift` with `0 < bitShift < 64`. -/
def shiftRightBitLoop (a : Array UInt64) (wordShift outLen : Nat) (b invB : UInt64)
    (i : Nat) (acc : Array UInt64) : Array UInt64 :=
  if _h : i < outLen then
    let lo := getLimb a (wordShift + i) >>> b
    let hi := getLimb a (wordShift + i + 1) <<< invB
    shiftRightBitLoop a wordShift outLen b invB (i + 1) (acc.push (lo ||| hi))
  else acc
termination_by outLen - i

/-- Right shift by `s` bits (`toNat (shiftRight a s) = toNat a >>> s`, `@borrowed a`). -/
def shiftRight (a : Array UInt64) (s : Nat) : Array UInt64 :=
  if s == 0 then normalize a
  else
    let wordShift := s / 64
    let bitShift := s % 64
    if a.size ≤ wordShift then #[]
    else
      let outLen := a.size - wordShift
      if bitShift == 0 then
        normalize (shiftRightWordLoop a wordShift outLen 0 (Array.mkEmpty outLen))
      else
        let b := UInt64.ofNat bitShift
        let invB := (64 : UInt64) - b
        normalize (shiftRightBitLoop a wordShift outLen b invB 0 (Array.mkEmpty outLen))

/-- Base-2 floor logarithm matching `Nat.log2` (`log2 0 = 0`, `@borrowed a`). -/
def log2 (a : Array UInt64) : Nat :=
  if h : a.size = 0 then 0
  else
    let top := a[a.size - 1]'(Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.one_pos)
    let lz := (clz64 top).toNat
    (a.size - 1) * 64 + (63 - lz)

/-! ### Lightweight Size Lemmas (used by Karatsuba termination in `Mul.lean`) -/

theorem size_addLoop_le (a b : Array UInt64) (n i : Nat) (carry : Bool) (acc : Array UInt64) :
    (addLoop a b n i carry acc).size ≤ acc.size + (n - i) + 1 := by
  induction h : n - i generalizing i carry acc with
  | zero =>
    unfold addLoop
    have hge : ¬ i < n := by omega
    simp only [hge, ↓reduceDIte]
    cases carry <;> simp <;> omega
  | succ d ih =>
    unfold addLoop
    have hlt : i < n := by omega
    simp only [hlt, ↓reduceDIte]
    have hstep : n - (i + 1) = d := by omega
    have := ih (i + 1) (addCarry64 (getLimb a i) (getLimb b i) carry).2
      (acc.push (addCarry64 (getLimb a i) (getLimb b i) carry).1) hstep
    simp only [Array.size_push] at this
    omega

theorem size_add_le (a b : Array UInt64) :
    (add a b).size ≤ max a.size b.size + 1 := by
  unfold add
  dsimp only
  let n := if a.size ≤ b.size then b.size else a.size
  have h1 := size_normalize_le (addLoop a b n 0 false (Array.mkEmpty (n + 1)))
  have h2 := size_addLoop_le a b n 0 false (Array.mkEmpty (n + 1))
  simp only [size_mkEmpty, Nat.zero_add, Nat.sub_zero] at h2
  have h3 : n = max a.size b.size := by dsimp [n]; split <;> omega
  exact Nat.le_trans h1 (by omega)

end IxCC.BigNat
