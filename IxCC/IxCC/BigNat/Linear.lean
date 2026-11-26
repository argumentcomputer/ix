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

/-- Fast small-bit left shift (`0 ≤ s < 64`, zero `wordShift`/`div`/`mod`, `@borrowed a`). -/
def shiftLeftSmall (a : Array UInt64) (s : Nat) : Array UInt64 :=
  if s == 0 then normalize a
  else
    let b := UInt64.ofNat s
    let invB := (64 : UInt64) - b
    normalize (shiftLeftBitLoop a b invB 0 0 (Array.mkEmpty (a.size + 1)))

/-- Fast small-bit right shift (`0 ≤ s < 64`, zero `wordShift`/`div`/`mod`, `@borrowed a`). -/
def shiftRightSmall (a : Array UInt64) (s : Nat) : Array UInt64 :=
  if s == 0 then normalize a
  else
    let b := UInt64.ofNat s
    let invB := (64 : UInt64) - b
    normalize (shiftRightBitLoop a 0 a.size b invB 0 (Array.mkEmpty a.size))

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

/-! ### Stage 2 In-Place Unique-COW Limb Operations & Fast 1-Bit Shifts -/

/-- Copy `src` into a freshly allocated array of `max src.size target` limbs, zero-padded.
Always allocates a fresh unique buffer of exact final capacity (`@borrowed src`). -/
def copyIntoZeros (src : Array UInt64) (target : Nat) : Array UInt64 :=
  let sz := if src.size < target then target else src.size
  let acc := copyAppendLoop src 0 (Array.mkEmpty sz)
  if src.size < target then padZerosLoop (target - src.size) acc else acc

/-- Propagate carry `1` starting at index `idx` into `@unique acc` in place
(structural recursion on `rem = acc.size - idx`). -/
def addCarryAtLoop (acc : Array UInt64) (idx : Nat) : Nat → Array UInt64
  | 0 => acc.push 1
  | rem + 1 =>
    let v := getLimb acc idx + 1
    if v == 0 then addCarryAtLoop (setLimb acc idx 0) (idx + 1) rem
    else setLimb acc idx v

/-- Add `b[i .. i + rem)` into `@unique acc` starting at `off + i` in place. -/
def addAtLoop (acc b : Array UInt64) (off i : Nat) (carry : Bool) : Nat → Array UInt64
  | 0 => if carry then addCarryAtLoop acc (off + i) (acc.size - (off + i)) else acc
  | rem + 1 =>
    let idx := off + i
    let (lo, c') := addCarry64 (getLimb acc idx) (getLimb b i) carry
    addAtLoop (setLimb acc idx lo) b off (i + 1) c' rem

/-- In-place shifted addition: computes `acc + b * (2^64)^off`, mutating `@unique acc`
in place (padding only if `acc.size < off + b.size`; caller calls `normalize` once). -/
def addAtInPlace (acc b : Array UInt64) (off : Nat) : Array UInt64 :=
  if b.size == 0 then acc
  else
    let acc0 := padZeros acc (off + b.size)
    addAtLoop acc0 b off 0 false b.size

/-- In-place addition `acc + b`, mutating `@unique acc` in place (unnormalized). -/
@[inline] def addInPlace (acc b : Array UInt64) : Array UInt64 :=
  addAtInPlace acc b 0

/-- Propagate borrow `1` starting at index `idx` into `@unique acc` in place
(structural recursion on `rem = acc.size - idx`). -/
def subBorrowAtLoop (acc : Array UInt64) (idx : Nat) : Nat → Array UInt64 × Bool
  | 0 => (acc, true)
  | rem + 1 =>
    let v := getLimb acc idx
    if v == 0 then subBorrowAtLoop (setLimb acc idx maxWord64) (idx + 1) rem
    else (setLimb acc idx (v - 1), false)

/-- Subtract `b[i .. i + rem)` from `@unique acc` starting at `off + i` in place. -/
def subAtLoop (acc b : Array UInt64) (off i : Nat) (borrow : Bool) : Nat → Array UInt64 × Bool
  | 0 => if borrow then subBorrowAtLoop acc (off + i) (acc.size - (off + i)) else (acc, false)
  | rem + 1 =>
    let idx := off + i
    let (lo, b') := subBorrow64 (getLimb acc idx) (getLimb b i) borrow
    subAtLoop (setLimb acc idx lo) b off (i + 1) b' rem

/-- In-place shifted subtraction: computes `acc - b * (2^64)^off`, mutating `@unique acc`
in place and returning `(res, borrowOut)`. -/
def subAtInPlace (acc b : Array UInt64) (off : Nat) : Array UInt64 × Bool :=
  if b.size == 0 then (acc, false)
  else
    let acc0 := padZeros acc (off + b.size)
    subAtLoop acc0 b off 0 false b.size

/-- In-place truncating subtraction on `@unique acc` (`toNat (subInPlace acc b) = toNat acc - toNat b`). -/
def subInPlace (acc b : Array UInt64) : Array UInt64 :=
  let (res, borrow) := subAtInPlace acc b 0
  if borrow then #[] else normalize res

/-- Fused 64-bit multiply-subtract with carry: computes `a - b * q - carry` as `(diff, nextCarry)`
with `diff + b * q + carry = a + nextCarry * 2^64` and `nextCarry < 2^64` (zero overflow since
`(2^64 - 1) + (2^64 - 1)^2 + (2^64 - 1) = 2^128 - 1 < 2^128`). -/
@[inline] def subMulCarry64 (a b q carry : UInt64) : UInt64 × UInt64 :=
  let p := mulWide64 q b
  let r1 := addCarry64 p.1 carry false
  let r2 := subBorrow64 a r1.1 false
  let c1 : UInt64 := if r1.2 then 1 else 0
  let b2 : UInt64 := if r2.2 then 1 else 0
  (r2.1, p.2 + c1 + b2)

/-- Add `m * b[i .. i + rem) * (2^64)^off` into `@unique acc` in place. -/
def addMul1AtLoop (acc b : Array UInt64) (off i : Nat) (m carry : UInt64) : Nat → Array UInt64
  | 0 =>
    if carry == 0 then acc
    else
      let idx := off + i
      if idx < acc.size then
        let (lo, c') := addCarry64 (getLimb acc idx) carry false
        let acc1 := setLimb acc idx lo
        if c' then addCarryAtLoop acc1 (idx + 1) (acc1.size - (idx + 1)) else acc1
      else acc.push carry
  | rem + 1 =>
    let idx := off + i
    let (lo, carry') := mulAddCarry64 m (getLimb b i) (getLimb acc idx) carry
    addMul1AtLoop (setLimb acc idx lo) b off (i + 1) m carry' rem

/-- In-place multiply-accumulate `acc + m * b * (2^64)^off` (`@unique acc`, `@borrowed b`). -/
def addMul1AtInPlace (acc b : Array UInt64) (m : UInt64) (off : Nat) : Array UInt64 :=
  if b.size == 0 || m == 0 then acc
  else
    let acc0 := padZeros acc (off + b.size)
    addMul1AtLoop acc0 b off 0 m 0 b.size

/-- In-place multiply-accumulate `acc + m * b` (`@unique acc`, `@borrowed b`). -/
@[inline] def addMul1InPlace (acc b : Array UInt64) (m : UInt64) : Array UInt64 :=
  addMul1AtInPlace acc b m 0

/-- Subtract `m * b[i .. i + rem) * (2^64)^off` from `@unique acc` in place, returning
`(res, borrowWord)` satisfying `toNat res + m * b * B^off = toNat acc + borrowWord * B^res.size`. -/
def subMul1AtLoop (acc b : Array UInt64) (off i : Nat) (m carry : UInt64) :
    Nat → Array UInt64 × UInt64
  | 0 =>
    if carry == 0 then (acc, 0)
    else
      let idx := off + i
      if idx < acc.size then
        let (lo, b') := subBorrow64 (getLimb acc idx) carry false
        let acc1 := setLimb acc idx lo
        if b' then
          let (acc2, bOut) := subBorrowAtLoop acc1 (idx + 1) (acc1.size - (idx + 1))
          (acc2, if bOut then 1 else 0)
        else (acc1, 0)
      else (acc, carry)
  | rem + 1 =>
    let idx := off + i
    let (diff, carry') := subMulCarry64 (getLimb acc idx) (getLimb b i) m carry
    subMul1AtLoop (setLimb acc idx diff) b off (i + 1) m carry' rem

/-- In-place multiply-subtract `acc - m * b * (2^64)^off` (`@unique acc`, `@borrowed b`),
returning `(res, borrowWord)` where `borrowWord == 0` iff no underflow occurred. -/
def subMul1AtInPlace (acc b : Array UInt64) (m : UInt64) (off : Nat) : Array UInt64 × UInt64 :=
  if b.size == 0 || m == 0 then (acc, 0)
  else
    let acc0 := padZeros acc (off + b.size)
    subMul1AtLoop acc0 b off 0 m 0 b.size

/-- In-place multiply-subtract `acc - m * b` (`@unique acc`, `@borrowed b`). -/
@[inline] def subMul1InPlace (acc b : Array UInt64) (m : UInt64) : Array UInt64 × UInt64 :=
  subMul1AtInPlace acc b m 0

/-- Fast 1-bit left shift loop (`@borrowed a`, `@unique acc`). -/
def shiftLeft1Loop (a : Array UInt64) (i : Nat) (carry : UInt64) (acc : Array UInt64) :
    Nat → Array UInt64
  | 0 => if carry == 0 then acc else acc.push carry
  | rem + 1 =>
    let v := getLimb a i
    let out := (v <<< (1 : UInt64)) ||| carry
    let carry' := v >>> (63 : UInt64)
    shiftLeft1Loop a (i + 1) carry' (acc.push out) rem

/-- Fast 1-bit left shift (`toNat (shiftLeft1 a) = toNat a * 2`, always `WF`). -/
def shiftLeft1 (a : Array UInt64) : Array UInt64 :=
  if a.size == 0 then #[]
  else normalize (shiftLeft1Loop a 0 0 (Array.mkEmpty (a.size + 1)) a.size)

/-- Fast 1-bit right shift loop (`@borrowed a`, `@unique acc`). -/
def shiftRight1Loop (a : Array UInt64) (i : Nat) (acc : Array UInt64) : Nat → Array UInt64
  | 0 => acc
  | rem + 1 =>
    let lo := getLimb a i >>> (1 : UInt64)
    let hi := getLimb a (i + 1) <<< (63 : UInt64)
    shiftRight1Loop a (i + 1) (acc.push (lo ||| hi)) rem

/-- Fast 1-bit right shift (`toNat (shiftRight1 a) = toNat a / 2`, always `WF`). -/
def shiftRight1 (a : Array UInt64) : Array UInt64 :=
  if a.size == 0 then #[]
  else normalize (shiftRight1Loop a 0 (Array.mkEmpty a.size) a.size)

/-! ### Lightweight Size Lemmas for Stage 2 In-Place Ops & 1-Bit Shifts -/

theorem size_copyAppendLoop (a : Array UInt64) (i : Nat) (acc : Array UInt64) :
    (copyAppendLoop a i acc).size = acc.size + (a.size - i) := by
  induction h : a.size - i generalizing i acc with
  | zero =>
    unfold copyAppendLoop
    have hge : ¬ i < a.size := by omega
    simp [hge]
  | succ d ih =>
    unfold copyAppendLoop
    have hlt : i < a.size := by omega
    simp only [hlt, ↓reduceDIte]
    have := ih (i + 1) (acc.push a[i]) (by omega)
    simp only [Array.size_push] at this
    omega

theorem size_copyIntoZeros (src : Array UInt64) (target : Nat) :
    (copyIntoZeros src target).size = max src.size target := by
  unfold copyIntoZeros
  dsimp only
  split
  · rw [size_padZerosLoop, size_copyAppendLoop, size_mkEmpty]; omega
  · rw [size_copyAppendLoop, size_mkEmpty]; omega

theorem size_shiftLeft1Loop_le (a : Array UInt64) (i : Nat) (carry : UInt64)
    (acc : Array UInt64) (rem : Nat) :
    (shiftLeft1Loop a i carry acc rem).size ≤ acc.size + rem + 1 := by
  induction rem generalizing i carry acc with
  | zero =>
    unfold shiftLeft1Loop
    split <;> simp <;> omega
  | succ rem ih =>
    unfold shiftLeft1Loop
    dsimp only
    have := ih (i + 1) (getLimb a i >>> (63 : UInt64)) (acc.push ((getLimb a i <<< (1 : UInt64)) ||| carry))
    simp only [Array.size_push] at this
    omega

theorem size_shiftLeft1_le (a : Array UInt64) : (shiftLeft1 a).size ≤ a.size + 1 := by
  unfold shiftLeft1
  split
  · simp
  · have h1 := size_normalize_le (shiftLeft1Loop a 0 0 (Array.mkEmpty (a.size + 1)) a.size)
    have h2 := size_shiftLeft1Loop_le a 0 0 (Array.mkEmpty (a.size + 1)) a.size
    simp only [size_mkEmpty, Nat.zero_add] at h2
    omega

theorem size_shiftRight1Loop (a : Array UInt64) (i : Nat) (acc : Array UInt64) (rem : Nat) :
    (shiftRight1Loop a i acc rem).size = acc.size + rem := by
  induction rem generalizing i acc with
  | zero => simp [shiftRight1Loop]
  | succ rem ih =>
    unfold shiftRight1Loop
    dsimp only
    rw [ih, Array.size_push]
    omega

theorem size_shiftRight1_le (a : Array UInt64) : (shiftRight1 a).size ≤ a.size := by
  unfold shiftRight1
  split
  · simp
  · have h1 := size_normalize_le (shiftRight1Loop a 0 (Array.mkEmpty a.size) a.size)
    rw [size_shiftRight1Loop, size_mkEmpty, Nat.zero_add] at h1
    exact h1

end IxCC.BigNat
