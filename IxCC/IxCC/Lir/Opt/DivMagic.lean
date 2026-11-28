import IxCC.Lir.Semantics

/-!
# Constant unsigned division and modulo strength reduction

Computes and validates exact strength reductions for unsigned division and
remainder by nonzero compile-time constants:

1. **Powers of two** (`2^k`, `0 < k < w.bits`): `udiv` → `shr k`, `urem` → `and (2^k - 1)`
   at all widths (`w8`, `w16`, `w32`, `w64`).
2. **Granlund–Montgomery magic multipliers** at `w64`:
   - **Case 1 (simple multiply-shift):** `q = mulHi(a, m) >>> s` whenever
     `2^(64 + s) ≤ d * m` and `(d * m - 2^(64 + s)) * (2^64 - 1) < 2^(64 + s)`.
     Covers `d = 3, 5, 6, 9, 10, 11, 12, 100, 1000, ..., 10^19` (including `BigNat.toDecimal`).
   - **Case 2 (add-shift multiply-high):** `hi = mulHi(a, m')`,
     `q = (((a - hi) >>> 1) + hi) >>> (s - 1)` whenever
     `2^(64 + s) ≤ d * (2^64 + m')` and
     `(d * (2^64 + m') - 2^(64 + s)) * (2^64 - 1) < 2^(64 + s)`.
     Covers the remaining divisors such as `d = 7, 13, 14, 19, 2^64 - 1`.
3. **32-bit magic multipliers** at `w32`:
   - `q = ((a &&& 0xffffffff) * m) >>> (32 + s)` without needing widening multiply.
4. **Constant remainder** `urem w a d`: `a - q * d` from any valid quotient `q`.

The boolean predicates (`isPow2`, `checkMagicSimple`, `checkMagicAddShift`,
`checkMagic32`) are the **trusted** validator checks proved sound in
`IxCC.Lir.Proof.Opt.Arith`; `magicU64` / `magicU32` are the untrusted
parameter finders.
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (Width Word)

/-- Whether `w.truncate d = 2^k` with `0 < k < w.bits`. -/
def isPow2 (w : Width) (d : Word) (k : Nat) : Bool :=
  decide (0 < k ∧ k < w.bits ∧ (w.truncate d).toNat = 2 ^ k)

/-- Exact arithmetic check for 64-bit simple multiply-shift:
`q = (mulHi a m) >>> s = a / d` for every `a : Word`. -/
def checkMagicSimple (d m : Word) (s : Nat) : Bool :=
  decide (1 < d.toNat ∧ s < 64 ∧
    2 ^ (64 + s) ≤ d.toNat * m.toNat ∧
    (d.toNat * m.toNat - 2 ^ (64 + s)) * (2 ^ 64 - 1) < 2 ^ (64 + s))

/-- Exact arithmetic check for 64-bit add-shift multiply-high:
`hi = mulHi a m'`, `q = (((a - hi) >>> 1) + hi) >>> (s - 1) = a / d` for every `a : Word`. -/
def checkMagicAddShift (d m' : Word) (s : Nat) : Bool :=
  decide (1 < d.toNat ∧ 1 ≤ s ∧ s ≤ 64 ∧
    2 ^ (64 + s) ≤ d.toNat * (2 ^ 64 + m'.toNat) ∧
    (d.toNat * (2 ^ 64 + m'.toNat) - 2 ^ (64 + s)) * (2 ^ 64 - 1) < 2 ^ (64 + s))

/-- Exact arithmetic check for 32-bit simple multiply-shift using 64-bit `mul`:
`q = ((a &&& 0xffffffff) * m) >>> (32 + s) = (w32.truncate a) / (w32.truncate d)`. -/
def checkMagic32 (d m : Word) (s : Nat) : Bool :=
  decide (1 < d.toNat ∧ d.toNat < 2 ^ 32 ∧ m.toNat ≤ 2 ^ 32 ∧ s < 32 ∧
    2 ^ (32 + s) ≤ d.toNat * m.toNat ∧
    (d.toNat * m.toNat - 2 ^ (32 + s)) * (2 ^ 32 - 1) < 2 ^ (32 + s))

/-- Exact arithmetic check for 32-bit add-shift multiply-high using 64-bit `mul`:
`u = a &&& 0xffffffff`, `hi = (u * m') >>> 32`, `q = (((u - hi) >>> 1) + hi) >>> (s - 1)`. -/
def checkMagic32AddShift (d m' : Word) (s : Nat) : Bool :=
  decide (1 < d.toNat ∧ d.toNat < 2 ^ 32 ∧ m'.toNat < 2 ^ 32 ∧ 1 ≤ s ∧ s ≤ 32 ∧
    2 ^ (32 + s) ≤ d.toNat * (2 ^ 32 + m'.toNat) ∧
    (d.toNat * (2 ^ 32 + m'.toNat) - 2 ^ (32 + s)) * (2 ^ 32 - 1) < 2 ^ (32 + s))

/-! ## Untrusted parameter finders -/

/-- Find `k` (`0 < k < w.bits`) such that `w.truncate d = 2^k`. -/
def findPow2 (w : Width) (d : Word) : Option Nat :=
  let v := (w.truncate d).toNat
  if v ≤ 1 then none
  else
    let k := Nat.log2 v
    if isPow2 w d k then some k else none

/-- 64-bit Granlund–Montgomery magic parameters for constant divisor `d > 1`. -/
inductive Magic64 where
  /-- `q = (mulHi a m) >>> s` (omit shift if `s = 0`). -/
  | simple (m : Word) (s : Nat)
  /-- `hi = mulHi a m'`, `q = (((a - hi) >>> 1) + hi) >>> (s - 1)`. -/
  | addShift (m' : Word) (s : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Compute validated 64-bit magic multiplier parameters for non-power-of-2 `d > 1`. -/
def magicU64 (d : Word) : Option Magic64 :=
  let dn := d.toNat
  if dn ≤ 1 then none
  else
    let l := Nat.log2 (dn - 1) + 1
    -- Case 1: try s = l - 1 (smallest shift; m = ceil(2^(64+s) / d))
    let s1 := l - 1
    let p1 := 2 ^ (64 + s1)
    let m1 := (p1 + dn - 1) / dn
    if m1 < 2 ^ 64 && checkMagicSimple d (UInt64.ofNat m1) s1 then
      some (.simple (UInt64.ofNat m1) s1)
    else
      -- Case 2: try s = l with M = ceil(2^(64+l) / d) = 2^64 + m'
      let s2 := l
      let p2 := 2 ^ (64 + s2)
      let m2 := (p2 + dn - 1) / dn
      if 2 ^ 64 ≤ m2 && m2 - 2 ^ 64 < 2 ^ 64 &&
          checkMagicAddShift d (UInt64.ofNat (m2 - 2 ^ 64)) s2 then
        some (.addShift (UInt64.ofNat (m2 - 2 ^ 64)) s2)
      else none

/-- 32-bit magic parameters for constant divisor `1 < d < 2^32`. -/
inductive Magic32 where
  | simple (m : Word) (s : Nat)
  | addShift (m' : Word) (s : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Compute validated 32-bit magic multiplier parameters for non-power-of-2 `1 < d < 2^32`. -/
def magicU32 (d : Word) : Option Magic32 :=
  let dw := X86.Width.w32.truncate d
  let dn := dw.toNat
  if dn ≤ 1 then none
  else
    let l := Nat.log2 (dn - 1) + 1
    let s1 := l - 1
    let p1 := 2 ^ (32 + s1)
    let m1 := (p1 + dn - 1) / dn
    if m1 ≤ 2 ^ 32 && checkMagic32 dw (UInt64.ofNat m1) s1 then
      some (.simple (UInt64.ofNat m1) s1)
    else
      let s2 := l
      let p2 := 2 ^ (32 + s2)
      let m2 := (p2 + dn - 1) / dn
      if 2 ^ 32 ≤ m2 && m2 - 2 ^ 32 < 2 ^ 32 &&
          checkMagic32AddShift dw (UInt64.ofNat (m2 - 2 ^ 32)) s2 then
        some (.addShift (UInt64.ofNat (m2 - 2 ^ 32)) s2)
      else none

end IxCC.Lir.Opt
