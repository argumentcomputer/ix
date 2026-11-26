import IxCC.BigNat.Div
import IxCC.BigNat.Lehmer

/-! # BigNat GCD and Chunked Decimal Conversion (`IxCC.BigNat.GcdConv`)

128-bit Lehmer–Jebelean greatest common divisor (`gcd`), single-limb multiply-add
(`mulAdd1`), and base-`10^19` chunked decimal conversion (`toDecimalChunks`,
`ofDecimalChunks`, `toDecimalDigits`, `ofDecimalDigits`, `toDecimal`, `ofDecimal`).

## Ownership & Bootstrap Contract

- All runtime functions are monomorphic, first-order, structurally recursive on
  `Nat`/`List` (zero `WellFounded.fix`, zero `Proof.*` imports), and never construct
  any `Nat` value `≥ 2^63`.
-/

namespace IxCC.BigNat

/-- `10^19` as a `UInt64`, built as `10^10 * 10^9` so no `Nat` literal `≥ 2^63` appears. -/
@[inline] def ten19 : UInt64 := (10000000000 : UInt64) * (1000000000 : UInt64)

/-! ### Euclidean Greatest Common Divisor (`gcd`) -/

/-- Multi-precision greatest common divisor matching `Nat.gcd` via 128-bit Lehmer GCD
(`@borrowed a`, `@borrowed b`). -/
@[inline] def gcd (a b : Array UInt64) : Array UInt64 :=
  gcdLehmer a b

/-! ### Single-Limb Multiply-Add (`mulAdd1`) -/

/-- Linear multiply-add loop: computes `a * m + carry` (`@borrowed a`, `@unique acc`,
structural recursion on `rem`, single `addCarry64` per limb). -/
def mulAdd1Loop (a : Array UInt64) (m : UInt64) (i : Nat) (carry : UInt64)
    (acc : Array UInt64) : Nat → Array UInt64
  | 0 => if carry == 0 then acc else acc.push carry
  | rem + 1 =>
    let (pLo, pHi) := mulWide64 (getLimb a i) m
    let (lo, c) := addCarry64 pLo carry false
    let carry' := if c then pHi + 1 else pHi
    mulAdd1Loop a m (i + 1) carry' (acc.push lo) rem

/-- Fast `O(n)` single-limb multiply-add: `toNat (mulAdd1 a m c) = toNat a * m.toNat + c.toNat`. -/
def mulAdd1 (a : Array UInt64) (m c : UInt64) : Array UInt64 :=
  if m == 0 then ofUInt64 c
  else if m == 1 && c == 0 then normalize a
  else if m == 2 && c == 0 then shiftLeft1 a
  else normalize (mulAdd1Loop a m 0 c (Array.mkEmpty (a.size + 1)) a.size)

/-! ### Base-`10^19` Chunked Decimal Conversion -/

/-- Repeatedly divide by `10^19`, accumulating big-endian base-`10^19` chunks with structural
recursion on `fuel` (`fuel = n.size * 2 + 1` exceeds the exact chunk count since `2^64 < (10^19)^2`). -/
def toDecimalChunksLoop (a : Array UInt64) (acc : List UInt64) : Nat → List UInt64
  | 0 => acc
  | fuel + 1 =>
    if a.size == 0 then acc
    else
      let res := divMod1 a ten19
      toDecimalChunksLoop res.1 (res.2 :: acc) fuel

/-- Convert a `BigNat` to its canonical big-endian list of base-`10^19` `UInt64` chunks
(`[]` for `0`; every chunk `< 10^19`). -/
def toDecimalChunks (a : Array UInt64) : List UInt64 :=
  let n := normalize a
  toDecimalChunksLoop n [] (n.size * 2 + 1)

/-- Horner accumulation of big-endian base-`10^19` `UInt64` chunks into a `BigNat`. -/
def ofDecimalChunksLoop (cs : List UInt64) (acc : Array UInt64) : Array UInt64 :=
  match cs with
  | [] => acc
  | c :: rest => ofDecimalChunksLoop rest (mulAdd1 acc ten19 c)

/-- Convert a big-endian list of base-`10^19` `UInt64` chunks to a canonical `BigNat`. -/
def ofDecimalChunks (cs : List UInt64) : Array UInt64 :=
  ofDecimalChunksLoop cs #[]

/-! ### Decimal Digits and String Formatting / Parsing -/

/-- Prepend exact `k` decimal digits (`0..9`) of `x` onto `acc` (fixed width, zero-padded). -/
def u64ToDigitsPad (x : UInt64) : Nat → List UInt8 → List UInt8
  | 0, acc => acc
  | k + 1, acc =>
    let d := (x % (10 : UInt64)).toUInt8
    u64ToDigitsPad (x / (10 : UInt64)) k (d :: acc)

/-- Structural-fuel helper prepending minimal decimal digits (`0..9`) of `x` onto `acc`
(`fuel = 20` exceeds `2^64 < 10^20`). -/
def u64ToDigitsMinimalLoop (x : UInt64) (acc : List UInt8) : Nat → List UInt8
  | 0 => acc
  | fuel + 1 =>
    if x == 0 then acc
    else
      let d := (x % (10 : UInt64)).toUInt8
      u64ToDigitsMinimalLoop (x / (10 : UInt64)) (d :: acc) fuel

/-- Prepend minimal decimal digits (`0..9`) of nonzero `x` onto `acc`. -/
def u64ToDigitsMinimal (x : UInt64) (acc : List UInt8) : List UInt8 :=
  u64ToDigitsMinimalLoop x acc 20

/-- Format reversed (least-significant-first) base-`10^19` chunks into big-endian decimal digits. -/
def chunksRevToDigits (revChunks : List UInt64) (acc : List UInt8) : List UInt8 :=
  match revChunks with
  | [] => acc
  | [head] =>
    if head == 0 then
      match acc with
      | [] => [0]
      | _ => acc
    else u64ToDigitsMinimal head acc
  | c :: rest => chunksRevToDigits rest (u64ToDigitsPad c 19 acc)

/-- Convert a `BigNat` to its canonical big-endian list of decimal digits `0..9`
(`[0]` for `0`; no leading zeros for nonzero values). -/
def toDecimalDigits (a : Array UInt64) : List UInt8 :=
  let chunks := toDecimalChunks a
  match chunks with
  | [] => [0]
  | _ => chunksRevToDigits chunks.reverse []

/-- Convert a list of decimal digits `0..9` to ASCII characters `'0'..'9'`. -/
def digitsToCharsLoop (ds : List UInt8) (acc : List Char) : List Char :=
  match ds with
  | [] => acc.reverse
  | d :: rest => digitsToCharsLoop rest (Char.ofNat (48 + d.toNat) :: acc)

/-- Convert a `BigNat` to its canonical base-10 ASCII string (via `10^19` chunked division). -/
def toDecimal (a : Array UInt64) : String :=
  String.ofList (digitsToCharsLoop (toDecimalDigits a) [])

/-- Chunked 19-digit decimal parser accumulating `UInt64` blocks before calling `mulAdd1`. -/
def ofDecimalDigitsLoop (ds : List UInt8) (chunkVal chunkPow : UInt64) (cnt : Nat)
    (acc : Array UInt64) : Array UInt64 :=
  match ds with
  | [] =>
    if cnt == 0 then acc else mulAdd1 acc chunkPow chunkVal
  | d :: rest =>
    let v := chunkVal * (10 : UInt64) + d.toUInt64
    let p := chunkPow * (10 : UInt64)
    if cnt + 1 == 19 then
      ofDecimalDigitsLoop rest 0 1 0 (mulAdd1 acc p v)
    else
      ofDecimalDigitsLoop rest v p (cnt + 1) acc

/-- Parse a big-endian list of decimal digits (`0..9`) into a canonical `BigNat`
in 19-digit chunks. -/
def ofDecimalDigits (ds : List UInt8) : Array UInt64 :=
  ofDecimalDigitsLoop ds 0 1 0 #[]

/-- Parse ASCII chars `'0'..'9'` into digits `0..9`, returning `none` on any non-digit. -/
def parseAsciiDigitsLoop (cs : List Char) (acc : List UInt8) : Option (List UInt8) :=
  match cs with
  | [] => some acc.reverse
  | c :: rest =>
    let n := c.toNat
    if 48 ≤ n && n ≤ 57 then
      parseAsciiDigitsLoop rest (UInt8.ofNat (n - 48) :: acc)
    else
      none

/-- Parse a non-empty ASCII decimal string into a canonical `BigNat` (in 19-digit chunks),
returning `none` on empty input or invalid characters. -/
def ofDecimal (s : String) : Option (Array UInt64) :=
  match s.toList with
  | [] => none
  | cs =>
    match parseAsciiDigitsLoop cs [] with
    | none => none
    | some ds => some (ofDecimalDigits ds)

end IxCC.BigNat
