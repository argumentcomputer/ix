import IxCC.BigNat.Div
import IxCC.BigNat.Proof.Div

/-! # BigNat GCD and Chunked Decimal Conversion (`IxCC.BigNat.GcdConv`)

Euclidean greatest common divisor (`gcd`) over `divMod`, single-limb multiply-add
(`mulAdd1`), and base-`10^19` chunked decimal conversion (`toDecimalChunks`,
`ofDecimalChunks`, `toDecimalDigits`, `ofDecimalDigits`, `toDecimal`, `ofDecimal`).

## Algorithms

- **GCD (`gcd`):** Tail-recursive Euclidean algorithm `gcd(a, b) = gcd(b, a mod b)`
  using `BigNat.mod`, terminating on `toNat b` (erased proof measure; zero runtime
  `toNat` or fuel overhead).
- **Decimal conversion (`toDecimal` / `ofDecimal`):**
  - `toDecimalChunks` repeatedly divides by `10^19 = 10_000_000_000 * 1_000_000_000`
    (the largest power of 10 fitting in `UInt64`, constructed without any `Nat`
    literal `≥ 2^63`) via `divMod1`, reducing multi-precision division work by 19×.
  - `ofDecimalDigits` accumulates 19-digit decimal chunks in a single `UInt64`
    before flushing via linear-time `mulAdd1`.

## Ownership & Bootstrap Contract

- All runtime functions are monomorphic, first-order, tail-recursive (modulo
  `List` digit formatting), and never construct any `Nat` value `≥ 2^63`.
- Termination proofs (`WF`, `toNat_mod_lt`, `toNat_divMod1_lt`) live in `Prop`
  and are completely erased at runtime.

## References

- Donald E. Knuth, *The Art of Computer Programming*, Vol. 2, §4.4 (Radix Conversion)
  and §4.5.2 (The Greatest Common Divisor, Algorithm A).
- Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone, *Handbook of Applied
  Cryptography*, Ch. 14 (Algorithm 14.54 / Euclidean GCD).
- Richard P. Brent and Paul Zimmermann, *Modern Computer Arithmetic*, §1.7 (Radix Conversion).
-/

namespace IxCC.BigNat

/-- `10^19` as a `UInt64`, built as `10^10 * 10^9` so no `Nat` literal `≥ 2^63` appears. -/
@[inline] def ten19 : UInt64 := (10000000000 : UInt64) * (1000000000 : UInt64)

theorem ten19_toNat : ten19.toNat = 10 ^ 19 := by
  unfold ten19
  rw [UInt64.toNat_mul]
  rfl

theorem ten19_gt_one : 1 < ten19.toNat := by
  rw [ten19_toNat]
  omega

theorem ten19_ne_zero : ten19 ≠ 0 := by
  intro h
  have := congrArg UInt64.toNat h
  rw [ten19_toNat] at this
  have hpos : 0 < 10 ^ 19 := Nat.pow_pos (by decide)
  have h0 : (0 : UInt64).toNat = 0 := rfl
  omega

/-! ### Euclidean Greatest Common Divisor (`gcd`) -/

/-- Tail-recursive Euclidean GCD loop (`@borrowed a`, `@borrowed b`, erased `hb : WF b`). -/
def gcdLoop (a b : Array UInt64) (hb : WF b) : Array UInt64 :=
  if hz : b.size = 0 then a
  else
    let r := mod a b
    have hr : WF r := wf_mod a b
    have _hlt : toNat r < toNat b := toNat_mod_lt a b hb hz
    gcdLoop b r hr
termination_by toNat b

/-- Multi-precision greatest common divisor matching `Nat.gcd` (`@borrowed a`, `@borrowed b`). -/
def gcd (a b : Array UInt64) : Array UInt64 :=
  gcdLoop (normalize a) (normalize b) (wf_normalize b)

/-! ### Single-Limb Multiply-Add (`mulAdd1`) -/

/-- Linear multiply-add loop: computes `a * m + carry` (`@borrowed a`, `@unique acc`). -/
def mulAdd1Loop (a : Array UInt64) (m : UInt64) (i : Nat) (carry : UInt64)
    (acc : Array UInt64) : Array UInt64 :=
  if h : i < a.size then
    let (lo, carry') := mulAddCarry64 a[i] m 0 carry
    mulAdd1Loop a m (i + 1) carry' (acc.push lo)
  else
    if carry == 0 then acc else acc.push carry
termination_by a.size - i

/-- Fast `O(n)` single-limb multiply-add: `toNat (mulAdd1 a m c) = toNat a * m.toNat + c.toNat`. -/
def mulAdd1 (a : Array UInt64) (m c : UInt64) : Array UInt64 :=
  normalize (mulAdd1Loop a m 0 c (Array.mkEmpty (a.size + 1)))

/-! ### Base-`10^19` Chunked Decimal Conversion -/

/-- Repeatedly divide by `10^19`, accumulating big-endian base-`10^19` chunks (`@borrowed a`). -/
def toDecimalChunksLoop (a : Array UInt64) (ha : WF a) (acc : List UInt64) : List UInt64 :=
  if hz : a.size = 0 then acc
  else
    let res := divMod1 a ten19
    have hq : WF res.1 := wf_divMod1 a ten19
    have _hlt : toNat res.1 < toNat a := toNat_divMod1_lt a ten19 ha hz ten19_gt_one
    toDecimalChunksLoop res.1 hq (res.2 :: acc)
termination_by toNat a

/-- Convert a `BigNat` to its canonical big-endian list of base-`10^19` `UInt64` chunks
(`[]` for `0`; every chunk `< 10^19`). -/
def toDecimalChunks (a : Array UInt64) : List UInt64 :=
  toDecimalChunksLoop (normalize a) (wf_normalize a) []

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

/-- Prepend minimal decimal digits (`0..9`) of nonzero `x` onto `acc`. -/
def u64ToDigitsMinimal (x : UInt64) (acc : List UInt8) : List UInt8 :=
  if h : x = 0 then acc
  else
    have hlt : (x / (10 : UInt64)).toNat < x.toNat := by
      rw [UInt64.toNat_div]
      have hx : 0 < x.toNat := by
        have : x.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      have h10 : (10 : UInt64).toNat = 10 := rfl
      rw [h10]
      exact Nat.div_lt_self hx (by decide)
    let d := (x % (10 : UInt64)).toUInt8
    u64ToDigitsMinimal (x / (10 : UInt64)) (d :: acc)
termination_by x.toNat

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
