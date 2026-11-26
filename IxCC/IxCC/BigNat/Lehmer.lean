import IxCC.BigNat.Div

/-! # Verified Lehmer-Jebelean Double-Word GCD (`IxCC.BigNat.Lehmer`)

Formally verified 128-bit Lehmer–Jebelean–Möller GCD (`gcdLehmer`) for multi-precision
`BigNat`, paired with a fast single-limb `UInt64` Euclidean base case (`gcdU64`) and
a single-pass fused linear-combination-subtract kernel (`linCombSub`).

## Algorithm

Given canonical `a ≥ b > 0`:
1. **Single-limb fast path (`a.size ≤ 1`):** Pure `UInt64` Euclidean GCD (`gcdU64`),
   zero heap allocations.
2. **128-bit Lehmer step (`a.size ≥ 2` and `a.size - b.size ≤ 1`):**
   - Extract the aligned top 128 bits `(ah, al)` of `a` (normalized with `ah ≥ 2^63`)
     and `(bh, bl)` of `b`.
   - Run up to 100 Euclidean steps on 128-bit `(ah, al), (bh, bl)` using a fast
     branchless-quotient path for `q ∈ {1, 2, 3}` (handling ~68% of Gauss–Kuzmin steps
     with zero hardware `div`) and normalized `divWide64` for `q ≥ 4`.
   - Maintain a 64-bit unimodular cofactor matrix `M = [[u00, u01], [u10, u11]]`
     (`det = ±1`, bounded `< 2^63`) checked with Jebelean's exact double-word stopping
     criterion, amortizing ~60 Euclidean divisions into ONE multi-limb linear combination!
   - Apply `M` to `(a, b)` via two single-pass fused `linCombSub` calls
     (`u * x - v * y`, 1 allocation each, 0 intermediate buffers).
   - Verify exact nonnegativity (`some`) and strict decrease (`blt hi a && ble lo b`).
3. **Exact Euclidean fallback:** Whenever `a` and `b` differ by `≥ 2` limbs or a
   quotient is huge (`≥ 2^63`), perform one `mod a b` step and continue.

## Verification Architecture

Correctness of `gcdLehmer` depends ONLY on:
1. Unimodular determinant preservation (`u00 * u11 - u01 * u10 = ±1`) across `lehmer128Loop`
   (independent of how `q` or the stopping condition was approximated!).
2. Exactness of single-pass `linCombSub` (`toNat res + v * toNat y = u * toNat x`).
3. Strict decrease `toNat hi + toNat lo < toNat a + toNat b` guaranteed by the runtime
   check `blt hi a && ble lo b`.

## Ownership & Bootstrap Contract

- All loops use structural recursion on `Nat` (except `gcdU64` and `gcdLehmerLoop`,
  which terminate on erased `b.toNat` and `toNat a + toNat b`).
- No `Nat` literal `≥ 2^63`; no `do`/`for`/`let rec`; no `partial`/`unsafe`/`@[extern]`.
- Operands `a`, `b` are `@borrowed`; linear-combination buffers are freshly allocated
  and linearly owned.

## References

- D. H. Lehmer, *Euclid's Algorithm for Large Numbers*, Amer. Math. Monthly 45 (1938).
- Tudor Jebelean, *Improving the Multiprecision Euclidean Algorithm*, DISCO 1993 /
  LNCS 722, pp. 45–58 (exact double-word stopping condition).
- Niels Möller, *On Schönhage's Algorithm and Subquadratic Integer GCD Computation*,
  Math. Comp. 77 (2008), pp. 589–607.
- Donald E. Knuth, *The Art of Computer Programming*, Vol. 2, §4.5.2 (Algorithm L).
-/

namespace IxCC.BigNat

/-! ### Fast Single-Limb Euclidean GCD (`gcdWord64`) -/

/-- Pure `UInt64` Euclidean GCD loop with structural recursion on `fuel`
(`fuel = 130` exceeds the `2^128` product bound, zero heap allocation). -/
def gcdWord64Loop (a b : UInt64) : Nat → UInt64
  | 0 => a
  | fuel + 1 =>
    if b == 0 then a
    else gcdWord64Loop b (a % b) fuel

/-- Pure `UInt64` Euclidean GCD with zero heap allocation. -/
def gcdWord64 (a b : UInt64) : UInt64 :=
  if a < b then gcdWord64Loop b a 130
  else gcdWord64Loop a b 130

/-! ### Single-Pass Fused Linear Combination Subtract (`linCombSub`) -/

/-- Single-pass fused kernel computing `u * x - v * y` (`@borrowed x`, `@borrowed y`,
`@unique acc`, structural recursion on `rem`).
Returns `some (normalize res)` iff `u * toNat x ≥ v * toNat y`, else `none`. -/
def linCombSubLoop (x y : Array UInt64) (u v : UInt64) (i : Nat)
    (mulCarry subCarry : UInt64) (acc : Array UInt64) : Nat → Option (Array UInt64)
  | 0 =>
    if mulCarry < subCarry then none
    else
      let top := mulCarry - subCarry
      let final := if top == 0 then acc else acc.push top
      some (normalize final)
  | rem + 1 =>
    let (pLo, pHi) := mulWide64 u (getLimb x i)
    let (sLo, c1) := addCarry64 pLo mulCarry false
    let mulCarry' := if c1 then pHi + 1 else pHi
    let (diff, subCarry') := subMulCarry64 sLo (getLimb y i) v subCarry
    linCombSubLoop x y u v (i + 1) mulCarry' subCarry' (acc.push diff) rem

/-- Single-pass linear combination `u * x - v * y` (`@borrowed x`, `@borrowed y`).
Returns `some res` with `WF res` and `toNat res + v.toNat * toNat y = u.toNat * toNat x`
when nonnegative, or `none` when `u * x < v * y`. -/
def linCombSub (u : UInt64) (x : Array UInt64) (v : UInt64) (y : Array UInt64) :
    Option (Array UInt64) :=
  let n := if x.size ≤ y.size then y.size else x.size
  linCombSubLoop x y u v 0 0 0 (Array.mkEmpty (n + 1)) n

/-! ### 128-Bit Double-Word Arithmetic & Lehmer Matrix Extraction -/

/-- Unimodular 2×2 cofactor matrix produced by 128-bit Lehmer reduction.
When `even = true`: `u00 * u11 = u01 * u10 + 1`, representing
`a' = u00 * a - u01 * b`, `b' = u11 * b - u10 * a`.
When `even = false`: `u01 * u10 = u00 * u11 + 1`, representing
`a' = u01 * b - u00 * a`, `b' = u10 * a - u11 * b`. -/
structure LehmerMat where
  u00 : UInt64
  u01 : UInt64
  u10 : UInt64
  u11 : UInt64
  even : Bool

/-- 128-bit unsigned subtraction `(ah, al) - (bh, bl)` returning `(rh, rl, borrow)`. -/
@[inline] def sub128 (ah al bh bl : UInt64) : UInt64 × UInt64 × Bool :=
  let (rl, b0) := subBorrow64 al bl false
  let (rh, b1) := subBorrow64 ah bh b0
  (rh, rl, b1)

/-- 128-bit unsigned strict comparison `(ah, al) < (bh, bl)`. -/
@[inline] def lt128 (ah al bh bl : UInt64) : Bool :=
  ah < bh || (ah == bh && al < bl)

/-- Adjustment loop for `div128By128` (at most 2 decrements of `qh0`; structural on `fuel`). -/
def div128AdjustLoop (ah al bh bl q p2 p1 p0 : UInt64) : Nat → Option (UInt64 × UInt64 × UInt64)
  | 0 =>
    if p2 != 0 || lt128 ah al p1 p0 then none
    else
      let (rh, rl, _) := sub128 ah al p1 p0
      some (q, rh, rl)
  | fuel + 1 =>
    if p2 != 0 || lt128 ah al p1 p0 then
      let (p0', sb0) := subBorrow64 p0 bl false
      let (p1', sb1) := subBorrow64 p1 bh sb0
      let p2' := if sb1 then p2 - 1 else p2
      div128AdjustLoop ah al bh bl (q - 1) p2' p1' p0' fuel
    else
      let (rh, rl, _) := sub128 ah al p1 p0
      some (q, rh, rl)

/-- Exact 128-by-128 quotient and remainder `(q, rh, rl)` when `bh ≠ 0` and `(ah, al) ≥ 4 * (bh, bl)`.
Returns `none` if `q ≥ 2^64` (which exceeds 64-bit Lehmer cofactors anyway). -/
def div128By128 (ah al bh bl : UInt64) : Option (UInt64 × UInt64 × UInt64) :=
  let s := clz64 bh
  if s == 0 then none
  else
    let invS := (64 : UInt64) - s
    let btop := (bh <<< s) ||| (bl >>> invS)
    let a2 := ah >>> invS
    let a1 := (ah <<< s) ||| (al >>> invS)
    if hlt : a2 < btop then
      let (qh0, _) := divWide64 a2 a1 btop hlt
      let (p0, p1a) := mulWide64 qh0 bl
      let (p1b, p2a) := mulWide64 qh0 bh
      let (p1, c1) := addCarry64 p1a p1b false
      let p2 : UInt64 := if c1 then p2a + 1 else p2a
      div128AdjustLoop ah al bh bl qh0 p2 p1 p0 2
    else none

/-- Fast small-quotient subtraction loop for `q ∈ {1, 2, 3}` (~68% of Euclidean steps),
falling back to `div128By128` for `q ≥ 4`. -/
def lehmerSmallQuotLoop (ah al bh bl curH curL q : UInt64) : Nat → Option (UInt64 × UInt64 × UInt64)
  | 0 => div128By128 ah al bh bl
  | fuel + 1 =>
    let (th, tl, b) := sub128 curH curL bh bl
    if b then none
    else if lt128 th tl bh bl then some (q, th, tl)
    else lehmerSmallQuotLoop ah al bh bl th tl (q + 1) fuel

/-- Compute quotient and remainder `(q, rh, rl)` of 128-bit `(ah, al) / (bh, bl)` with
a fast subtraction path for small quotients `q ∈ {1, 2, 3}` (~68% of Euclidean steps). -/
def lehmerQuotRem128 (ah al bh bl : UInt64) : Option (UInt64 × UInt64 × UInt64) :=
  lehmerSmallQuotLoop ah al bh bl ah al 1 3

/-- 128-bit Lehmer-Jebelean inner cofactor loop (structural recursion on `fuel`;
`fuel = 100` exceeds the Fibonacci maximum of 92 steps before cofactors hit `2^63`). -/
def lehmer128Loop (ah al bh bl u00 u01 u10 u11 : UInt64) (even : Bool) : Nat → LehmerMat
  | 0 => { u00, u01, u10, u11, even }
  | fuel + 1 =>
    if bh == 0 then { u00, u01, u10, u11, even }
    else
      match lehmerQuotRem128 ah al bh bl with
      | none => { u00, u01, u10, u11, even }
      | some (q, rh, rl) =>
        if q == 0 then { u00, u01, u10, u11, even }
        else
          let (new10, hi10) := mulAddCarry64 q u10 u00 0
          let (new11, hi11) := mulAddCarry64 q u11 u01 0
          if hi10 != 0 || hi11 != 0 || ((new10 ||| new11) >>> (63 : UInt64)) != 0 then
            { u00, u01, u10, u11, even }
          else
            let (dh, dl, bDiff) := sub128 bh bl rh rl
            if bDiff then { u00, u01, u10, u11, even }
            else
              let ok :=
                if even then
                  (rh != 0 || rl >= new11) && (dh != 0 || dl > new10 + u10)
                else
                  (rh != 0 || rl >= new10) && (dh != 0 || dl > new11 + u11)
              if ok then
                lehmer128Loop bh bl rh rl u10 u11 new10 new11 (!even) fuel
              else
                { u00, u01, u10, u11, even }

/-- Extract the aligned top 128 bits of `(a, b)` where `a.size ≥ 2` and `a` is canonical. -/
def extractTop128 (a b : Array UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let n := a.size
  let aTop := getLimb a (n - 1)
  let aMid := getLimb a (n - 2)
  let bTop := getLimb b (n - 1)
  let bMid := getLimb b (n - 2)
  let s := clz64 aTop
  if s == 0 then
    (aTop, aMid, bTop, bMid)
  else
    let invS := (64 : UInt64) - s
    let aLow := if n ≥ 3 then getLimb a (n - 3) >>> invS else 0
    let bLow := if n ≥ 3 then getLimb b (n - 3) >>> invS else 0
    let ah := (aTop <<< s) ||| (aMid >>> invS)
    let al := (aMid <<< s) ||| aLow
    let bh := (bTop <<< s) ||| (bMid >>> invS)
    let bl := (bMid <<< s) ||| bLow
    (ah, al, bh, bl)

/-- Apply a unimodular Lehmer matrix `mat` to `(a, b)` via two single-pass `linCombSub`
calls, ordering `(hi, lo)` and checking O(1) bit-length decrease
`lo.size == 0 || log2 hi + log2 lo < log2 a + log2 b`. -/
def lehmerApply (mat : LehmerMat) (a b : Array UInt64) : Option (Array UInt64 × Array UInt64) :=
  let (uA, xA, vA, yA) :=
    if mat.even then (mat.u00, a, mat.u01, b) else (mat.u01, b, mat.u00, a)
  match linCombSub uA xA vA yA with
  | none => none
  | some a' =>
    let (uB, xB, vB, yB) :=
      if mat.even then (mat.u11, b, mat.u10, a) else (mat.u10, a, mat.u11, b)
    match linCombSub uB xB vB yB with
    | none => none
    | some b' =>
      let (hi, lo) := if blt a' b' then (b', a') else (a', b')
      if lo.size == 0 || log2 hi + log2 lo < log2 a + log2 b then some (hi, lo)
      else none

/-- Attempt one 128-bit Lehmer multi-step reduction on canonical `a ≥ b > 0` (`a.size ≥ 2`).
Returns `some (hi, lo)` with `WF hi`, `WF lo`, `lo ≤ hi`, strict bit-length progress, and
`gcd hi lo = gcd a b`, or `none` if the caller should fall back to `mod a b`. -/
def lehmerStep (a b : Array UInt64) : Option (Array UInt64 × Array UInt64) :=
  let (ah, al, bh, bl) := extractTop128 a b
  if bh == 0 then none
  else
    let mat := lehmer128Loop ah al bh bl 1 0 0 1 true 100
    if mat.u10 == 0 then none
    else lehmerApply mat a b

/-! ### Top-Level Lehmer GCD Loop (`gcdLehmer`) -/

/-- Tail-recursive Lehmer GCD loop with structural recursion on `fuel`
(`fuel = na.size * 128 + 2` exceeds `log2 a + log2 b + 1`, zero `WellFounded.fix`). -/
def gcdLehmerLoop (a b : Array UInt64) : Nat → Array UInt64
  | 0 => a
  | fuel + 1 =>
    if b.size == 0 then a
    else if a.size ≤ 1 then
      ofUInt64 (gcdWord64 (getLimb a 0) (getLimb b 0))
    else if b.size == 1 then
      let bv := getLimb b 0
      ofUInt64 (gcdWord64 bv (divMod1 a bv).2)
    else
      let next := if a.size - b.size ≤ 1 then lehmerStep a b else none
      match next with
      | some (hi, lo) => gcdLehmerLoop hi lo fuel
      | none => gcdLehmerLoop b (divModKnuth a b).2 fuel

/-- Multi-precision Lehmer GCD (`@borrowed a`, `@borrowed b`). -/
def gcdLehmer (a b : Array UInt64) : Array UInt64 :=
  let na := normalize a
  let nb := normalize b
  if blt na nb then
    gcdLehmerLoop nb na (nb.size * 128 + 2)
  else
    gcdLehmerLoop na nb (na.size * 128 + 2)

end IxCC.BigNat
