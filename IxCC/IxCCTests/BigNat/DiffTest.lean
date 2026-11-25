import IxCC.BigNat
import IxCC.BigNat.NatEntry

/-! # Differential Fuzz Test Suite for `IxCC.BigNat` (`IxCCTests.BigNat.DiffTest`)

Executable pure-Lean differential oracle comparing EVERY `IxCC.BigNat` operation
against Lean's GMP-backed `Nat` across 100,000+ randomized and adversarial cases:
- Boundary values: `0`, `1`, `2^63-1`, `2^63`, `2^64-1`, `2^64`, `10^19`, `2^128`,
  all-`0xFFFFFFFFFFFFFFFF` limb runs, sparse powers of 2.
- Karatsuba threshold boundaries: 31, 32, 33, 63, 64, 65, 127, 128, 129, 256, 512, 1000 limbs.
- Knuth Algorithm D rare `q̂ - 1` add-back triggers (explicitly verified to fire!).
- Zero divisors (`n / 0 = 0`, `n % 0 = n`).
- Large operands up to 1,000 limbs (64,000 bits).
- Canonical `WF` normal-form check on EVERY output.
- The entries over `Nat` (`IxCC.BigNat.NatEntry`) and the two representation primitives
  (`IxCC.NatRep.toLimbs`, `ofLimbs`) against `Nat` itself, including the canonical equation
  of `toLimbs`, limb arrays that are not canonical, and counts beyond the tagged range.

Run with: `lake env lean --run IxCCTests/BigNat/DiffTest.lean` (or compile via `leanc`).
-/

namespace IxCCTests.BigNat.DiffTest

open IxCC.BigNat

/-- Deterministic SplitMix64 PRNG for reproducible fuzzing. -/
structure Rng where
  state : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.state + (0x9e3779b97f4a7c15 : UInt64)
  let z := (s ^^^ (s >>> 30)) * (0xbf58476d1ce4e5b9 : UInt64)
  let z := (z ^^^ (z >>> 27)) * (0x94d049bb133111eb : UInt64)
  let z := z ^^^ (z >>> 31)
  (z, { state := s })

def Rng.nextRange (r : Rng) (bound : Nat) : Nat × Rng :=
  if bound == 0 then (0, r)
  else
    let (w, r') := r.next
    (w.toNat % bound, r')

/-- Generate a random `BigNat` of up to `maxLimbs` limbs (biased toward interesting bit patterns). -/
def Rng.nextBigNat (r : Rng) (limbs : Nat) : Array UInt64 × Rng :=
  let (mode, r) := r.nextRange 8
  let rec go (k : Nat) (r : Rng) (acc : Array UInt64) : Array UInt64 × Rng :=
    match k with
    | 0 => (normalize acc, r)
    | k' + 1 =>
      let (w, r') := r.next
      let limb :=
        if mode == 0 then maxWord64                 -- all-ones stress
        else if mode == 1 then if w % 4 == 0 then 0 else maxWord64  -- sparse all-ones
        else if mode == 2 then if w % 3 == 0 then 0 else w          -- sparse random
        else if mode == 3 then ((1 : UInt64) <<< (w % 64))          -- single-bit limbs
        else w                                                       -- uniform random
      go k' r' (acc.push limb)
  go limbs r (Array.mkEmpty limbs)

/-- Runtime check of canonical normal form `WF`. -/
def isWF (xs : Array UInt64) : Bool :=
  if h : 0 < xs.size then xs[xs.size - 1] != 0 else true

structure Stats where
  total : Nat := 0
  failures : Nat := 0
  addBackHits : Nat := 0
  lehmerHits : Nat := 0
  lehmerFallbacks : Nat := 0
  divRem21Step5Hits : Nat := 0
  divRem21Step6Hits : Nat := 0

def check (st : Stats) (cond : Bool) (msg : Unit → String) : IO Stats := do
  if cond then
    pure { st with total := st.total + 1 }
  else
    if st.failures < 20 then
      IO.eprintln s!"FAIL: {msg ()}"
    pure { st with total := st.total + 1, failures := st.failures + 1 }

/-- Check all LimbOps on a sample of words. -/
def testLimbOps (st : Stats) (r : Rng) (count : Nat) : IO (Stats × Rng) := do
  let edgeWords : Array UInt64 := #[
    0, 1, 2, 3, 7, 10, 63, 64, 65,
    (1 : UInt64) <<< 32, ((1 : UInt64) <<< 32) - 1,
    ((1 : UInt64) <<< 63) - 1, (1 : UInt64) <<< 63, ((1 : UInt64) <<< 63) + 1,
    ten19 - 1, ten19, ten19 + 1,
    maxWord64 - 1, maxWord64
  ]
  let mut st := st
  let mut r := r
  for a in edgeWords do
    for b in edgeWords do
      for c in #[false, true] do
        let (lo, cOut) := addCarry64 a b c
        st ← check st (lo.toNat + cOut.toNat * 2 ^ 64 == a.toNat + b.toNat + c.toNat)
          (fun _ => s!"addCarry64 {a} {b} {c}")
        let (dlo, bOut) := subBorrow64 a b c
        st ← check st (dlo.toNat + b.toNat + c.toNat == a.toNat + bOut.toNat * 2 ^ 64)
          (fun _ => s!"subBorrow64 {a} {b} {c}")
      let (mlo, mhi) := mulWide64 a b
      st ← check st (mlo.toNat + mhi.toNat * 2 ^ 64 == a.toNat * b.toNat)
        (fun _ => s!"mulWide64 {a} {b}")
      if h : a < b then
        let (q, rem) := divWide64 a b b h
        st ← check st (q.toNat * b.toNat + rem.toNat == a.toNat * 2 ^ 64 + b.toNat && rem < b)
          (fun _ => s!"divWide64 {a} {b} {b}")
    let lz := clz64 a
    let okClz := if a == 0 then lz == 64 else
      lz.toNat < 64 && 2 ^ (63 - lz.toNat) ≤ a.toNat && a.toNat < 2 ^ (64 - lz.toNat)
    st ← check st okClz (fun _ => s!"clz64 {a} = {lz}")
  for _ in [:count] do
    let (a, r1) := r.next
    let (b, r2) := r1.next
    let (c, r3) := r2.next
    let (d, r4) := r3.next
    r := r4
    let (lo, hi) := mulAddCarry64 a b c d
    st ← check st (lo.toNat + hi.toNat * 2 ^ 64 == a.toNat * b.toNat + c.toNat + d.toNat)
      (fun _ => s!"mulAddCarry64 {a} {b} {c} {d}")
    if h : a < d then
      let (q, rem) := divWide64 a b d h
      st ← check st (q.toNat * d.toNat + rem.toNat == a.toNat * 2 ^ 64 + b.toNat && rem < d)
        (fun _ => s!"divWide64 {a} {b} {d}")
  pure (st, r)

/-- Check all linear ops on a pair `(a, b)`. -/
def checkLinearPair (st : Stats) (a b : Array UInt64) : IO Stats := do
  let na := toNat a
  let nb := toNat b
  let mut st := st
  -- cmp / beq / ble / blt
  st ← check st (cmp a b == compare na nb) (fun _ => s!"cmp {na} {nb}")
  st ← check st (beq a b == (na == nb)) (fun _ => s!"beq {na} {nb}")
  st ← check st (ble a b == decide (na ≤ nb)) (fun _ => s!"ble {na} {nb}")
  st ← check st (blt a b == decide (na < nb)) (fun _ => s!"blt {na} {nb}")
  -- add
  let s := add a b
  st ← check st (isWF s && toNat s == na + nb) (fun _ => s!"add {na} {nb}")
  -- sub & subRaw
  let d := sub a b
  st ← check st (isWF d && toNat d == na - nb) (fun _ => s!"sub {na} {nb}")
  let dr := subRaw a b
  st ← check st (isWF dr && toNat dr == na - nb) (fun _ => s!"subRaw {na} {nb}")
  -- pred
  let p := pred a
  st ← check st (isWF p && toNat p == na - 1) (fun _ => s!"pred {na}")
  -- land / lor / xor
  let la := land a b
  st ← check st (isWF la && toNat la == (na &&& nb)) (fun _ => s!"land {na} {nb}")
  let lo := lor a b
  st ← check st (isWF lo && toNat lo == (na ||| nb)) (fun _ => s!"lor {na} {nb}")
  let lx := xor a b
  st ← check st (isWF lx && toNat lx == (na ^^^ nb)) (fun _ => s!"xor {na} {nb}")
  -- log2
  st ← check st (log2 a == Nat.log2 na) (fun _ => s!"log2 {na}")
  -- toSmall?
  let expectedSmall := if na < 2 ^ 63 then some na else none
  st ← check st (toSmall? a == expectedSmall) (fun _ => s!"toSmall? {na}")
  -- ofNat roundtrip
  let rt := ofNat na
  st ← check st (isWF rt && rt == a) (fun _ => s!"ofNat roundtrip {na}")
  pure st

/-- Exhaustive boundary cases covering 2^63-1, 2^63, 2^64-1, 2^64, 10^19, etc. -/
def testBoundaries (st : Stats) : IO Stats := do
  let vals : Array Nat := #[
    0, 1, 2, 3, 7, 9, 10, 15, 16, 63, 64, 65, 127, 128,
    2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1,
    2 ^ 63 - 2, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1,
    10 ^ 19 - 1, 10 ^ 19, 10 ^ 19 + 1,
    2 ^ 64 - 2, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1,
    2 ^ 127 - 1, 2 ^ 127, 2 ^ 128 - 1, 2 ^ 128, 2 ^ 128 + 1,
    10 ^ 38 - 1, 10 ^ 38, 10 ^ 38 + 1,
    2 ^ 192 - 1, 2 ^ 192, 2 ^ 256 - 1, 2 ^ 256
  ]
  let bigs := vals.map ofNat
  let mut st := st
  for a in bigs do
    for b in bigs do
      st ← checkLinearPair st a b
      let na := toNat a
      let nb := toNat b
      -- mulSchoolbook & mul
      let ms := mulSchoolbook a b
      st ← check st (isWF ms && toNat ms == na * nb) (fun _ => s!"mulSchoolbook boundary")
      let mk := mul a b
      st ← check st (isWF mk && toNat mk == na * nb) (fun _ => s!"mul boundary")
      -- divMod / div / mod (including b = 0!)
      let (q, rem) := divMod a b
      st ← check st (isWF q && isWF rem && toNat q == na / nb && toNat rem == na % nb)
        (fun _ => s!"divMod boundary {na} / {nb}")
      -- gcd
      let g := gcd a b
      st ← check st (isWF g && toNat g == Nat.gcd na nb) (fun _ => s!"gcd boundary")
    -- sqr & decimal
    let na := toNat a
    let sq := sqr a
    st ← check st (isWF sq && toNat sq == na * na) (fun _ => s!"sqr boundary")
    let dec := toDecimal a
    st ← check st (dec == toString na) (fun _ => s!"toDecimal boundary {na}: got {dec}")
    st ← check st (ofDecimal dec == some a) (fun _ => s!"ofDecimal boundary {na}")
    -- shifts
    for sh in #[0, 1, 2, 31, 32, 63, 64, 65, 127, 128, 129, 255, 256, 512] do
      let sl := shiftLeft a sh
      st ← check st (isWF sl && toNat sl == (na <<< sh)) (fun _ => s!"shiftLeft {sh}")
      let sr := shiftRight a sh
      st ← check st (isWF sr && toNat sr == (na >>> sh)) (fun _ => s!"shiftRight {sh}")
  -- Negative tests for ofDecimal
  for bad in #["", " ", "12a3", "-5", "+1", "12 34", "/", ":"] do
    st ← check st (ofDecimal bad == none) (fun _ => s!"ofDecimal bad '{bad}'")
  pure st

/-- Helper to detect whether Knuth D Step D4 actually triggers add-back on `(u, v)`. -/
def countKnuthAddBack (u v : Array UInt64) : Nat :=
  let u := normalize u
  let v := normalize v
  if v.size < 2 || u.size < v.size then 0
  else
    let n := v.size
    let m := u.size - n
    let s := (clz64 (getLimb v (n - 1))).toNat
    let vn := shiftLeft v s
    let un := padZeros (shiftLeft u s) (m + n + 1)
    let vn1 := getLimb vn (n - 1)
    let vn2 := getLimb vn (n - 2)
    let rec go (rem : Array UInt64) (steps hits : Nat) : Nat :=
      match steps with
      | 0 => hits
      | j + 1 =>
        let u2 := getLimb rem (j + n)
        let u1 := getLimb rem (j + n - 1)
        let u0 := getLimb rem (j + n - 2)
        let qhat := trialQhat u2 u1 u0 vn1 vn2
        let (rem1, borrow) := subMulShiftLoop rem vn j n 0 qhat 0 false
        if borrow then
          let rem2 := addShiftLoop rem1 vn j n 0 false
          go rem2 j (hits + 1)
        else
          go rem1 j hits
    go un (m + 1) 0

/-- Explicit adversarial Knuth Algorithm D add-back triggers (both `u2 < vn1` and `u2 == vn1`,
multiple quotient digits, and arbitrary normalization shifts `s = 0..63`). -/
def testKnuthAddBack (st : Stats) : IO Stats := do
  let half : UInt64 := (1 : UInt64) <<< 63
  let mut st := st
  let triggers : Array (Array UInt64 × Array UInt64) := #[
    -- Classic 3-limb divisor add-back: v = [B-1, 0, 2^63], u = [0, 0, 2^63, 2^63-1]
    (#[0, 0, half, half - 1], #[maxWord64, 0, half]),
    -- Variant with nonzero low limbs
    (#[1, 2, half, half - 1], #[maxWord64, 0, half]),
    (#[maxWord64, maxWord64, half - 1, half - 1], #[maxWord64, 0, half]),
    -- 4-limb divisor add-back
    (#[0, 0, 0, half, half - 1], #[maxWord64, maxWord64, 0, half]),
    (#[0, 0, 0, half, half - 1], #[1, maxWord64, 0, half]),
    -- Multi-step (m = 1, 2, 4) add-back
    (#[0, 0, 0, half, half - 1], #[maxWord64, 0, half]),
    (#[0, 0, half, 0, half, half - 1], #[maxWord64, 0, half]),
    (#[0, 0, 0, 0, 0, half, half - 1], #[maxWord64, 0, half]),
    -- Higher vn1 = 2^63 + 1, 2^64 - 1
    (#[0, 0, half + 1, half], #[maxWord64, 0, half + 1]),
    (#[0, 0, maxWord64, maxWord64 - 1], #[maxWord64, 0, maxWord64]),
    -- u2 == vn1 boundary cases
    (#[0, 0, 0, half], #[maxWord64, 1, half]),
    (#[0, 0, maxWord64, maxWord64], #[maxWord64, maxWord64, maxWord64]),
    (#[0, 0, 0, maxWord64], #[maxWord64, 0, maxWord64])
  ]
  for (u0, v0) in triggers do
    -- Test unshifted and right-shifted by various amounts to exercise normalization shift s = 0..63
    for sh in #[0, 1, 2, 7, 17, 31, 32, 62, 63] do
      let u := shiftRight u0 sh
      let v := shiftRight v0 sh
      let hits := countKnuthAddBack u v
      st := { st with addBackHits := st.addBackHits + hits }
      let (q, rem) := divMod u v
      let nu := toNat u
      let nv := toNat v
      st ← check st (isWF q && isWF rem && toNat q == nu / nv && toNat rem == nu % nv)
        (fun _ => s!"Knuth add-back trigger sh={sh}: u={nu}, v={nv}")
  -- Verify at least 10 add-back events genuinely fired!
  st ← check st (st.addBackHits ≥ 10)
    (fun _ => s!"Expected ≥ 10 Knuth add-back hits, got {st.addBackHits}")
  pure st

/-- Test Karatsuba threshold boundaries: 31, 32, 33, 63, 64, 65, 127, 128, 129, 256, 512, 1000 limbs. -/
def testKaratsubaBoundaries (st : Stats) (r : Rng) : IO (Stats × Rng) := do
  let sizes : Array Nat := #[1, 2, 15, 16, 30, 31, 32, 33, 34, 48, 63, 64, 65, 96, 127, 128, 129, 256]
  let mut st := st
  let mut r := r
  for sa in sizes do
    for sb in #[sa, if sa > 0 then sa - 1 else 0, sa + 1, 31, 32, 33] do
      let (a, r1) := r.nextBigNat sa
      let (b, r2) := r1.nextBigNat sb
      r := r2
      let na := toNat a
      let nb := toNat b
      let mk := mulKaratsuba a b
      st ← check st (isWF mk && toNat mk == na * nb)
        (fun _ => s!"mulKaratsuba sizes ({sa}, {sb})")
      if sa ≤ 65 && sb ≤ 65 then
        let ms := mulSchoolbook a b
        st ← check st (mk == ms)
          (fun _ => s!"mulKaratsuba != mulSchoolbook sizes ({sa}, {sb})")
    let (a, r1) := r.nextBigNat sa
    r := r1
    let na := toNat a
    let sq := sqrKaratsuba a
    st ← check st (isWF sq && toNat sq == na * na)
      (fun _ => s!"sqrKaratsuba size {sa}")
    if sa ≤ 65 then
      let sqs := sqrSchoolbook a
      st ← check st (sq == sqs)
        (fun _ => s!"sqrKaratsuba != sqrSchoolbook size {sa}")
  -- Extra large operands up to 1,000 limbs (64,000 bits)!
  for bigSz in #[300, 512, 750, 1000] do
    let (a, r1) := r.nextBigNat bigSz
    let (b, r2) := r1.nextBigNat bigSz
    let (c, r3) := r2.nextBigNat (bigSz / 2)
    r := r3
    let na := toNat a
    let nb := toNat b
    let nc := toNat c
    let s := add a b
    st ← check st (isWF s && toNat s == na + nb) (fun _ => s!"large add {bigSz}")
    let d := sub a b
    st ← check st (isWF d && toNat d == na - nb) (fun _ => s!"large sub {bigSz}")
    let m := mul a b
    st ← check st (isWF m && toNat m == na * nb) (fun _ => s!"large mul {bigSz}")
    let sq := sqr a
    st ← check st (isWF sq && toNat sq == na * na) (fun _ => s!"large sqr {bigSz}")
    let (q, rem) := divMod a c
    st ← check st (isWF q && isWF rem && toNat q == na / nc && toNat rem == na % nc)
      (fun _ => s!"large divMod {bigSz}/{bigSz / 2}")
    let (q0, rem0) := divMod a #[]
    st ← check st (q0 == #[] && rem0 == a) (fun _ => s!"large divMod zero {bigSz}")
    let dec := toDecimal a
    st ← check st (dec == toString na) (fun _ => s!"large toDecimal {bigSz}")
    st ← check st (ofDecimal dec == some a) (fun _ => s!"large ofDecimal {bigSz}")
  pure (st, r)

/-- High-volume randomized differential fuzz loop (100k+ individual checks). -/
def testRandomFuzz (st : Stats) (r : Rng) : IO (Stats × Rng) := do
  let mut st := st
  let mut r := r
  -- 1. Linear & bitwise ops (5,000 pairs × 14 checks = 70,000 checks)
  for i in [:5000] do
    let maxL := if i % 50 == 0 then 128 else if i % 10 == 0 then 32 else 8
    let (la, r1) := r.nextRange (maxL + 1)
    let (lb, r2) := r1.nextRange (maxL + 1)
    let (a, r3) := r2.nextBigNat la
    let (b, r4) := r3.nextBigNat lb
    r := r4
    st ← checkLinearPair st a b
  -- 2. Shifts (5,000 cases × 2 = 10,000 checks)
  for _ in [:5000] do
    let (la, r1) := r.nextRange 20
    let (a, r2) := r1.nextBigNat la
    let (sh, r3) := r2.nextRange 300
    r := r3
    let na := toNat a
    let sl := shiftLeft a sh
    st ← check st (isWF sl && toNat sl == (na <<< sh)) (fun _ => s!"fuzz shiftLeft {sh}")
    let sr := shiftRight a sh
    st ← check st (isWF sr && toNat sr == (na >>> sh)) (fun _ => s!"fuzz shiftRight {sh}")
  -- 3. Mul & Sqr (5,000 cases × 2 = 10,000 checks)
  for i in [:5000] do
    let maxL := if i % 40 == 0 then 70 else if i % 10 == 0 then 36 else 12
    let (la, r1) := r.nextRange (maxL + 1)
    let (lb, r2) := r1.nextRange (maxL + 1)
    let (a, r3) := r2.nextBigNat la
    let (b, r4) := r3.nextBigNat lb
    r := r4
    let na := toNat a
    let nb := toNat b
    let m := mul a b
    st ← check st (isWF m && toNat m == na * nb) (fun _ => s!"fuzz mul")
    let sq := sqr a
    st ← check st (isWF sq && toNat sq == na * na) (fun _ => s!"fuzz sqr")
  -- 4. Pow (1,500 cases)
  for _ in [:1500] do
    let (la, r1) := r.nextRange 4
    let (a, r2) := r1.nextBigNat la
    let (e, r3) := r2.nextRange 25
    r := r3
    let p := pow a e
    st ← check st (isWF p && toNat p == (toNat a) ^ e) (fun _ => s!"fuzz pow e={e}")
  -- 5. DivMod1 & DivMod (8,000 cases × 2 = 16,000 checks, including exact multiples & q*v - 1)
  for i in [:8000] do
    let maxL := if i % 40 == 0 then 64 else if i % 10 == 0 then 20 else 8
    let (la, r1) := r.nextRange (maxL + 1)
    let (lb, r2) := r1.nextRange (maxL + 1)
    let (a0, r3) := r2.nextBigNat la
    let (b, r4) := r3.nextBigNat lb
    let (d1, r5) := r4.next
    r := r5
    -- Mix direct random dividends with adversarial q*b + r and q*b - 1
    let a :=
      if i % 5 == 0 && b.size > 0 then sub (mul a0 b) one
      else if i % 5 == 1 && b.size > 0 then mul a0 b
      else a0
    let na := toNat a
    let nb := toNat b
    let (q, rem) := divMod a b
    st ← check st (isWF q && isWF rem && toNat q == na / nb && toNat rem == na % nb)
      (fun _ => s!"fuzz divMod la={a.size} lb={b.size}")
    if d1 != 0 then
      let (q1, rem1) := divMod1 a d1
      st ← check st (isWF q1 && toNat q1 == na / d1.toNat && rem1.toNat == na % d1.toNat)
        (fun _ => s!"fuzz divMod1")
    else
      let (q1, rem1) := divMod1 a 0
      st ← check st (q1 == #[] && rem1 == 0) (fun _ => s!"fuzz divMod1 zero")
  -- 6. GCD (3,000 cases, including shared-factor triples g*a, g*b)
  for i in [:3000] do
    let (la, r1) := r.nextRange 8
    let (lb, r2) := r1.nextRange 8
    let (a0, r3) := r2.nextBigNat la
    let (b0, r4) := r3.nextBigNat lb
    let (g0, r5) := r4.nextBigNat (i % 4 + 1)
    r := r5
    let (a, b) := if i % 2 == 0 then (mul a0 g0, mul b0 g0) else (a0, b0)
    let g := gcd a b
    st ← check st (isWF g && toNat g == Nat.gcd (toNat a) (toNat b))
      (fun _ => s!"fuzz gcd")
  -- 7. Decimal conversion (4,000 cases × 3 = 12,000 checks)
  for i in [:4000] do
    let maxL := if i % 40 == 0 then 40 else 10
    let (la, r1) := r.nextRange (maxL + 1)
    let (a, r2) := r1.nextBigNat la
    r := r2
    let na := toNat a
    let chunks := toDecimalChunks a
    st ← check st (ofDecimalChunks chunks == a) (fun _ => s!"fuzz chunks roundtrip")
    let dec := toDecimal a
    st ← check st (dec == toString na) (fun _ => s!"fuzz toDecimal")
    st ← check st (ofDecimal dec == some a) (fun _ => s!"fuzz ofDecimal")
  pure (st, r)

/-- Stage 2 targeted differential suite: Möller–Granlund `invert21`/`divRem21`,
`divExact3`, Toom-3 thresholds `95..1000` limbs + squaring + unbalanced, Lehmer GCD
multi-step + huge-quotient fallback + 512-limb shared factors, `divQuick1`, and in-place COW ops. -/
def testStage2 (st : Stats) (r : Rng) : IO (Stats × Rng) := do
  let mut st := st
  let mut r := r
  let half : UInt64 := (1 : UInt64) <<< 63
  -- 1. Möller–Granlund invert21 & divRem21 edge cases (adversarial + 5,000 random)
  let edgeDivisors : Array UInt64 := #[
    half, half + 1, half + 2, half + 3,
    half + ((1 : UInt64) <<< 32), half + ((1 : UInt64) <<< 62),
    ((0xAAAAAAAA : UInt64) <<< 32) ||| (0xAAAAAAAA : UInt64),
    ((0xCCCCCCCC : UInt64) <<< 32) ||| (0xCCCCCCCC : UInt64),
    ((0xF0000000 : UInt64) <<< 32) ||| (0x00000001 : UInt64),
    maxWord64 - 2, maxWord64 - 1, maxWord64
  ]
  for d in edgeDivisors do
    if hd : 2 ^ 63 ≤ d.toNat then
      let v := invert21 d hd
      let expectedV := (2 ^ 128 - 1) / d.toNat - 2 ^ 64
      st ← check st (v.toNat == expectedV)
        (fun _ => s!"invert21 edge d={d}: got {v}, expected {expectedV}")
      let u1s : Array UInt64 := #[0, 1, 2, d / 2, d - 3, d - 2, d - 1]
      let u0s : Array UInt64 := #[0, 1, 2, half - 1, half, d - 1, d, maxWord64 - 1, maxWord64]
      for u1 in u1s do
        for u0 in u0s do
          if hu1 : u1 < d then
            let (q, rem) := divRem21 u1 u0 d v
            let (qw, remW) := divWide64 u1 u0 d hu1
            st ← check st (q == qw && rem == remW)
              (fun _ => s!"divRem21 edge u1={u1} u0={u0} d={d}: got ({q},{rem}), exp ({qw},{remW})")
            -- Track Step 5 (r > q0) & Step 6 (r ≥ d) coverage
            let (pLo, pHi) := mulWide64 v u1
            let (q0, c0) := addCarry64 pLo u0 false
            let (q1i, _) := addCarry64 pHi u1 c0
            let q1 := q1i + 1
            let r0 := u0 - q1 * d
            let r1 := if r0 > q0 then r0 + d else r0
            if r0 > q0 then st := { st with divRem21Step5Hits := st.divRem21Step5Hits + 1 }
            if r1 ≥ d then st := { st with divRem21Step6Hits := st.divRem21Step6Hits + 1 }
  for _ in [:5000] do
    let (dRaw, r1) := r.next
    let (u1Raw, r2) := r1.next
    let (u0, r3) := r2.next
    r := r3
    let d := dRaw ||| half
    if hd : 2 ^ 63 ≤ d.toNat then
      let v := invert21 d hd
      let u1 := u1Raw % d
      if hu1 : u1 < d then
        let (q, rem) := divRem21 u1 u0 d v
        let (qw, remW) := divWide64 u1 u0 d hu1
        st ← check st (q == qw && rem == remW)
          (fun _ => s!"divRem21 fuzz u1={u1} u0={u0} d={d}")
  st ← check st (st.divRem21Step5Hits > 0 && st.divRem21Step6Hits > 0)
    (fun _ => s!"divRem21 coverage: step5={st.divRem21Step5Hits} step6={st.divRem21Step6Hits}")

  -- 2. divExact3 (edge cases + 1,000 random multiples of 3 up to 150 limbs)
  let exact3Edges : Array (Array UInt64) := #[
    #[], #[0], #[3], #[6], #[2, 1], #[1, 2], #[1, 1, 1],
    #[maxWord64, maxWord64], #[maxWord64, maxWord64, maxWord64, maxWord64]
  ]
  for x in exact3Edges do
    let x3 := mulAdd1 x 3 0
    let q := divExact3 x3
    st ← check st (isWF q && q == normalize x)
      (fun _ => s!"divExact3 edge {toNat x}")
  for i in [:1000] do
    let (sz, r1) := r.nextRange (if i % 10 == 0 then 150 else 20)
    let (x, r2) := r1.nextBigNat sz
    r := r2
    let x3 := mulAdd1 x 3 0
    let q := divExact3 x3
    st ← check st (isWF q && q == x)
      (fun _ => s!"divExact3 fuzz sz={sz}")

  -- 3. Toom-3 thresholds (95..1000 limbs, balanced + unbalanced + squaring + mul a a fast path)
  let toomSizes : Array Nat := #[
    94, 95, 96, 97, 98, 99, 100, 127, 128, 129, 150, 192, 200, 255, 256, 257, 300, 384, 512, 750, 1000
  ]
  for sa in toomSizes do
    let sbList := if sa ≤ 260 then #[sa, sa - 1, sa + 1, sa / 2, (2 * sa) / 3] else #[sa, sa / 2]
    for sb in sbList do
      let (a, r1) := r.nextBigNat sa
      let (b, r2) := r1.nextBigNat sb
      r := r2
      let na := toNat a
      let nb := toNat b
      let mt := mulToom3 a b
      st ← check st (isWF mt && toNat mt == na * nb)
        (fun _ => s!"mulToom3 ({sa}, {sb})")
      if sa ≤ 160 && sb ≤ 160 then
        let mk := mulKaratsuba a b
        st ← check st (mt == mk)
          (fun _ => s!"mulToom3 != mulKaratsuba ({sa}, {sb})")
    let (a, r1) := r.nextBigNat sa
    r := r1
    let na := toNat a
    let sqt := sqrToom3 a
    st ← check st (isWF sqt && toNat sqt == na * na)
      (fun _ => s!"sqrToom3 {sa}")
    let maa := mul a a
    st ← check st (maa == sqt)
      (fun _ => s!"mul a a != sqrToom3 a ({sa})")

  -- 4. Lehmer GCD: multi-step, Fibonacci-like, huge-quotient fallback, 512-limb shared factors
  -- 4a. Explicit Fibonacci-like pair (128 limbs) exercising maximum Lehmer steps
  let mut fa := one
  let mut fb := ofUInt64 2
  for _ in [:2000] do
    let fc := add fa fb
    fa := fb
    fb := fc
  match lehmerStep fb fa with
  | some _ => st := { st with lehmerHits := st.lehmerHits + 1 }
  | none => st := { st with lehmerFallbacks := st.lehmerFallbacks + 1 }
  let gFib := gcd fb fa
  st ← check st (isWF gFib && gFib == one) (fun _ => s!"Lehmer Fib gcd != 1")
  -- 4b. Huge-quotient fallback trigger (a = (2^192 + 1) * b + r)
  let (bSmall, r1) := r.nextBigNat 8
  let (rSmall, r2) := r1.nextBigNat 4
  r := r2
  let bigQ := add (shiftLimbs one 3) one
  let aHuge := add (mul bigQ bSmall) rSmall
  match lehmerStep aHuge bSmall with
  | some _ => st := { st with lehmerHits := st.lehmerHits + 1 }
  | none => st := { st with lehmerFallbacks := st.lehmerFallbacks + 1 }
  let gHuge := gcd aHuge bSmall
  st ← check st (isWF gHuge && toNat gHuge == Nat.gcd (toNat aHuge) (toNat bSmall))
    (fun _ => s!"Lehmer huge-quotient fallback")
  -- 4c. Shared-factor large GCDs (64, 128, 256, 512 limbs!)
  for gSz in #[64, 128, 256, 512] do
    let (a0, r1) := r.nextBigNat (gSz / 2)
    let (b0, r2) := r1.nextBigNat (gSz / 2)
    let (g0, r3) := r2.nextBigNat (gSz / 2)
    r := r3
    let a := mul a0 g0
    let b := mul b0 g0
    let (hi, lo) := if blt a b then (b, a) else (a, b)
    if hi.size ≥ 2 && hi.size - lo.size ≤ 1 then
      match lehmerStep hi lo with
      | some _ => st := { st with lehmerHits := st.lehmerHits + 1 }
      | none => st := { st with lehmerFallbacks := st.lehmerFallbacks + 1 }
    let g := gcd a b
    st ← check st (isWF g && toNat g == Nat.gcd (toNat a) (toNat b))
      (fun _ => s!"Lehmer large shared-factor {gSz} limbs")
  -- 4d. 1,500 random multi-limb Lehmer GCD pairs (2..48 limbs)
  for i in [:1500] do
    let maxL := if i % 25 == 0 then 48 else 12
    let (la, r1) := r.nextRange maxL
    let (lb, r2) := r1.nextRange maxL
    let (a0, r3) := r2.nextBigNat (la + 2)
    let (b0, r4) := r3.nextBigNat (lb + 2)
    r := r4
    let (hi, lo) := if blt a0 b0 then (b0, a0) else (a0, b0)
    if hi.size ≥ 2 && hi.size - lo.size ≤ 1 then
      match lehmerStep hi lo with
      | some _ => st := { st with lehmerHits := st.lehmerHits + 1 }
      | none => st := { st with lehmerFallbacks := st.lehmerFallbacks + 1 }
    let g := gcd a0 b0
    st ← check st (isWF g && toNat g == Nat.gcd (toNat a0) (toNat b0))
      (fun _ => s!"Lehmer fuzz gcd i={i}")
  st ← check st (st.lehmerHits ≥ 50 && st.lehmerFallbacks ≥ 1)
    (fun _ => s!"Lehmer coverage: hits={st.lehmerHits} fallbacks={st.lehmerFallbacks}")

  -- 5. divQuick1, BigNat.div, and Stage 2 in-place COW ops (2,000 cases)
  for i in [:2000] do
    let maxL := if i % 40 == 0 then 120 else 16
    let (lv, r1) := r.nextRange maxL
    let (v, r2) := r1.nextBigNat (lv + 2)
    let (qSmall, r3) := r2.nextRange 20
    let (remRaw, r4) := r3.nextBigNat (lv + 2)
    r := r4
    let rem := if blt remRaw v then remRaw else mod remRaw v
    let u := add (mulAdd1 v (UInt64.ofNat qSmall) 0) rem
    let nu := toNat u
    let nv := toNat v
    let qDiv := IxCC.BigNat.div u v
    st ← check st (isWF qDiv && toNat qDiv == nu / nv)
      (fun _ => s!"BigNat.div small-q i={i}")
    match divQuick1 u v with
    | some qq =>
      st ← check st (isWF qq && toNat qq == nu / nv)
        (fun _ => s!"divQuick1 mismatch i={i}")
    | none => pure ()
    -- Exercise in-place COW ops on freshly copied accumulators
    let (off, r5) := r.nextRange 5
    let (mWord, r6) := r5.next
    r := r6
    let accAdd := normalize (addAtInPlace (copyIntoZeros u (u.size + off + v.size)) v off)
    st ← check st (isWF accAdd && toNat accAdd == nu + nv * (2 ^ 64) ^ off)
      (fun _ => s!"addAtInPlace i={i}")
    let accMul := normalize (addMul1InPlace (copyIntoZeros u (u.size + v.size + 1)) v mWord)
    st ← check st (isWF accMul && toNat accMul == nu + mWord.toNat * nv)
      (fun _ => s!"addMul1InPlace i={i}")
    let (subRes, borrowW) := subMul1InPlace (copyIntoZeros accMul accMul.size) v mWord
    st ← check st (borrowW == 0 && normalize subRes == u)
      (fun _ => s!"subMul1InPlace roundtrip i={i}")
    let shl1 := shiftLeft1 u
    let shr1 := shiftRight1 shl1
    st ← check st (isWF shl1 && toNat shl1 == nu * 2 && shr1 == u)
      (fun _ => s!"shiftLeft1/shiftRight1 roundtrip i={i}")
  pure (st, r)

/-- One pair through every binary entry over `Nat` (`IxCC.BigNat.NatEntry`), against Lean's
own `Nat`. -/
def checkNatEntryPair (st : Stats) (a b : Nat) : IO Stats := do
  let mut st := st
  st ← check st (NatEntry.add a b == a + b) (fun _ => s!"NatEntry.add {a} {b}")
  st ← check st (NatEntry.sub a b == a - b) (fun _ => s!"NatEntry.sub {a} {b}")
  st ← check st (NatEntry.mul a b == a * b) (fun _ => s!"NatEntry.mul {a} {b}")
  st ← check st (NatEntry.div a b == a / b) (fun _ => s!"NatEntry.div {a} {b}")
  st ← check st (NatEntry.mod a b == a % b) (fun _ => s!"NatEntry.mod {a} {b}")
  st ← check st (NatEntry.gcd a b == Nat.gcd a b) (fun _ => s!"NatEntry.gcd {a} {b}")
  st ← check st (NatEntry.land a b == (a &&& b)) (fun _ => s!"NatEntry.land {a} {b}")
  st ← check st (NatEntry.lor a b == (a ||| b)) (fun _ => s!"NatEntry.lor {a} {b}")
  st ← check st (NatEntry.xor a b == (a ^^^ b)) (fun _ => s!"NatEntry.xor {a} {b}")
  st ← check st (NatEntry.cmp a b == compare a b) (fun _ => s!"NatEntry.cmp {a} {b}")
  st ← check st (NatEntry.beq a b == (a == b)) (fun _ => s!"NatEntry.beq {a} {b}")
  st ← check st (NatEntry.ble a b == decide (a ≤ b)) (fun _ => s!"NatEntry.ble {a} {b}")
  st ← check st (NatEntry.blt a b == decide (a < b)) (fun _ => s!"NatEntry.blt {a} {b}")
  pure st

/-- One natural through the two representation primitives (`IxCC.NatRep`), the unary entries
and the canonical equation of `toLimbs`. -/
def checkNatRep (st : Stats) (n : Nat) : IO Stats := do
  let mut st := st
  let ls := IxCC.NatRep.toLimbs n
  st ← check st (isWF ls && ls == ofNat n) (fun _ => s!"toLimbs canonical {n}")
  st ← check st (IxCC.NatRep.ofLimbs ls == n) (fun _ => s!"ofLimbs (toLimbs {n})")
  st ← check st (IxCC.NatRep.ofLimbs ls == toNat ls) (fun _ => s!"ofLimbs = toNat {n}")
  -- a limb array that is not canonical denotes the same natural, and comes back canonical
  let padded := (ls.push 0).push 0
  st ← check st (IxCC.NatRep.ofLimbs padded == n) (fun _ => s!"ofLimbs padded {n}")
  st ← check st (IxCC.NatRep.toLimbs (IxCC.NatRep.ofLimbs padded) == ls)
    (fun _ => s!"toLimbs (ofLimbs padded) {n}")
  -- the canonical equation: the low limb, then the limbs of the quotient
  let expected : List UInt64 :=
    if n == 0 then [] else UInt64.ofNat (n % 2 ^ 64) :: (IxCC.NatRep.toLimbs (n / 2 ^ 64)).toList
  st ← check st (ls.toList == expected) (fun _ => s!"toLimbs equation {n}")
  st ← check st (NatEntry.pred n == n - 1) (fun _ => s!"NatEntry.pred {n}")
  st ← check st (NatEntry.log2 n == Nat.log2 n) (fun _ => s!"NatEntry.log2 {n}")
  let dec := NatEntry.toDecimal n
  st ← check st (dec == toString n) (fun _ => s!"NatEntry.toDecimal {n}: got {dec}")
  st ← check st (NatEntry.ofDecimal dec == some n) (fun _ => s!"NatEntry.ofDecimal {n}")
  pure st

/-- The entries over `Nat` and the representation primitives: boundary values, then random
operands up to 200 limbs (past the Karatsuba and Toom-3 thresholds). -/
def testNatEntry (st : Stats) (r : Rng) : IO (Stats × Rng) := do
  let mut st := st
  let mut r := r
  let vals : Array Nat := #[
    0, 1, 2, 3, 7, 9, 10, 63, 64, 65,
    2 ^ 32 - 1, 2 ^ 32,
    2 ^ 63 - 2, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1,
    10 ^ 19 - 1, 10 ^ 19, 10 ^ 19 + 1,
    2 ^ 64 - 2, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1,
    2 ^ 127 - 1, 2 ^ 127, 2 ^ 128 - 1, 2 ^ 128, 2 ^ 128 + 1,
    10 ^ 38, 2 ^ 192, 2 ^ 256 - 1, 2 ^ 256
  ]
  for a in vals do
    st ← checkNatRep st a
    for b in vals do
      st ← checkNatEntryPair st a b
    for sh in #[0, 1, 2, 31, 32, 63, 64, 65, 127, 128, 129, 255, 256, 512] do
      st ← check st (NatEntry.shiftLeft a sh == a <<< sh) (fun _ => s!"NatEntry.shiftLeft {a} {sh}")
      st ← check st (NatEntry.shiftRight a sh == a >>> sh)
        (fun _ => s!"NatEntry.shiftRight {a} {sh}")
    -- a count that is itself beyond the tagged range: the result is exactly `0`
    st ← check st (NatEntry.shiftRight a (2 ^ 64 + 3) == 0)
      (fun _ => s!"NatEntry.shiftRight {a} by 2^64+3")
    for e in #[0, 1, 2, 3, 5, 17] do
      st ← check st (NatEntry.pow a e == a ^ e) (fun _ => s!"NatEntry.pow {a} {e}")
  -- exponents beyond the tagged range, on the bases whose power is small
  st ← check st (NatEntry.pow 0 (2 ^ 64) == 0) (fun _ => "NatEntry.pow 0 (2^64)")
  st ← check st (NatEntry.pow 1 (2 ^ 64) == 1) (fun _ => "NatEntry.pow 1 (2^64)")
  for bad in #["", " ", "12a3", "-5", "+1", "12 34", "1_000"] do
    st ← check st (NatEntry.ofDecimal bad == none) (fun _ => s!"NatEntry.ofDecimal bad '{bad}'")
  st ← check st (NatEntry.ofDecimal "000123" == some 123) (fun _ => "NatEntry.ofDecimal 000123")
  for i in [:1500] do
    let maxL := if i % 100 == 0 then 200 else if i % 10 == 0 then 40 else 8
    let (la, r1) := r.nextRange (maxL + 1)
    let (lb, r2) := r1.nextRange (maxL + 1)
    let (xa, r3) := r2.nextBigNat la
    let (xb, r4) := r3.nextBigNat lb
    let (sh, r5) := r4.nextRange 300
    let (e, r6) := r5.nextRange 6
    r := r6
    let a := toNat xa
    let b := toNat xb
    st ← checkNatRep st a
    st ← checkNatEntryPair st a b
    st ← check st (NatEntry.shiftLeft a sh == a <<< sh) (fun _ => s!"fuzz NatEntry.shiftLeft {sh}")
    st ← check st (NatEntry.shiftRight a sh == a >>> sh) (fun _ => s!"fuzz NatEntry.shiftRight {sh}")
    if la ≤ 8 then
      st ← check st (NatEntry.pow a e == a ^ e) (fun _ => s!"fuzz NatEntry.pow e={e}")
  pure (st, r)

def runAll : IO Unit := do
  let mut st : Stats := {}
  let mut r : Rng := { state := 0x123456789abcdef0 }
  let (st1, r1) ← testLimbOps st r 2000
  st := st1; r := r1
  IO.println s!"[1/7] LimbOps: {st.total} checks, {st.failures} failures"
  st ← testBoundaries st
  IO.println s!"[2/7] Boundaries: {st.total} checks, {st.failures} failures"
  st ← testKnuthAddBack st
  IO.println s!"[3/7] Knuth Add-Back: {st.total} checks, {st.failures} failures, {st.addBackHits} add-back hits"
  let (st4, r4) ← testKaratsubaBoundaries st r
  st := st4; r := r4
  IO.println s!"[4/7] Karatsuba & 1000-limb: {st.total} checks, {st.failures} failures"
  let (st5, r5) ← testRandomFuzz st r
  st := st5; r := r5
  IO.println s!"[5/7] Random Fuzz: {st.total} checks, {st.failures} failures"
  let (st6, r6) ← testStage2 st r
  st := st6; r := r6
  IO.println s!"[6/7] Stage 2 (InvDiv/Toom3/Lehmer/COW): {st.total} checks, {st.failures} failures (lehmerHits={st.lehmerHits}, fallbacks={st.lehmerFallbacks}, divRem21S5={st.divRem21Step5Hits}, divRem21S6={st.divRem21Step6Hits})"
  let (st7, _) ← testNatEntry st r
  st := st7
  IO.println s!"[7/7] Entries over Nat and toLimbs/ofLimbs: {st.total} checks, {st.failures} failures"
  if st.failures != 0 then
    throw (IO.userError s!"BigNat DiffTest FAILED with {st.failures} failures out of {st.total} checks")
  IO.println s!"BigNat DiffTest PASS: {st.total} checks, 0 failures ({st.addBackHits} Knuth D add-back triggers, {st.lehmerHits} Lehmer hits, {st.lehmerFallbacks} fallbacks)"

end IxCCTests.BigNat.DiffTest

def main : IO Unit := IxCCTests.BigNat.DiffTest.runAll
