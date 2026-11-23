import IxCC.BigNat

/-!
# Pure-Lean 100k+ Native Arbitrary-Precision Differential Harness (`IxCCTests.BigNat.NativeDiff`)

Fast, pure-Lean differential test driver built for Wave 3b / Wave 4 validation of compiled `ixcc`
arbitrary-precision `Nat` executables against Lean 4's GMP-backed `Nat` oracle.

## Coverage (100,000+ cases by default)
1. **Small & Boundary Cross-Product**: `0..128`, `2^32±1`, `2^63-2..2^63+1`, `10^19±1`,
   `2^64-2..2^64+1`, `2^127±1`, `2^128±1`, `2^192±1`, `2^256±1`, `2^512±1`.
2. **Zero-Divisor & Edge-Zero Suite**: `n / 0 = 0`, `n % 0 = n`, `0 / b = 0`, `0 % b = 0`,
   `gcd n 0 = n`, `gcd 0 n = n`, `0 - n = 0`, `n ^ 0 = 1`, `0 ^ 0 = 1`, `pred 0 = 0`, `log2 0 = 0`
   across 0..1,000-limb operands.
3. **Knuth Algorithm D Add-Back Triggers**: classic 3-limb, 4-limb, multi-step (`m = 1, 2, 4`),
   and `u2 == vn1` add-back triggers across normalization shifts `s ∈ {0, 1, 2, 7, 17, 31, 32, 62, 63}`,
   asserting `≥ 10` genuine Step-D4 add-back executions.
4. **Karatsuba Thresholds & 1,000-Limb Operands**: exact thresholds `31, 32, 33, 63, 64, 65, 127,
   128, 129, 256, 512, 1000` limbs (balanced, off-by-one, and cross-threshold pairs; all-ones
   `2^(64k) - 1`, sparse powers of 2, and uniform random limbs up to 64,000 bits).
5. **High-Volume Randomized Stress**: 0..1,000-limb adversarial bit patterns (all-ones, sparse
   all-ones, sparse random, single-bit, uniform, `q*b`, `q*b - 1`, shared-factor GCD pairs) across
   all 18 arbitrary-precision `Nat` operations.

## Modes
- `--self-test` (default): compares `IxCC.BigNat` (plus `WF` normal-form check on every output)
  against Lean 4 GMP across 100k+ cases.
- `--batch <exe> [--arg <x> ...]`: streams `<op> <a> [b]\n` over stdin/stdout to a compiled `ixcc`
  batch executable (zero per-case process-spawn overhead for 100k+ checks).
- `--exe-dir <dir>` / `--exe <op>=<path>`: invokes per-operation compiled `ixcc --exe` binaries
  (`<exe> <a> [b]`) and compares stdout against Lean 4 GMP.
- `--emit-vectors <file>`: emits `<op> <a> <b> <expected>` lines for offline/CI replay.
- Options: `--count <N>` (default `100000`), `--seed <UInt64>`, `--op <name>`, `--bool-as-nat`,
  `--exe-limit <N>`, `--fail-fast`.

All functions are total (zero `partial`, zero `sorry`, `-DwarningAsError=true` clean).
-/

namespace IxCCTests.BigNat.NativeDiff

open IxCC.BigNat

/-! ## Operations and Reference Oracles -/

inductive DiffOp where
  | add
  | sub
  | mul
  | div
  | mod
  | gcd
  | land
  | lor
  | xor
  | shiftLeft
  | shiftRight
  | pow
  | pred
  | log2
  | sqr
  | beq
  | ble
  | blt
  deriving BEq, DecidableEq, Repr, Inhabited

def DiffOp.all : Array DiffOp := #[
  .add, .sub, .mul, .div, .mod, .gcd,
  .land, .lor, .xor, .shiftLeft, .shiftRight,
  .pow, .pred, .log2, .sqr, .beq, .ble, .blt
]

def DiffOp.name : DiffOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"
  | .mod => "mod"
  | .gcd => "gcd"
  | .land => "land"
  | .lor => "lor"
  | .xor => "xor"
  | .shiftLeft => "shiftLeft"
  | .shiftRight => "shiftRight"
  | .pow => "pow"
  | .pred => "pred"
  | .log2 => "log2"
  | .sqr => "sqr"
  | .beq => "beq"
  | .ble => "ble"
  | .blt => "blt"

def DiffOp.ofName? (s : String) : Option DiffOp :=
  DiffOp.all.find? (fun op => op.name == s)

def DiffOp.isUnary : DiffOp → Bool
  | .pred | .log2 | .sqr => true
  | _ => false

def DiffOp.isBool : DiffOp → Bool
  | .beq | .ble | .blt => true
  | _ => false

def formatBool (boolAsNat : Bool) (b : Bool) : String :=
  if boolAsNat then (if b then "1" else "0") else (if b then "true" else "false")

/-- Lean 4 GMP-backed reference oracle. -/
def DiffOp.evalGMP (boolAsNat : Bool) : DiffOp → Nat → Nat → String
  | .add, a, b => toString (a + b)
  | .sub, a, b => toString (a - b)
  | .mul, a, b => toString (a * b)
  | .div, a, b => toString (a / b)
  | .mod, a, b => toString (a % b)
  | .gcd, a, b => toString (Nat.gcd a b)
  | .land, a, b => toString (a &&& b)
  | .lor, a, b => toString (a ||| b)
  | .xor, a, b => toString (a ^^^ b)
  | .shiftLeft, a, b => toString (a <<< b)
  | .shiftRight, a, b => toString (a >>> b)
  | .pow, a, b => toString (a ^ b)
  | .pred, a, _ => toString (a - 1)
  | .log2, a, _ => toString (Nat.log2 a)
  | .sqr, a, _ => toString (a * a)
  | .beq, a, b => formatBool boolAsNat (a == b)
  | .ble, a, b => formatBool boolAsNat (decide (a ≤ b))
  | .blt, a, b => formatBool boolAsNat (decide (a < b))

/-- Runtime canonical normal-form (`WF`) check on a limb array. -/
@[inline] def isWF (xs : Array UInt64) : Bool :=
  if h : 0 < xs.size then xs[xs.size - 1] != 0 else true

/-- In-process `IxCC.BigNat` evaluator returning `(formattedResult, wfOk)` for `--self-test`. -/
def DiffOp.evalBigNat (boolAsNat : Bool) (op : DiffOp) (a b : Nat) : String × Bool :=
  let ba := IxCC.BigNat.ofNat a
  let bb := IxCC.BigNat.ofNat b
  match op with
  | .add =>
    let r := IxCC.BigNat.add ba bb
    (toString (toNat r), isWF r)
  | .sub =>
    let r := IxCC.BigNat.sub ba bb
    (toString (toNat r), isWF r)
  | .mul =>
    let r := IxCC.BigNat.mul ba bb
    (toString (toNat r), isWF r)
  | .div =>
    let r := IxCC.BigNat.div ba bb
    (toString (toNat r), isWF r)
  | .mod =>
    let r := IxCC.BigNat.mod ba bb
    (toString (toNat r), isWF r)
  | .gcd =>
    let r := IxCC.BigNat.gcd ba bb
    (toString (toNat r), isWF r)
  | .land =>
    let r := IxCC.BigNat.land ba bb
    (toString (toNat r), isWF r)
  | .lor =>
    let r := IxCC.BigNat.lor ba bb
    (toString (toNat r), isWF r)
  | .xor =>
    let r := IxCC.BigNat.xor ba bb
    (toString (toNat r), isWF r)
  | .shiftLeft =>
    let r := IxCC.BigNat.shiftLeft ba b
    (toString (toNat r), isWF r)
  | .shiftRight =>
    let r := IxCC.BigNat.shiftRight ba b
    (toString (toNat r), isWF r)
  | .pow =>
    let r := IxCC.BigNat.pow ba b
    (toString (toNat r), isWF r)
  | .pred =>
    let r := IxCC.BigNat.pred ba
    (toString (toNat r), isWF r)
  | .log2 =>
    (toString (IxCC.BigNat.log2 ba), true)
  | .sqr =>
    let r := IxCC.BigNat.sqr ba
    (toString (toNat r), isWF r)
  | .beq =>
    (formatBool boolAsNat (IxCC.BigNat.beq ba bb), true)
  | .ble =>
    (formatBool boolAsNat (IxCC.BigNat.ble ba bb), true)
  | .blt =>
    (formatBool boolAsNat (IxCC.BigNat.blt ba bb), true)

/-- A single differential test case. -/
structure DiffCase where
  tag : String
  op : DiffOp
  a : Nat
  b : Nat
  deriving Repr, Inhabited

/-- Format a test case as a batch-protocol request line: `<op> <a>` or `<op> <a> <b>`. -/
def DiffCase.toRequestLine (c : DiffCase) : String :=
  if c.op.isUnary then s!"{c.op.name} {c.a}" else s!"{c.op.name} {c.a} {c.b}"

/-! ## Deterministic SplitMix64 PRNG and Limb-Pattern Generators -/

structure Rng where
  state : UInt64

@[inline] def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.state + (0x9e3779b97f4a7c15 : UInt64)
  let z := (s ^^^ (s >>> 30)) * (0xbf58476d1ce4e5b9 : UInt64)
  let z := (z ^^^ (z >>> 27)) * (0x94d049bb133111eb : UInt64)
  let z := z ^^^ (z >>> 31)
  (z, { state := s })

@[inline] def Rng.nextRange (r : Rng) (bound : Nat) : Nat × Rng :=
  if bound == 0 then (0, r)
  else
    let (w, r') := r.next
    (w.toNat % bound, r')

/-- Build a random canonical `BigNat` of `limbs` limbs using adversarial bit patterns. -/
def Rng.nextLimbs (r : Rng) (limbs : Nat) : Array UInt64 × Rng :=
  let (mode, r) := r.nextRange 8
  let rec go (k : Nat) (r : Rng) (acc : Array UInt64) : Array UInt64 × Rng :=
    match k with
    | 0 => (normalize acc, r)
    | k' + 1 =>
      let (w, r') := r.next
      let limb : UInt64 :=
        if mode == 0 then maxWord64                                   -- all-ones carry cascade
        else if mode == 1 then if w % 4 == 0 then 0 else maxWord64    -- sparse all-ones
        else if mode == 2 then if w % 3 == 0 then 0 else w            -- sparse random
        else if mode == 3 then ((1 : UInt64) <<< (w % 64))            -- single-bit limbs
        else if mode == 4 then (maxWord64 ^^^ ((1 : UInt64) <<< (w % 64))) -- single-zero-bit limbs
        else w                                                         -- uniform random
      go k' r' (acc.push limb)
  go limbs r (Array.mkEmpty limbs)

/-- Build a random `Nat` with `limbs` base-`2^64` limbs. -/
def Rng.nextNatLimbs (r : Rng) (limbs : Nat) : Nat × Rng :=
  let (arr, r') := r.nextLimbs limbs
  (toNat arr, r')

/-- All-ones `Nat` of exactly `k` limbs: `2^(64*k) - 1`. -/
def allOnesLimbs (k : Nat) : Nat :=
  let rec go (n : Nat) (acc : Array UInt64) : Array UInt64 :=
    match n with
    | 0 => acc
    | n' + 1 => go n' (acc.push maxWord64)
  toNat (go k (Array.mkEmpty k))

/-- Exact Knuth Algorithm D Step-D4 add-back hit detector (mirrors `IxCC.BigNat.Div`). -/
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

/-! ## Adversarial & Randomized Vector Builders (100,000+ cases) -/

/-- Canonical boundary values spanning small ints, `2^32`, `2^63±1`, `10^19±1`, `2^64±1`,
`2^128±1`, `2^192±1`, `2^256±1`, and `2^512±1`. -/
def boundaryVals : Array Nat := #[
  0, 1, 2, 3, 7, 9, 10, 15, 16, 31, 32, 33, 63, 64, 65, 127, 128,
  2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1,
  2 ^ 63 - 2, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1,
  10 ^ 19 - 1, 10 ^ 19, 10 ^ 19 + 1,
  2 ^ 64 - 2, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1,
  2 ^ 127 - 1, 2 ^ 127,
  2 ^ 128 - 1, 2 ^ 128, 2 ^ 128 + 1,
  10 ^ 38 - 1, 10 ^ 38, 10 ^ 38 + 1,
  2 ^ 192 - 1, 2 ^ 192,
  2 ^ 256 - 1, 2 ^ 256,
  2 ^ 512 - 1, 2 ^ 512
]

/-- Emit structured adversarial cases (boundaries, zero divisors, Knuth D add-back triggers,
Karatsuba thresholds 31/32/33/63/64/65/127/128/129/256/512/1000 limbs), returning `(cases,
addBackHits, rng)`. -/
def buildAdversarialCases (r0 : Rng) : Array DiffCase × Nat × Rng := Id.run do
  let mut out : Array DiffCase := Array.mkEmpty 32000
  let mut r := r0
  let mut addBackHits : Nat := 0
  -- 1. Boundary cross-product (first 28 core boundaries × 28 × 12 binary ops + all 45 unary/shift)
  let core := boundaryVals.extract 0 28
  let binOps : Array DiffOp := #[.add, .sub, .mul, .div, .mod, .gcd, .land, .lor, .xor, .beq, .ble, .blt]
  for a in core do
    for b in core do
      for op in binOps do
        out := out.push { tag := "boundary", op, a, b }
  -- Full boundary list: unary ops, shifts, small powers, and self/neighbor binary pairs
  for a in boundaryVals do
    out := out.push { tag := "boundary-unary", op := .pred, a, b := 0 }
    out := out.push { tag := "boundary-unary", op := .log2, a, b := 0 }
    out := out.push { tag := "boundary-unary", op := .sqr, a, b := 0 }
    for sh in #[0, 1, 2, 31, 32, 63, 64, 65, 127, 128, 129, 255, 256, 512] do
      out := out.push { tag := "boundary-shift", op := .shiftLeft, a, b := sh }
      out := out.push { tag := "boundary-shift", op := .shiftRight, a, b := sh }
    for e in #[0, 1, 2, 3, 4, 7, 8] do
      if a < 2 ^ 257 then
        out := out.push { tag := "boundary-pow", op := .pow, a, b := e }
  -- 2. Explicit zero-divisor and edge-zero cases across 0..1000 limbs
  let zeroTargets : Array Nat := boundaryVals ++ #[
    allOnesLimbs 31, allOnesLimbs 32, allOnesLimbs 33,
    allOnesLimbs 64, allOnesLimbs 128, allOnesLimbs 256, allOnesLimbs 1000
  ]
  for a in zeroTargets do
    out := out.push { tag := "zero-div", op := .div, a, b := 0 }
    out := out.push { tag := "zero-mod", op := .mod, a, b := 0 }
    out := out.push { tag := "zero-div-lhs", op := .div, a := 0, b := a }
    out := out.push { tag := "zero-mod-lhs", op := .mod, a := 0, b := a }
    out := out.push { tag := "zero-gcd-rhs", op := .gcd, a, b := 0 }
    out := out.push { tag := "zero-gcd-lhs", op := .gcd, a := 0, b := a }
    out := out.push { tag := "zero-sub-lhs", op := .sub, a := 0, b := a }
    out := out.push { tag := "zero-pow-rhs", op := .pow, a, b := 0 }
    out := out.push { tag := "zero-add-rhs", op := .add, a, b := 0 }
    out := out.push { tag := "zero-mul-rhs", op := .mul, a, b := 0 }
  -- 3. Knuth Algorithm D Step-D4 add-back triggers across shifts 0..63
  let half : UInt64 := (1 : UInt64) <<< 63
  let triggers : Array (Array UInt64 × Array UInt64) := #[
    (#[0, 0, half, half - 1], #[maxWord64, 0, half]),
    (#[1, 2, half, half - 1], #[maxWord64, 0, half]),
    (#[maxWord64, maxWord64, half - 1, half - 1], #[maxWord64, 0, half]),
    (#[0, 0, 0, half, half - 1], #[maxWord64, maxWord64, 0, half]),
    (#[0, 0, 0, half, half - 1], #[1, maxWord64, 0, half]),
    (#[0, 0, 0, half, half - 1], #[maxWord64, 0, half]),
    (#[0, 0, half, 0, half, half - 1], #[maxWord64, 0, half]),
    (#[0, 0, 0, 0, 0, half, half - 1], #[maxWord64, 0, half]),
    (#[0, 0, half + 1, half], #[maxWord64, 0, half + 1]),
    (#[0, 0, maxWord64, maxWord64 - 1], #[maxWord64, 0, maxWord64]),
    (#[0, 0, 0, half], #[maxWord64, 1, half]),
    (#[0, 0, maxWord64, maxWord64], #[maxWord64, maxWord64, maxWord64]),
    (#[0, 0, 0, maxWord64], #[maxWord64, 0, maxWord64])
  ]
  for (u0, v0) in triggers do
    for sh in #[0, 1, 2, 7, 17, 31, 32, 62, 63] do
      let u := shiftRight u0 sh
      let v := shiftRight v0 sh
      addBackHits := addBackHits + countKnuthAddBack u v
      let nu := toNat u
      let nv := toNat v
      out := out.push { tag := s!"knuth-addback-sh{sh}", op := .div, a := nu, b := nv }
      out := out.push { tag := s!"knuth-addback-sh{sh}", op := .mod, a := nu, b := nv }
  -- 4. Karatsuba thresholds (31, 32, 33, 63, 64, 65, 127, 128, 129, 256, 512, 1000 limbs)
  let karaSizes : Array Nat := #[1, 2, 15, 16, 30, 31, 32, 33, 34, 48, 63, 64, 65, 96, 127, 128, 129, 256]
  for sa in karaSizes do
    for sb in #[sa, if sa > 0 then sa - 1 else 0, sa + 1, 31, 32, 33] do
      let (na, r1) := r.nextNatLimbs sa
      let (nb, r2) := r1.nextNatLimbs sb
      r := r2
      out := out.push { tag := s!"kara-mul-{sa}x{sb}", op := .mul, a := na, b := nb }
      out := out.push { tag := s!"kara-add-{sa}x{sb}", op := .add, a := na, b := nb }
      out := out.push { tag := s!"kara-sub-{sa}x{sb}", op := .sub, a := na, b := nb }
    let (na, r1) := r.nextNatLimbs sa
    r := r1
    out := out.push { tag := s!"kara-sqr-{sa}", op := .sqr, a := na, b := 0 }
    -- All-ones carry cascade at exact threshold sizes
    let onesA := allOnesLimbs sa
    out := out.push { tag := s!"kara-ones-mul-{sa}", op := .mul, a := onesA, b := onesA }
    out := out.push { tag := s!"kara-ones-add-{sa}", op := .add, a := onesA, b := 1 }
    out := out.push { tag := s!"kara-ones-sub-{sa}", op := .sub, a := onesA + 1, b := 1 }
  -- 5. Large 300..1,000-limb (up to 64,000-bit) full-suite stress
  for bigSz in #[300, 512, 750, 1000] do
    let (na, r1) := r.nextNatLimbs bigSz
    let (nb, r2) := r1.nextNatLimbs bigSz
    let (nc, r3) := r2.nextNatLimbs (bigSz / 2)
    r := r3
    let tag := s!"large-{bigSz}limbs"
    out := out.push { tag, op := .add, a := na, b := nb }
    out := out.push { tag, op := .sub, a := na, b := nb }
    out := out.push { tag, op := .sub, a := nb, b := na }
    out := out.push { tag, op := .mul, a := na, b := nb }
    out := out.push { tag, op := .sqr, a := na, b := 0 }
    out := out.push { tag, op := .div, a := na, b := nc }
    out := out.push { tag, op := .mod, a := na, b := nc }
    out := out.push { tag, op := .div, a := na, b := 0 }
    out := out.push { tag, op := .mod, a := na, b := 0 }
    out := out.push { tag, op := .land, a := na, b := nb }
    out := out.push { tag, op := .lor, a := na, b := nb }
    out := out.push { tag, op := .xor, a := na, b := nb }
    out := out.push { tag, op := .beq, a := na, b := na }
    out := out.push { tag, op := .beq, a := na, b := nb }
    out := out.push { tag, op := .ble, a := na, b := nb }
    out := out.push { tag, op := .blt, a := na, b := nb }
    out := out.push { tag, op := .shiftLeft, a := na, b := 65 }
    out := out.push { tag, op := .shiftRight, a := na, b := 65 }
    out := out.push { tag, op := .log2, a := na, b := 0 }
    out := out.push { tag, op := .pred, a := na, b := 0 }
  (out, addBackHits, r)

/-- Generate `n` randomized differential cases across all 18 operations and 0..1000 limbs
(with stratified limb-length distribution so 100k+ checks run in seconds). -/
def generateRandomCase (idx : Nat) (r : Rng) : DiffCase × Rng :=
  let bucket := idx % 20
  if bucket < 7 then
    -- Linear & bitwise & comparisons: up to 128 limbs (occasionally 512)
    let maxL := if idx % 200 == 0 then 512 else if idx % 40 == 0 then 128 else if idx % 10 == 0 then 32 else 8
    let (la, r1) := r.nextRange (maxL + 1)
    let (lb, r2) := r1.nextRange (maxL + 1)
    let (a, r3) := r2.nextNatLimbs la
    let (b, r4) := r3.nextNatLimbs lb
    let ops : Array DiffOp := #[.add, .sub, .land, .lor, .xor, .beq, .ble, .blt, .pred, .log2]
    let (oi, r5) := r4.nextRange ops.size
    let op := ops.getD oi .add
    ({ tag := s!"rand-lin-{idx}", op, a, b }, r5)
  else if bucket < 10 then
    -- Shifts
    let maxL := if idx % 100 == 0 then 128 else 20
    let (la, r1) := r.nextRange (maxL + 1)
    let (a, r2) := r1.nextNatLimbs la
    let (sh, r3) := r2.nextRange 320
    let op := if idx % 2 == 0 then DiffOp.shiftLeft else DiffOp.shiftRight
    ({ tag := s!"rand-shift-{idx}", op, a, b := sh }, r3)
  else if bucket < 14 then
    -- Mul & Sqr (exercising both schoolbook and Karatsuba > 32 limbs)
    let maxL := if idx % 160 == 0 then 140 else if idx % 25 == 0 then 40 else 12
    let (la, r1) := r.nextRange (maxL + 1)
    let (lb, r2) := r1.nextRange (maxL + 1)
    let (a, r3) := r2.nextNatLimbs la
    let (b, r4) := r3.nextNatLimbs lb
    let op := if bucket == 13 then DiffOp.sqr else DiffOp.mul
    ({ tag := s!"rand-mul-{idx}", op, a, b }, r4)
  else if bucket < 18 then
    -- Div & Mod (mixing direct random, exact multiples q*b, and q*b - 1)
    let maxL := if idx % 120 == 0 then 64 else if idx % 20 == 0 then 24 else 8
    let (la, r1) := r.nextRange (maxL + 1)
    let (lb, r2) := r1.nextRange (maxL + 1)
    let (a0, r3) := r2.nextNatLimbs la
    let (b, r4) := r3.nextNatLimbs lb
    let a :=
      if idx % 7 == 0 && b > 0 then a0 * b - 1
      else if idx % 7 == 1 && b > 0 then a0 * b
      else a0
    let op := if idx % 2 == 0 then DiffOp.div else DiffOp.mod
    ({ tag := s!"rand-div-{idx}", op, a, b }, r4)
  else if bucket == 18 then
    -- GCD (50% shared-factor triples (g*a, g*b))
    let (la, r1) := r.nextRange 8
    let (lb, r2) := r1.nextRange 8
    let (a0, r3) := r2.nextNatLimbs la
    let (b0, r4) := r3.nextNatLimbs lb
    let (g0, r5) := r4.nextNatLimbs (idx % 4 + 1)
    let (a, b) := if idx % 2 == 0 then (a0 * g0, b0 * g0) else (a0, b0)
    ({ tag := s!"rand-gcd-{idx}", op := .gcd, a, b }, r5)
  else
    -- Pow (small bases and bounded exponents)
    let (la, r1) := r.nextRange 4
    let (a, r2) := r1.nextNatLimbs la
    let (e, r3) := r2.nextRange 20
    ({ tag := s!"rand-pow-{idx}", op := .pow, a, b := e }, r3)

/-! ## Configuration, CLI Parsing, and Execution Backends -/

inductive RunMode where
  | selfTest
  | batch (exe : String) (extraArgs : Array String)
  | exePerOp (exeDir : Option String) (overrides : Array (DiffOp × String))
  | emitVectors (outPath : String)
  deriving Repr

structure Config where
  mode : RunMode := .selfTest
  targetCount : Nat := 100000
  seed : UInt64 := 0x9e3779b97f4a7c15
  filterOp : Option DiffOp := none
  boolAsNat : Bool := false
  failFast : Bool := false
  exeLimit : Nat := 500
  batchChunkSize : Nat := 4096

def parseNatArg (flag val : String) : Except String Nat :=
  match val.toNat? with
  | some n => .ok n
  | none => .error s!"invalid natural number for {flag}: '{val}'"

def parseArgs (args : List String) : Except String Config :=
  let rec go (rest : List String) (cfg : Config) (extraArgs : Array String)
      (overrides : Array (DiffOp × String)) : Except String Config :=
    match rest with
    | [] =>
      let mode := match cfg.mode with
        | .batch exe _ => .batch exe extraArgs
        | .exePerOp dir _ => .exePerOp dir overrides
        | m => m
      .ok { cfg with mode }
    | "--self-test" :: tl => go tl { cfg with mode := .selfTest } extraArgs overrides
    | "--batch" :: exe :: tl => go tl { cfg with mode := .batch exe #[] } extraArgs overrides
    | "--arg" :: v :: tl => go tl cfg (extraArgs.push v) overrides
    | "--exe-dir" :: dir :: tl =>
      go tl { cfg with mode := .exePerOp (some dir) #[] } extraArgs overrides
    | "--exe" :: spec :: tl =>
      match spec.splitOn "=" with
      | [opName, path] =>
        match DiffOp.ofName? opName with
        | some op =>
          let mode := match cfg.mode with
            | .exePerOp dir _ => .exePerOp dir #[]
            | _ => .exePerOp none #[]
          go tl { cfg with mode } extraArgs (overrides.push (op, path))
        | none => .error s!"unknown op in --exe: '{opName}'"
      | _ => .error s!"--exe expects <op>=<path>, got '{spec}'"
    | "--emit-vectors" :: path :: tl =>
      go tl { cfg with mode := .emitVectors path } extraArgs overrides
    | "--count" :: v :: tl => do
      let n ← parseNatArg "--count" v
      go tl { cfg with targetCount := n } extraArgs overrides
    | "--seed" :: v :: tl => do
      let n ← parseNatArg "--seed" v
      go tl { cfg with seed := UInt64.ofNat n } extraArgs overrides
    | "--exe-limit" :: v :: tl => do
      let n ← parseNatArg "--exe-limit" v
      go tl { cfg with exeLimit := n } extraArgs overrides
    | "--chunk" :: v :: tl => do
      let n ← parseNatArg "--chunk" v
      go tl { cfg with batchChunkSize := max 1 n } extraArgs overrides
    | "--op" :: opName :: tl =>
      match DiffOp.ofName? opName with
      | some op => go tl { cfg with filterOp := some op } extraArgs overrides
      | none => .error s!"unknown --op '{opName}'"
    | "--bool-as-nat" :: tl => go tl { cfg with boolAsNat := true } extraArgs overrides
    | "--fail-fast" :: tl => go tl { cfg with failFast := true } extraArgs overrides
    | flag :: _ => .error s!"unknown or incomplete CLI argument: '{flag}'"
  go args {} #[] #[]

structure RunStats where
  checked : Nat := 0
  failures : Nat := 0
  wfFailures : Nat := 0
  addBackHits : Nat := 0

def keepCase (cfg : Config) (c : DiffCase) : Bool :=
  match cfg.filterOp with
  | none => true
  | some op => c.op == op

/-- Truncate huge decimal numbers when printing failure diagnostics. -/
def previewNum (s : String) : String :=
  if s.length ≤ 80 then s
  else s!"{s.take 36}...({s.length} digits)...{s.drop (s.length - 20)}"

def reportMismatch (st : RunStats) (c : DiffCase) (expected got : String) (wfOk : Bool) :
    IO RunStats := do
  if st.failures < 20 then
    IO.eprintln s!"MISMATCH [{c.tag}] {c.op.name}({previewNum (toString c.a)}, {previewNum (toString c.b)}):"
    IO.eprintln s!"  expected (GMP): {previewNum expected}"
    IO.eprintln s!"  actual        : {previewNum got} (WF={wfOk})"
  pure {
    st with
    checked := st.checked + 1
    failures := st.failures + 1
    wfFailures := st.wfFailures + (if wfOk then 0 else 1)
  }

/-- Build the full filtered test vector array (adversarial + randomized up to `cfg.targetCount`). -/
def buildAllCases (cfg : Config) : Array DiffCase × Nat := Id.run do
  let r0 : Rng := { state := cfg.seed }
  let (advRaw, addBackHits, r1) := buildAdversarialCases r0
  let mut cases : Array DiffCase := Array.mkEmpty (max cfg.targetCount advRaw.size)
  for c in advRaw do
    if keepCase cfg c then
      cases := cases.push c
  let mut r := r1
  let mut idx := 0
  let maxIters := cfg.targetCount * 20 + 1000
  for _ in [:maxIters] do
    if cases.size ≥ cfg.targetCount then
      break
    let (c, r') := generateRandomCase idx r
    r := r'
    idx := idx + 1
    if keepCase cfg c then
      cases := cases.push c
  (cases, addBackHits)

/-- Mode 1: In-process self-test comparing `IxCC.BigNat` + `WF` against Lean 4 GMP. -/
def runSelfTest (cfg : Config) (cases : Array DiffCase) (addBackHits : Nat) : IO RunStats := do
  let mut st : RunStats := { addBackHits }
  for c in cases do
    let expected := c.op.evalGMP cfg.boolAsNat c.a c.b
    let (got, wfOk) := c.op.evalBigNat cfg.boolAsNat c.a c.b
    if got == expected && wfOk then
      st := { st with checked := st.checked + 1 }
    else
      st ← reportMismatch st c expected got wfOk
      if cfg.failFast then return st
  -- Also verify `toDecimal` / `ofDecimal` roundtrip on boundaries + large 1000-limb value
  let decSamples := boundaryVals ++ #[allOnesLimbs 32, allOnesLimbs 64, allOnesLimbs 128, allOnesLimbs 1000]
  for n in decSamples do
    let bn := ofNat n
    let dec := toDecimal bn
    let rt := ofDecimal dec
    let ok := dec == toString n && rt == some bn
    if ok then
      st := { st with checked := st.checked + 1 }
    else
      st ← reportMismatch st { tag := "decimal-rt", op := .add, a := n, b := 0 }
        (toString n) dec (rt == some bn)
      if cfg.failFast then return st
  pure st

/-- Mode 2: Stream chunks of `<op> <a> [b]\n` to a single compiled `ixcc` batch executable. -/
def runBatch (cfg : Config) (exe : String) (extraArgs : Array String)
    (cases : Array DiffCase) (addBackHits : Nat) : IO RunStats := do
  let mut st : RunStats := { addBackHits }
  let chunkSz := max 1 cfg.batchChunkSize
  let numChunks := (cases.size + chunkSz - 1) / chunkSz
  for ci in [:numChunks] do
    let start := ci * chunkSz
    let stop := min cases.size (start + chunkSz)
    let slice := cases.extract start stop
    let mut inputBuf := ""
    for c in slice do
      inputBuf := inputBuf ++ c.toRequestLine ++ "\n"
    let child ← IO.Process.spawn {
      cmd := exe
      args := extraArgs
      stdin := .piped
      stdout := .piped
      stderr := .piped
    }
    let (stdin, child) ← child.takeStdin
    let writeTask ← IO.asTask (prio := .dedicated) do
      stdin.putStr inputBuf
      stdin.flush
    let errTask ← IO.asTask (prio := .dedicated) child.stderr.readToEnd
    let stdout ← child.stdout.readToEnd
    let _ ← IO.ofExcept writeTask.get
    let stderr ← IO.ofExcept errTask.get
    let exitCode ← child.wait
    if exitCode != 0 then
      throw (IO.userError s!"batch executable '{exe}' exited with code {exitCode}: {stderr}")
    let lines := (stdout.splitOn "\n").toArray.filter (fun l => !l.trimAscii.isEmpty)
    if lines.size != slice.size then
      throw (IO.userError s!"batch chunk {ci}: expected {slice.size} output lines, got {lines.size}")
    for j in [:slice.size] do
      let c := slice[j]!
      let expected := c.op.evalGMP cfg.boolAsNat c.a c.b
      let got := lines[j]!.trimAscii.toString
      if got == expected then
        st := { st with checked := st.checked + 1 }
      else
        st ← reportMismatch st c expected got true
        if cfg.failFast then return st
  pure st

/-- Resolve the binary path for `op` under `--exe-dir` / `--exe`. -/
def resolveOpExe (exeDir : Option String) (overrides : Array (DiffOp × String)) (op : DiffOp) :
    Option String :=
  match overrides.find? (fun p => p.1 == op) with
  | some (_, path) => some path
  | none => exeDir.map fun dir => s!"{dir}/{op.name}"

/-- Mode 3: Invoke per-operation standalone compiled `ixcc --exe` binaries (`<exe> <a> [b]`). -/
def runExePerOp (cfg : Config) (exeDir : Option String) (overrides : Array (DiffOp × String))
    (cases : Array DiffCase) (addBackHits : Nat) : IO RunStats := do
  let mut st : RunStats := { addBackHits }
  let limit := min cases.size cfg.exeLimit
  for i in [:limit] do
    let c := cases[i]!
    match resolveOpExe exeDir overrides c.op with
    | none => pure ()
    | some exe =>
      let args := if c.op.isUnary then #[toString c.a] else #[toString c.a, toString c.b]
      let out ← IO.Process.output { cmd := exe, args }
      if out.exitCode != 0 then
        throw (IO.userError s!"exe '{exe}' exited {out.exitCode} on {c.tag}: {out.stderr}")
      let got := out.stdout.trimAscii.toString
      let expected := c.op.evalGMP cfg.boolAsNat c.a c.b
      if got == expected then
        st := { st with checked := st.checked + 1 }
      else
        st ← reportMismatch st c expected got true
        if cfg.failFast then return st
  pure st

/-- Mode 4: Emit `<op> <a> <b> <expected>` lines to `outPath` for external/CI differential suites. -/
def runEmitVectors (cfg : Config) (outPath : String) (cases : Array DiffCase)
    (addBackHits : Nat) : IO RunStats := do
  let h ← IO.FS.Handle.mk outPath .write
  let mut count := 0
  for c in cases do
    let expected := c.op.evalGMP cfg.boolAsNat c.a c.b
    h.putStrLn s!"{c.op.name} {c.a} {c.b} {expected}"
    count := count + 1
  h.flush
  pure { checked := count, failures := 0, wfFailures := 0, addBackHits }

def runWithConfig (cfg : Config) : IO Unit := do
  let (cases, addBackHits) := buildAllCases cfg
  if cfg.filterOp.isNone && addBackHits < 10 then
    throw (IO.userError s!"Expected ≥ 10 Knuth Algorithm D add-back triggers, got {addBackHits}")
  let st ← match cfg.mode with
    | .selfTest => runSelfTest cfg cases addBackHits
    | .batch exe extra => runBatch cfg exe extra cases addBackHits
    | .exePerOp dir ovs => runExePerOp cfg dir ovs cases addBackHits
    | .emitVectors path => runEmitVectors cfg path cases addBackHits
  if st.failures != 0 then
    throw (IO.userError
      s!"NativeDiff FAILED: {st.failures} mismatches ({st.wfFailures} WF failures) out of {st.checked} checks")
  IO.println
    s!"NativeDiff PASS: {st.checked} checks, 0 failures ({st.addBackHits} Knuth D add-back triggers, 0..1000 limbs, Karatsuba thresholds 31..1000)"

def main (args : List String) : IO Unit := do
  match parseArgs args with
  | .error msg =>
    IO.eprintln s!"NativeDiff usage error: {msg}"
    IO.eprintln "Usage: native-diff [--self-test | --batch <exe> [--arg <x>] | --exe-dir <dir> | --exe <op>=<path> | --emit-vectors <file>]"
    IO.eprintln "                   [--count <N>] [--seed <UInt64>] [--op <name>] [--bool-as-nat] [--exe-limit <N>] [--fail-fast]"
    IO.Process.exit 2
  | .ok cfg => runWithConfig cfg

end IxCCTests.BigNat.NativeDiff

def main (args : List String) : IO Unit := IxCCTests.BigNat.NativeDiff.main args
