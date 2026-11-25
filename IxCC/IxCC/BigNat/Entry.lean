import IxCC.BigNat

/-! # Arbitrary-Precision `Nat` Slow-Path Entrypoints (`IxCC.BigNat.Entry`)

Monomorphic, first-order, zero-`Nat ≥ 2^63` slow-path entrypoints for every `Nat`
operation in IxCC (`add`, `sub`, `pred`, `mul`, `divMod`, `div`, `mod`, `pow`,
`pow?`, `gcd`, `cmp`, `beq`, `ble`, `blt`, `land`, `lor`, `xor`, `shiftLeft`,
`shiftLeft?`, `shiftRight`, `shiftRightSlow`, `log2`, `log2Slow`, `toDecimal`,
`ofDecimal`).

## Representation & Canonical Boundary Contract

`SlowNat` is the pure-Lean algebraic mirror of the Phase 4 runtime `Nat` value
representation (`IxCC/docs/bignum-design.md`, §Representation):

* `.small (v : UInt64)` — immediate fixnum value `v < 2^63` (equivalently
  `(v >>> 63) == 0`), corresponding to odd tagged word `2v + 1`.
* `.big (limbs : Array UInt64)` — canonical little-endian base-`2^64` limb array
  with `BigNat.WF limbs` and `BigNat.toNat limbs ≥ 2^63`, corresponding to an
  even pointer to a `LimbArray` cell (`scan = 0`, `tag = 0x7F03`).

Every entrypoint handles all four operand combinations (`small-small`,
`small-big`, `big-small`, `big-big`), promotes results `≥ 2^63` to canonical
`.big`, and demotes results `< 2^63` to canonical `.small` without ever
constructing a `Nat` literal or intermediate `Nat` value `≥ 2^63`.

## References

* Donald E. Knuth, *The Art of Computer Programming*, Vol. 2, §4.3.1, §4.4, §4.5.2, §4.6.3.
* Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone, *Handbook of Applied
  Cryptography*, Ch. 14.
* Richard P. Brent and Paul Zimmermann, *Modern Computer Arithmetic*, Ch. 1.
* `IxCC/docs/bignum-design.md` (§Representation, §Bootstrapping, §Proof obligation).
-/

set_option autoImplicit false

namespace IxCC.BigNat.Entry

open IxCC.BigNat

/-! ## Runtime Value Type and Specification Denotation -/

/-- Canonical boundary representation between tagged fixnums (`< 2^63`) and
arbitrary-precision `BigNat` limb arrays (`≥ 2^63`). -/
inductive SlowNat where
  /-- Small fixnum value (`v.toNat < 2^63`, tagged as `2v + 1` at LIR). -/
  | small (v : UInt64)
  /-- Canonical multi-precision limb array (`WF limbs ∧ 2^63 ≤ toNat limbs`). -/
  | big (limbs : Array UInt64)
  deriving DecidableEq, Repr, Inhabited

/-- Specification function: exact mathematical `Nat` denoted by a `SlowNat`.
Proof/test only — never called by runtime routines. -/
def SlowNat.val : SlowNat → Nat
  | .small v => v.toNat
  | .big ls => BigNat.toNat ls

/-- Canonical normal-form invariant for `SlowNat`:
* `.small v` holds strictly `< 2^63`;
* `.big ls` is canonical (`BigNat.WF ls`) and `≥ 2^63`. -/
def SlowNat.Canonical : SlowNat → Prop
  | .small v => v.toNat < 2 ^ 63
  | .big ls => BigNat.WF ls ∧ 2 ^ 63 ≤ BigNat.toNat ls

/-- Specification/test helper: convert any `Nat` to its canonical `SlowNat`.
Proof/test only — never called by runtime routines. -/
def SlowNat.ofNat (n : Nat) : SlowNat :=
  if n < 2 ^ 63 then .small (UInt64.ofNat n) else .big (BigNat.ofNat n)

/-- Number of limbs in a `SlowNat` (`0` for `0`, `1` for nonzero small, `ls.size` for big). -/
@[inline] def SlowNat.limbCount : SlowNat → Nat
  | .small v => if v == 0 then 0 else 1
  | .big ls => ls.size

/-! ## Canonical Promotion, Demotion, and Tagging Helpers -/

/-- Test whether a `UInt64` fits in the small fixnum range `[0, 2^63)` without
constructing any `Nat` literal `≥ 2^63`. -/
@[inline] def isSmallU64 (v : UInt64) : Bool :=
  (v >>> (63 : UInt64)) == 0

/-- Canonical promotion of a raw `UInt64` word: `.small v` if `< 2^63`, else `.big #[v]`. -/
@[inline] def fromUInt64 (v : UInt64) : SlowNat :=
  if isSmallU64 v then .small v else .big #[v]

/-- Canonical normalization and demotion of a limb array:
returns `.small v` iff `toNat xs < 2^63`, else `.big (normalize xs)`. -/
def fromLimbs (xs : Array UInt64) : SlowNat :=
  let ys := normalize xs
  if h : ys.size = 0 then
    .small 0
  else if ys.size == 1 then
    let v := ys[0]'(Nat.pos_of_ne_zero h)
    if isSmallU64 v then .small v else .big ys
  else
    .big ys

/-- View any `SlowNat` as a little-endian `Array UInt64` limb array. -/
@[inline] def toLimbs : SlowNat → Array UInt64
  | .small v => ofUInt64 v
  | .big ls => ls

/-- Re-canonicalize an arbitrary `SlowNat`. -/
@[inline] def canon : SlowNat → SlowNat
  | .small v => fromUInt64 v
  | .big ls => fromLimbs ls

/-- Decode a small tagged LIR immediate `2n + 1` into a canonical `.small` `SlowNat`.
Because `(w >>> 1).toNat < 2^63` unconditionally, the result is always canonical. -/
@[inline] def ofTaggedWord (w : UInt64) : SlowNat :=
  .small (w >>> (1 : UInt64))

/-- Encode a canonical `.small` `SlowNat` as a tagged LIR immediate `2n + 1`;
returns `none` for values `≥ 2^63`. -/
@[inline] def toTaggedWord? : SlowNat → Option UInt64
  | .small v =>
    if isSmallU64 v then some ((v <<< (1 : UInt64)) ||| (1 : UInt64)) else none
  | .big _ => none

/-- Promote a small runtime `Nat` (`n < 2^63`) into a canonical `SlowNat`. -/
@[inline] def ofSmallNat (n : Nat) : SlowNat :=
  fromUInt64 (UInt64.ofNat n)

/-- Computable canonical normal-form predicate matching `SlowNat.Canonical`. -/
def isCanonical : SlowNat → Bool
  | .small v => isSmallU64 v
  | .big ls =>
    if h : 0 < ls.size then
      let top := ls[ls.size - 1]'(Nat.sub_lt h Nat.one_pos)
      if top == 0 then false
      else if ls.size == 1 then !isSmallU64 top
      else true
    else false

/-- Test whether a `SlowNat` denotes `0`. -/
@[inline] def isZero : SlowNat → Bool
  | .small v => v == 0
  | .big ls => (normalize ls).size == 0

/-- Test whether a `SlowNat` denotes `1`. -/
@[inline] def isOne : SlowNat → Bool
  | .small v => v == 1
  | .big ls =>
    let ys := normalize ls
    ys.size == 1 && getLimb ys 0 == 1

/-! ## Comparisons (`cmp`, `beq`, `ble`, `blt`) -/

/-- Three-way comparison on canonical `SlowNat`s. Small-vs-big comparisons resolve in
O(1) with zero limb reads by canonical threshold separation (`< 2^63` vs `≥ 2^63`). -/
def cmp (a b : SlowNat) : Ordering :=
  match a, b with
  | .small va, .small vb =>
    if va < vb then .lt
    else if va > vb then .gt
    else .eq
  | .small _, .big _ => .lt
  | .big _, .small _ => .gt
  | .big la, .big lb => BigNat.cmp la lb

/-- Arbitrary-precision `Nat.beq` slow-path entrypoint. -/
@[inline] def beq (a b : SlowNat) : Bool :=
  match cmp a b with
  | .eq => true
  | _ => false

/-- Arbitrary-precision `Nat.ble` slow-path entrypoint. -/
@[inline] def ble (a b : SlowNat) : Bool :=
  match cmp a b with
  | .gt => false
  | _ => true

/-- Arbitrary-precision `Nat.blt` slow-path entrypoint. -/
@[inline] def blt (a b : SlowNat) : Bool :=
  match cmp a b with
  | .lt => true
  | _ => false

/-! ## Linear Arithmetic (`add`, `sub`, `pred`) -/

/-- Arbitrary-precision `Nat.add` slow-path entrypoint.
Uses a single `addCarry64` without intermediate limb arrays on `small-small` overflow. -/
def add (a b : SlowNat) : SlowNat :=
  match a, b with
  | .small va, .small vb =>
    let (lo, carry) := addCarry64 va vb false
    if carry then .big #[lo, 1]
    else fromUInt64 lo
  | _, _ => fromLimbs (BigNat.add (toLimbs a) (toLimbs b))

/-- Arbitrary-precision truncating `Nat.sub` slow-path entrypoint (with demotion). -/
def sub (a b : SlowNat) : SlowNat :=
  match a, b with
  | .small va, .small vb =>
    if va < vb then .small 0
    else fromUInt64 (va - vb)
  | _, _ => fromLimbs (BigNat.subRaw (toLimbs a) (toLimbs b))

/-- Arbitrary-precision truncating `Nat.pred` slow-path entrypoint (demotes `2^63` to `2^63 - 1`). -/
def pred (a : SlowNat) : SlowNat :=
  match a with
  | .small va =>
    if va == 0 then .small 0 else fromUInt64 (va - 1)
  | .big ls => fromLimbs (BigNat.pred (normalize ls))

/-! ## Multiplication and Exponentiation (`mul`, `pow`, `pow?`) -/

/-- Arbitrary-precision `Nat.mul` slow-path entrypoint.
Fast-paths `small-small` via one `mulWide64` and `small-big`/`big-small` via linear `mulAdd1`. -/
def mul (a b : SlowNat) : SlowNat :=
  match a, b with
  | .small va, .small vb =>
    let (lo, hi) := mulWide64 va vb
    if hi == 0 then fromUInt64 lo else .big #[lo, hi]
  | .small va, .big lb =>
    if va == 0 then .small 0 else fromLimbs (BigNat.mulAdd1 lb va 0)
  | .big la, .small vb =>
    if vb == 0 then .small 0 else fromLimbs (BigNat.mulAdd1 la vb 0)
  | .big la, .big lb =>
    fromLimbs (BigNat.mul la lb)

/-- Arbitrary-precision exponentiation for a small `Nat` exponent (`exp < 2^63`). -/
def pow (base : SlowNat) (exp : Nat) : SlowNat :=
  fromLimbs (BigNat.pow (toLimbs base) exp)

/-- Arbitrary-precision `Nat.pow` slow-path entrypoint accepting a `SlowNat` exponent.
Returns `some (base ^ exp)` whenever the exponent is `< 2^63` OR `base ∈ {0, 1}`
(handling `0^big = 0` and `1^big = 1` in O(1)); returns `none` exclusively when
`base ≥ 2` and `exp ≥ 2^63` (where `base ^ exp ≥ 2^(2^63)` exceeds any 64-bit heap). -/
def pow? (base exp : SlowNat) : Option SlowNat :=
  match exp with
  | .small ve =>
    if isSmallU64 ve then
      some (fromLimbs (BigNat.pow (toLimbs base) ve.toNat))
    else if isZero base then some (.small 0)
    else if isOne base then some (.small 1)
    else none
  | .big le =>
    let le' := normalize le
    if le'.size == 0 then
      some (.small 1)
    else
      match toSmall? le' with
      | some e => some (fromLimbs (BigNat.pow (toLimbs base) e))
      | none =>
        if isZero base then some (.small 0)
        else if isOne base then some (.small 1)
        else none

/-! ## Euclidean Division and Remainder (`divMod`, `div`, `mod`) -/

/-- Arbitrary-precision Euclidean division and remainder matching Lean's `Nat.div`/`Nat.mod`
(`a / 0 = 0`, `a % 0 = a`). Delegates `.big` dividends to `BigNat.divMod`, which fast-paths
1-limb divisors via Möller–Granlund `divMod1`. -/
def divMod (a b : SlowNat) : SlowNat × SlowNat :=
  match a with
  | .small va =>
    match b with
    | .small vb =>
      if vb == 0 then (.small 0, fromUInt64 va)
      else (fromUInt64 (va / vb), fromUInt64 (va % vb))
    | .big lb =>
      let lb' := normalize lb
      if lb'.size == 1 then
        let vb := getLimb lb' 0
        (fromUInt64 (va / vb), fromUInt64 (va % vb))
      else (.small 0, fromUInt64 va)
  | .big la =>
    let (q, r) := BigNat.divMod la (toLimbs b)
    (fromLimbs q, fromLimbs r)

/-- Arbitrary-precision `Nat.div` slow-path entrypoint.
Routes `.big` dividends directly through `BigNat.div` (activating 1-limb `divMod1`,
the O(1) `divQuick1` fast path, and skipping remainder unnormalization). -/
def div (a b : SlowNat) : SlowNat :=
  match a with
  | .small va =>
    match b with
    | .small vb =>
      if vb == 0 then .small 0 else fromUInt64 (va / vb)
    | .big lb =>
      let lb' := normalize lb
      if lb'.size == 1 then fromUInt64 (va / getLimb lb' 0)
      else .small 0
  | .big la =>
    fromLimbs (BigNat.div la (toLimbs b))

/-- Arbitrary-precision `Nat.mod` slow-path entrypoint.
Implemented directly (avoiding duplicating `Entry.divMod` in the compiled closure). -/
def mod (a b : SlowNat) : SlowNat :=
  match a with
  | .small va =>
    match b with
    | .small vb =>
      if vb == 0 then fromUInt64 va else fromUInt64 (va % vb)
    | .big lb =>
      let lb' := normalize lb
      if lb'.size == 1 then fromUInt64 (va % getLimb lb' 0)
      else fromUInt64 va
  | .big la =>
    fromLimbs (BigNat.mod la (toLimbs b))

/-! ## Greatest Common Divisor (`gcd`) -/

/-- Tail-recursive Euclidean GCD on raw `UInt64` words (zero `Nat` allocation). -/
def gcdU64 (a b : UInt64) : UInt64 :=
  if h : b = 0 then a
  else
    have hlt : (a % b).toNat < b.toNat := by
      rw [UInt64.toNat_mod]
      have hb : 0 < b.toNat := by
        have hne : b.toNat ≠ 0 := fun hz => h (UInt64.toNat_inj.mp (by simpa using hz))
        omega
      exact Nat.mod_lt a.toNat hb
    gcdU64 b (a % b)
termination_by b.toNat

/-- Arbitrary-precision `Nat.gcd` slow-path entrypoint.
Fast-paths `small-small` via `gcdU64`; delegates mixed/big pairs to `BigNat.gcd`
(which reduces 1-limb operands via `divMod1` + `gcdWord64` and multi-limb pairs via Lehmer).
Matches on `a` first, so no match alternative is shared between branches (a shared
alternative is copied into each branch, with the `BigNat.gcd` call it holds). -/
def gcd (a b : SlowNat) : SlowNat :=
  match a with
  | .small va =>
    match b with
    | .small vb => fromUInt64 (gcdU64 va vb)
    | .big lb => fromLimbs (BigNat.gcd (ofUInt64 va) lb)
  | .big la => fromLimbs (BigNat.gcd la (toLimbs b))

/-! ## Bitwise Operations (`land`, `lor`, `xor`) -/

/-- Arbitrary-precision `Nat.land` slow-path entrypoint.
Any `small &&& big` or `big &&& small` resolves in O(1) on limb 0 with zero allocation. -/
def land (a b : SlowNat) : SlowNat :=
  match a, b with
  | .small va, .small vb => fromUInt64 (va &&& vb)
  | .small va, .big lb => fromUInt64 (va &&& getLimb lb 0)
  | .big la, .small vb => fromUInt64 (getLimb la 0 &&& vb)
  | .big la, .big lb => fromLimbs (BigNat.land la lb)

/-- Arbitrary-precision `Nat.lor` slow-path entrypoint. -/
def lor (a b : SlowNat) : SlowNat :=
  match a, b with
  | .small va, .small vb => fromUInt64 (va ||| vb)
  | _, _ => fromLimbs (BigNat.lor (toLimbs a) (toLimbs b))

/-- Arbitrary-precision `Nat.xor` slow-path entrypoint (with demotion when top limbs cancel). -/
def xor (a b : SlowNat) : SlowNat :=
  match a, b with
  | .small va, .small vb => fromUInt64 (va ^^^ vb)
  | _, _ => fromLimbs (BigNat.xor (toLimbs a) (toLimbs b))

/-! ## Shifts and Base-2 Logarithm (`shiftLeft`, `shiftRight`, `log2`) -/

/-- Arbitrary-precision left shift by a small `Nat` count (`s < 2^63`). -/
def shiftLeft (a : SlowNat) (s : Nat) : SlowNat :=
  fromLimbs (BigNat.shiftLeft (toLimbs a) s)

/-- Arbitrary-precision `Nat.shiftLeft` slow-path entrypoint accepting a `SlowNat` count.
Returns `some 0` for `0 <<< big`, `some (a <<< s)` for any small `s < 2^63`, and `none`
exclusively when `a > 0 ∧ s ≥ 2^63` (where `a * 2^s ≥ 2^(2^63)` exceeds any 64-bit heap). -/
def shiftLeft? (a s : SlowNat) : Option SlowNat :=
  if isZero a then some (.small 0)
  else
    match s with
    | .small vs =>
      if isSmallU64 vs then some (fromLimbs (BigNat.shiftLeft (toLimbs a) vs.toNat))
      else none
    | .big ls =>
      match toSmall? (normalize ls) with
      | some sv => some (fromLimbs (BigNat.shiftLeft (toLimbs a) sv))
      | none => none

/-- Arbitrary-precision right shift by a small `Nat` count (`s < 2^63`). -/
def shiftRight (a : SlowNat) (s : Nat) : SlowNat :=
  fromLimbs (BigNat.shiftRight (toLimbs a) s)

/-- Arbitrary-precision `Nat.shiftRight` slow-path entrypoint accepting a `SlowNat` count.
For any shift count `s ≥ 2^63` and any representable `a` (`limbCount < 2^57`, covering
all arrays up to 1 exabyte), `a >>> s = 0` immediately in O(1). -/
def shiftRightSlow (a s : SlowNat) : SlowNat :=
  match a, s with
  | .small va, .small vs =>
    if vs ≥ (64 : UInt64) then .small 0 else fromUInt64 (va >>> vs)
  | .small va, .big ls =>
    match toSmall? (normalize ls) with
    | some sv =>
      if sv ≥ 64 then .small 0 else fromUInt64 (va >>> UInt64.ofNat sv)
    | none => .small 0
  | .big la, .small vs =>
    if isSmallU64 vs then fromLimbs (BigNat.shiftRight la vs.toNat)
    else .small 0
  | .big la, .big ls =>
    match toSmall? (normalize ls) with
    | some sv => fromLimbs (BigNat.shiftRight la sv)
    | none => .small 0

/-- Base-2 floor logarithm returning a small `Nat` matching `Nat.log2` (`log2 0 = 0`). -/
def log2 (a : SlowNat) : Nat :=
  match a with
  | .small va => if va == 0 then 0 else 63 - (clz64 va).toNat
  | .big la => BigNat.log2 (normalize la)

/-- Base-2 floor logarithm returning a canonical `SlowNat`. -/
def log2Slow (a : SlowNat) : SlowNat :=
  fromUInt64 (UInt64.ofNat (log2 a))

/-! ## Decimal Formatting and Parsing (`toDecimal`, `ofDecimal`) -/

/-- Canonical base-10 ASCII string conversion via `10^19` chunked division. -/
def toDecimal (a : SlowNat) : String :=
  BigNat.toDecimal (toLimbs a)

/-- Parse a non-empty ASCII decimal string into a canonical `SlowNat`,
demoting values `< 2^63` to `.small` and keeping `≥ 2^63` as `.big`. -/
def ofDecimal (s : String) : Option SlowNat :=
  (BigNat.ofDecimal s).map fromLimbs

/-! ## Entrypoint Manifest (for `IxCC.BigNat.Bootstrap`) -/

/-- Canonical Lean constant names of all monomorphic slow-path runtime entrypoints
frozen into the Wave 3b `BigNat` runtime library closure. -/
def entryConstNames : List String :=
  [ "IxCC.BigNat.Entry.add"
  , "IxCC.BigNat.Entry.sub"
  , "IxCC.BigNat.Entry.pred"
  , "IxCC.BigNat.Entry.mul"
  , "IxCC.BigNat.Entry.divMod"
  , "IxCC.BigNat.Entry.div"
  , "IxCC.BigNat.Entry.mod"
  , "IxCC.BigNat.Entry.pow"
  , "IxCC.BigNat.Entry.pow?"
  , "IxCC.BigNat.Entry.gcd"
  , "IxCC.BigNat.Entry.cmp"
  , "IxCC.BigNat.Entry.beq"
  , "IxCC.BigNat.Entry.ble"
  , "IxCC.BigNat.Entry.blt"
  , "IxCC.BigNat.Entry.land"
  , "IxCC.BigNat.Entry.lor"
  , "IxCC.BigNat.Entry.xor"
  , "IxCC.BigNat.Entry.shiftLeft"
  , "IxCC.BigNat.Entry.shiftLeft?"
  , "IxCC.BigNat.Entry.shiftRight"
  , "IxCC.BigNat.Entry.shiftRightSlow"
  , "IxCC.BigNat.Entry.log2"
  , "IxCC.BigNat.Entry.log2Slow"
  , "IxCC.BigNat.Entry.toDecimal"
  , "IxCC.BigNat.Entry.ofDecimal"
  , "IxCC.BigNat.Entry.fromUInt64"
  , "IxCC.BigNat.Entry.fromLimbs"
  , "IxCC.BigNat.Entry.ofTaggedWord"
  , "IxCC.BigNat.Entry.toTaggedWord?"
  ]

end IxCC.BigNat.Entry
