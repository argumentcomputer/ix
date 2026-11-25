import IxCC.BigNat
import IxCC.Nat.Rep

/-! # The library's entries over `Nat` (`IxCC.BigNat.NatEntry`)

Design note: `plans/ONE-PIPELINE.md`, section 4.3 (decision D4).

Each entry is a plain function over `Nat`: it reaches limbs through the two representation
primitives of `IxCC.Nat.Rep` (`toLimbs`, `ofLimbs`) and otherwise only calls the limb-level
algorithm of `IxCC.BigNat`. Nothing here mentions a cell, a tag or a small/big case split: an
entry is the slow path of one `Nat` primitive, called natively when an operand is a limb cell or
a result leaves the tagged range, and its contract is the equation with the `Nat` operation
(`IxCC.BigNat.Proof.NatEntry`: `add a b = a + b`, and so on, without side condition).

An entry applies no `Nat` operation to an operand except through `toLimbs`; the exponent of
`pow` and the count of the shifts are passed to the limb-level algorithm as the naturals they
are, so those algorithms' arithmetic on the count is ordinary `Nat` arithmetic and is exact for
every count.

These replace the entries over `SlowNat` (`IxCC.BigNat.Entry`), which stay only for the frozen
`--bignat` side path and are to be removed with it.
-/

set_option autoImplicit false

namespace IxCC.BigNat.NatEntry

open IxCC.NatRep (toLimbs ofLimbs)

/-! ## Arithmetic -/

/-- Slow path of `Nat.add`. -/
def add (a b : Nat) : Nat :=
  ofLimbs (BigNat.add (toLimbs a) (toLimbs b))

/-- Slow path of truncating `Nat.sub`. -/
def sub (a b : Nat) : Nat :=
  ofLimbs (BigNat.subRaw (toLimbs a) (toLimbs b))

/-- Slow path of `Nat.pred`. -/
def pred (a : Nat) : Nat :=
  ofLimbs (BigNat.pred (toLimbs a))

/-- Slow path of `Nat.mul`. -/
def mul (a b : Nat) : Nat :=
  ofLimbs (BigNat.mul (toLimbs a) (toLimbs b))

/-- Slow path of `Nat.div` (`a / 0 = 0`). -/
def div (a b : Nat) : Nat :=
  ofLimbs (BigNat.div (toLimbs a) (toLimbs b))

/-- Slow path of `Nat.mod` (`a % 0 = a`). -/
def mod (a b : Nat) : Nat :=
  ofLimbs (BigNat.mod (toLimbs a) (toLimbs b))

/-- Slow path of `Nat.pow`. -/
def pow (a e : Nat) : Nat :=
  ofLimbs (BigNat.pow (toLimbs a) e)

/-- Slow path of `Nat.gcd`. -/
def gcd (a b : Nat) : Nat :=
  ofLimbs (BigNat.gcd (toLimbs a) (toLimbs b))

/-! ## Comparisons -/

/-- Three-way comparison. -/
def cmp (a b : Nat) : Ordering :=
  BigNat.cmp (toLimbs a) (toLimbs b)

/-- Slow path of `Nat.beq`. -/
def beq (a b : Nat) : Bool :=
  BigNat.beq (toLimbs a) (toLimbs b)

/-- Slow path of `Nat.ble`. -/
def ble (a b : Nat) : Bool :=
  BigNat.ble (toLimbs a) (toLimbs b)

/-- Slow path of `Nat.blt`. -/
def blt (a b : Nat) : Bool :=
  BigNat.blt (toLimbs a) (toLimbs b)

/-! ## Bitwise operations and shifts -/

/-- Slow path of `Nat.land`. -/
def land (a b : Nat) : Nat :=
  ofLimbs (BigNat.land (toLimbs a) (toLimbs b))

/-- Slow path of `Nat.lor`. -/
def lor (a b : Nat) : Nat :=
  ofLimbs (BigNat.lor (toLimbs a) (toLimbs b))

/-- Slow path of `Nat.xor`. -/
def xor (a b : Nat) : Nat :=
  ofLimbs (BigNat.xor (toLimbs a) (toLimbs b))

/-- Slow path of `Nat.shiftLeft`. -/
def shiftLeft (a s : Nat) : Nat :=
  ofLimbs (BigNat.shiftLeft (toLimbs a) s)

/-- Slow path of `Nat.shiftRight`. -/
def shiftRight (a s : Nat) : Nat :=
  ofLimbs (BigNat.shiftRight (toLimbs a) s)

/-- Slow path of `Nat.log2` (`log2 0 = 0`). -/
def log2 (a : Nat) : Nat :=
  BigNat.log2 (toLimbs a)

/-! ## Decimal conversion -/

/-- The decimal digits of a natural, most significant first (`"0"` for `0`). -/
def toDecimal (a : Nat) : String :=
  BigNat.toDecimal (toLimbs a)

/-- Parse a non-empty string of ASCII decimal digits; `none` on anything else. -/
def ofDecimal (s : String) : Option Nat :=
  (BigNat.ofDecimal s).map ofLimbs

/-! ## Manifest -/

/-- The Lean constant names of the entries over `Nat`, and of the two representation
primitives they are written over. -/
def entryConstNames : List String :=
  [ "IxCC.BigNat.NatEntry.add"
  , "IxCC.BigNat.NatEntry.sub"
  , "IxCC.BigNat.NatEntry.pred"
  , "IxCC.BigNat.NatEntry.mul"
  , "IxCC.BigNat.NatEntry.div"
  , "IxCC.BigNat.NatEntry.mod"
  , "IxCC.BigNat.NatEntry.pow"
  , "IxCC.BigNat.NatEntry.gcd"
  , "IxCC.BigNat.NatEntry.cmp"
  , "IxCC.BigNat.NatEntry.beq"
  , "IxCC.BigNat.NatEntry.ble"
  , "IxCC.BigNat.NatEntry.blt"
  , "IxCC.BigNat.NatEntry.land"
  , "IxCC.BigNat.NatEntry.lor"
  , "IxCC.BigNat.NatEntry.xor"
  , "IxCC.BigNat.NatEntry.shiftLeft"
  , "IxCC.BigNat.NatEntry.shiftRight"
  , "IxCC.BigNat.NatEntry.log2"
  , "IxCC.BigNat.NatEntry.toDecimal"
  , "IxCC.BigNat.NatEntry.ofDecimal"
  ]

/-- The two representation primitives (`IxCC.Nat.Rep`). -/
def repConstNames : List String :=
  [ "IxCC.NatRep.toLimbs", "IxCC.NatRep.ofLimbs" ]

end IxCC.BigNat.NatEntry
