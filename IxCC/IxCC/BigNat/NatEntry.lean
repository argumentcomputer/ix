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

## Internal quantities (a statement, not proved)

Compiled through the pipeline, every `Nat` operation inside the library has a fast path and a
cold slow-path call back into these entries; the call is correct if taken (design note 4.5), so
nothing below is needed for `NatLib.Spec`. It is what would make the cold calls unreachable.
The lemma would be about the library's image `L` at `Fir`, with an instrumented run that
records each `Nat` primitive it executes: for every entry and literal arguments with

* every operand that goes through `toLimbs` below `2^(64·2^57)`, i.e. fewer than `2^57` limbs
  (`IxCC.NatRep.size_toLimbs_le_iff`), and likewise the result (`mul`: the sum of the limb
  counts; `pow`: the base's limb count times the exponent; `shiftLeft`: the limb count plus
  `s / 64 + 1`), and
* the count of `shiftLeft`, `shiftRight` and the exponent of `pow` below `2^63`,

every operand and result of every executed `Nat` primitive is below `2^63` (indices and loop
bounds are at most a limb count plus one, `log2` is below `64·2^57 = 2^63`, the decimal fuels
are linear in the limb count). Proving it needs that instrumented semantics; per loop it is
the observation that each index is bounded by a limb count. The first condition holds for any
operand in memory (x86-64 user space is below `2^47` bytes, `2^44` limbs). The second does not:
`shiftRight a (2^64)` and `pow 1 (2^64)` have small results and operands of two limbs, but
`BigNat.shiftRight` and `BigNat.pow` compute `s == 0`, `s / 64`, `s % 64`, `e == 0` on the count
itself, so those slow paths are reachable (and correct). A clamp of the count in these two
entries would remove them: a count of at least `2^63` gives `0` for `shiftRight` of any operand
in memory, `0` or `1` for `pow` of `0` or `1`, and otherwise a result that does not fit in
memory.
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
