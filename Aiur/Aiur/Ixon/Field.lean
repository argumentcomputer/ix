module
public import Aiur.Ixon

/-! Scalar encodings for compiled artifacts. Structural counts and indices
remain ordinary TagN integers. Wide scalars are a count followed by zero to
four little-endian UInt64 limbs, each encoded with TagN. -/

public section
namespace Aiur.Ixon

inductive FieldEncoding where
  | narrow
  | wide
  deriving Repr, BEq, DecidableEq

/-- The minimal little-endian limb sequence of an unsigned 256-bit integer. -/
def putWideNat (value : Nat) : PutM Unit := do
  unless value < 2 ^ 256 do throw s!"field integer {value} exceeds 256 bits"
  let limbs := ((List.range 4).map fun i => (value / 2 ^ (64 * i)) % 2 ^ 64).reverse
    |>.dropWhile (· == 0) |>.reverse
  nat limbs.length
  for limb in limbs do nat limb

/-- A canonical unsigned 256-bit integer; zero has no limbs. -/
def getWideNat : GetM Nat := do
  let count ← getNat
  unless count ≤ 4 do fail s!"field integer has {count} limbs, expected at most four"
  let mut value := 0
  let mut high := 0
  for i in [0:count] do
    let limb ← getNat
    value := value + limb * 2 ^ (64 * i)
    high := limb
  if count > 0 && high == 0 then fail "field integer has a leading zero limb"
  return value

def FieldEncoding.put (encoding : FieldEncoding) (value : Nat) : PutM Unit :=
  match encoding with
  | .narrow => nat value
  | .wide => putWideNat value

/-- Encoding checks the modulus range; primality belongs to field selection. -/
def FieldEncoding.putModulus (encoding : FieldEncoding) (modulus : Nat) : PutM Unit := do
  match encoding with
  | .narrow =>
      if modulus < 2 || modulus ≥ 2 ^ 64 then
        throw "execution requires a prime modulus fitting UInt64"
  | .wide =>
      if modulus < 2 || modulus ≥ 2 ^ 256 then
        throw "wide artifact modulus must be in [2, 2^256)"
  encoding.put modulus

/-- Wide artifacts carry canonical field representatives. The narrow writer
retains the version-two encoding and its existing UInt64 range check. -/
def FieldEncoding.putScalar (encoding : FieldEncoding) (modulus value : Nat) : PutM Unit := do
  if encoding == .wide && value ≥ modulus then
    throw s!"field integer {value} is not below modulus {modulus}"
  encoding.put value

end Aiur.Ixon

end
