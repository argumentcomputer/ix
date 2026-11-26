/-
  Basic type generators for testing.
  Generators and test types for property-based FFI roundtrip tests.
-/
module

public import LSpec
public import Std.Data.HashMap

public section

open LSpec LSpec.Prop Gen

/-! ## Helper combinators -/

def genUInt8 : Gen UInt8 :=
  Gen.chooseUInt8

def genUInt32 : Gen UInt32 :=
  Gen.chooseUInt32

def genUInt64 : Gen UInt64 :=
  Gen.chooseUInt64

def genUSize : Gen USize :=
  .ofNat <$> Gen.chooseNat 0 (2^System.Platform.numBits - 1)

def frequency' (default : Gen α) (xs : List (Nat × Gen α)) : Gen α :=
  Gen.frequency xs.toArray default

def frequency [Inhabited α] (xs : List (Nat × Gen α)) : Gen α :=
  Gen.frequency xs.toArray (pure default)

def oneOf' [Inhabited α] (xs : List (Gen α)) : Gen α :=
  Gen.oneOf! xs.toArray

/-! ## Basic type generators -/

/-- Generate Nats across the full range: small, medium, large, and huge -/
def genNat : Gen Nat := do
  let choice ← Gen.chooseNat 0 100
  if choice < 50 then
    -- 50%: small nats (0-1000)
    Gen.chooseNat 0 1000
  else if choice < 75 then
    -- 25%: medium nats (up to 2^32)
    Gen.chooseNat 0 (2^32)
  else if choice < 90 then
    -- 15%: large nats (up to 2^64)
    Gen.chooseNat 0 (2^64)
  else
    -- 10%: huge nats (up to 2^256)
    Gen.chooseNat 0 (2^256)

def genSmallNat : Gen Nat := Gen.chooseNat 0 1000

def genString : Gen String := do
  let len ← Gen.chooseNat 0 100
  let chars ← Gen.listOf (Gen.chooseNat 32 126 >>= fun n => pure (Char.ofNat n))
  pure (String.ofList (chars.take len))

def genListNat : Gen (List Nat) := do
  let len ← Gen.chooseNat 0 20
  let mut result := []
  for _ in [:len] do
    result := (← genSmallNat) :: result
  pure result.reverse

def genArrayNat : Gen (Array Nat) := do
  let list ← genListNat
  pure list.toArray

def genByteArray : Gen ByteArray := do
  let len ← Gen.chooseNat 0 100
  let mut bytes := ByteArray.emptyWithCapacity len
  for _ in [:len] do
    let b ← Gen.chooseNat 0 255
    bytes := bytes.push b.toUInt8
  pure bytes

def genBool : Gen Bool := Gen.bool

def genHashMapNatNat : Gen (Std.HashMap Nat Nat) := do
  let len ← Gen.chooseNat 0 20
  let mut map : Std.HashMap Nat Nat := {}
  for _ in [:len] do
    let k ← genSmallNat
    let v ← genSmallNat
    map := map.insert k v
  pure map

/-! ## FormatValue / Shrinkable / Sampleable instances -/

instance : Repr ByteArray where
  reprPrec ba _ := s!"ByteArray#{ba.toList}"

instance : FormatValue (Std.HashMap Nat Nat) where
  formatValue m := reprStr m.toList

instance : Shrinkable (Std.HashMap Nat Nat) where
  shrink m :=
    let list := m.toList
    match list with
    | [] => []
    | _ :: tail => [Std.HashMap.ofList tail]

instance : Sampleable (Std.HashMap Nat Nat) := ⟨genHashMapNatNat⟩

end
