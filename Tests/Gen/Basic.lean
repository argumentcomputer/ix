/-
  Basic type generators for testing.
  Generators and test types for property-based FFI roundtrip tests.
-/

import LSpec
import Std.Data.HashMap

open LSpec SlimCheck Gen

/-! ## Helper combinators -/

def genUInt8 : Gen UInt8 :=
  UInt8.ofNat <$> choose Nat 0 0xFF

def genUInt32 : Gen UInt32 :=
  UInt32.ofNat <$> choose Nat 0 0xFFFFFFFF

def genUInt64 : Gen UInt64 :=
  UInt64.ofNat <$> choose Nat 0 0xFFFFFFFFFFFFFFFF

def genUSize : Gen USize :=
  .ofNat <$> choose Nat 0 (2^System.Platform.numBits - 1)

def frequency' (default: Gen α) (xs: List (Nat × Gen α)) : Gen α := do
  let n ← choose Nat 0 total
  pick n xs
  where
    total := List.sum (Prod.fst <$> xs)
    pick n xs := match xs with
    | [] => default
    | (k, x) :: xs => if n <= k then x else pick (n - k) xs

def frequency [Inhabited α] (xs: List (Nat × Gen α)) : Gen α :=
  frequency' xs.head!.snd xs

def oneOf' [Inhabited α] (xs: List (Gen α)) : Gen α :=
  frequency (xs.map (fun x => (100, x)))

/-! ## Basic type generators -/

/-- Generate Nats across the full range: small, medium, large, and huge -/
def genNat : Gen Nat := do
  let choice ← choose Nat 0 100
  if choice < 50 then
    -- 50%: small nats (0-1000)
    choose Nat 0 1000
  else if choice < 75 then
    -- 25%: medium nats (up to 2^32)
    choose Nat 0 (2^32)
  else if choice < 90 then
    -- 15%: large nats (up to 2^64)
    choose Nat 0 (2^64)
  else
    -- 10%: huge nats (up to 2^256)
    choose Nat 0 (2^256)

def genSmallNat : Gen Nat := choose Nat 0 1000

def genString : Gen String := do
  let len ← choose Nat 0 100
  let chars ← Gen.listOf (choose Nat 32 126 >>= fun n => pure (Char.ofNat n))
  pure (String.ofList (chars.take len))

def genListNat : Gen (List Nat) := do
  let len ← choose Nat 0 20
  let mut result := []
  for _ in [:len] do
    result := (← genSmallNat) :: result
  pure result.reverse

def genArrayNat : Gen (Array Nat) := do
  let list ← genListNat
  pure list.toArray

def genByteArray : Gen ByteArray := do
  let len ← choose Nat 0 100
  let mut bytes := ByteArray.emptyWithCapacity len
  for _ in [:len] do
    let b ← choose Nat 0 255
    bytes := bytes.push b.toUInt8
  pure bytes

def genBool : Gen Bool := choose Bool .false true

/-! ## Test struct generators -/

/-- A simple 2D point struct for FFI testing -/
structure Point where
  x : Nat
  y : Nat
deriving Repr, BEq, DecidableEq, Inhabited

def genPoint : Gen Point := do
  let x ← genSmallNat
  let y ← genSmallNat
  pure ⟨x, y⟩

/-- A simple binary tree of Nats for FFI testing -/
inductive NatTree where
  | leaf : Nat → NatTree
  | node : NatTree → NatTree → NatTree
deriving Repr, BEq, DecidableEq, Inhabited

/-- Generate a random NatTree with bounded depth -/
def genNatTree : Nat → Gen NatTree
  | 0 => do
    let n ← genSmallNat
    pure (.leaf n)
  | maxDepth + 1 => do
    let choice ← choose Nat 0 2
    if choice == 0 then
      let n ← genSmallNat
      pure (.leaf n)
    else
      let left ← genNatTree maxDepth
      let right ← genNatTree maxDepth
      pure (.node left right)

def genHashMapNatNat : Gen (Std.HashMap Nat Nat) := do
  let len ← choose Nat 0 20
  let mut map : Std.HashMap Nat Nat := {}
  for _ in [:len] do
    let k ← genSmallNat
    let v ← genSmallNat
    map := map.insert k v
  pure map

/-! ## Shrinkable instances -/

instance : Shrinkable Nat where
  shrink n := if n == 0 then [] else [n / 2]

instance : Shrinkable (List Nat) where
  shrink xs := match xs with
    | [] => []
    | _ :: tail => [tail]

instance : Shrinkable (Array Nat) where
  shrink arr := if arr.isEmpty then [] else [arr.pop]

instance : Repr ByteArray where
  reprPrec ba _ := s!"ByteArray#{ba.toList}"

instance : Shrinkable ByteArray where
  shrink ba := if ba.isEmpty then [] else [ba.extract 0 (ba.size - 1)]

instance : Shrinkable String where
  shrink s := if s.isEmpty then [] else [s.dropEnd 1 |>.toString]

instance : Shrinkable Point where
  shrink p := if p.x == 0 && p.y == 0 then [] else [⟨p.x / 2, p.y / 2⟩]

instance : Shrinkable NatTree where
  shrink t := match t with
    | .leaf n => if n == 0 then [] else [.leaf (n / 2)]
    | .node l r => [l, r]

instance : Shrinkable (Std.HashMap Nat Nat) where
  shrink m :=
    let list := m.toList
    match list with
    | [] => []
    | _ :: tail => [Std.HashMap.ofList tail]

/-! ## SampleableExt instances -/

instance : SampleableExt Nat := SampleableExt.mkSelfContained genNat

instance : SampleableExt (List Nat) := SampleableExt.mkSelfContained genListNat

instance : SampleableExt (Array Nat) := SampleableExt.mkSelfContained genArrayNat

instance : SampleableExt ByteArray := SampleableExt.mkSelfContained genByteArray

instance : SampleableExt String := SampleableExt.mkSelfContained genString

instance : SampleableExt Point := SampleableExt.mkSelfContained genPoint

instance : SampleableExt NatTree := SampleableExt.mkSelfContained (genNatTree 4)

instance : SampleableExt (Std.HashMap Nat Nat) := SampleableExt.mkSelfContained genHashMapNatNat
