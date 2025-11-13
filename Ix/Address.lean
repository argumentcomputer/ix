import Lean
import Ix.ByteArray
import Ix.Common
import Blake3

deriving instance Lean.ToExpr for ByteArray
deriving instance Repr for ByteArray

structure Address where
  hash : ByteArray
  deriving Inhabited, Lean.ToExpr, BEq, Hashable

def Address.blake3 (x: ByteArray) : Address := ⟨(Blake3.hash x).val⟩

def hexOfNat : Nat -> Option Char
| 0 => .some '0'
| 1 => .some '1'
| 2 => .some '2'
| 3 => .some '3'
| 4 => .some '4'
| 5 => .some '5'
| 6 => .some '6'
| 7 => .some '7'
| 8 => .some '8'
| 9 => .some '9'
| 10 => .some 'a'
| 11 => .some 'b'
| 12 => .some 'c'
| 13 => .some 'd'
| 14 => .some 'e'
| 15 => .some 'f'
|  _ => .none

def natOfHex : Char -> Option Nat
| '0' => .some 0
| '1' => .some 1
| '2' => .some 2
| '3' => .some 3
| '4' => .some 4
| '5' => .some 5
| '6' => .some 6
| '7' => .some 7
| '8' => .some 8
| '9' => .some 9
| 'a' => .some 10
| 'b' => .some 11
| 'c' => .some 12
| 'd' => .some 13
| 'e' => .some 14
| 'f' => .some 15
| 'A' => .some 10
| 'B' => .some 11
| 'C' => .some 12
| 'D' => .some 13
| 'E' => .some 14
| 'F' => .some 15
|  _ => .none

/-- Convert a byte (UInt8) to a two‐digit big-endian hexadecimal string. -/
def hexOfByte (b : UInt8) : String :=
  let hi := hexOfNat (UInt8.toNat (b >>> 4))
  let lo := hexOfNat (UInt8.toNat (b &&& 0xF))
  String.mk [hi.get!, lo.get!]

/-- Convert a ByteArray to a big-endian hexadecimal string. -/
def hexOfBytes (ba : ByteArray) : String :=
  (ba.toList.map hexOfByte).foldl (· ++ ·) ""

instance : ToString Address where
  toString adr := hexOfBytes adr.hash

instance : Repr Address where
  reprPrec a _ := "#" ++ (toString a).toFormat

instance : Ord Address where
  compare a b := compare a.hash.data.toList b.hash.data.toList

instance : Inhabited Address where
  default := Address.blake3 ⟨#[]⟩

def byteOfHex : Char -> Char -> Option UInt8
| hi, lo => do
  let hi <- natOfHex hi
  let lo <- natOfHex lo
  UInt8.ofNat (hi <<< 4 + lo)

def bytesOfHex (s: String) : Option ByteArray := do
  let bs <- go s.toList
  return ⟨bs.toArray⟩
  where
    go : List Char -> Option (List UInt8)
    | hi::lo::rest => do
      let b <- byteOfHex hi lo
      let bs <- go rest
      b :: bs
    | [] => return []
    | _ => .none

def Address.fromString (s: String) : Option Address := do
  let ba <- bytesOfHex s
  if ba.size == 32 then .some ⟨ba⟩ else .none

def Address.toUniqueName (addr: Address): Lean.Name :=
  .str (.str (.str .anonymous "Ix") "_#") (hexOfBytes addr.hash)

def Address.fromUniqueName (name: Lean.Name) : Option Address :=
  match name with
  | .str (.str (.str .anonymous "Ix") "_#") s => Address.fromString s
  | _ => .none

structure MetaAddress where
  data : Address
  «meta» : Address
  deriving Inhabited, Nonempty, Lean.ToExpr, BEq, Hashable, Repr, Ord

instance : ToString MetaAddress where
  toString adr := s!"{hexOfBytes adr.data.hash}:{hexOfBytes adr.meta.hash}"

