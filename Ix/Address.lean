import Lean
import Ix.ByteArray
import Blake3

structure Address where
  hash : ByteArray
  deriving Inhabited, BEq, Hashable

instance : ToString Address where
  toString adr := toString adr.hash -- TODO

def Address.ofChars (_adrChars : List Char) : Option Address :=
  some default -- TODO

def Address.ofString (adrStr: String) : Option Address :=
  Address.ofChars adrStr.data

def Address.blake3 (x: ByteArray) : Address := ⟨(Blake3.hash x).val⟩

open Lean

instance : ToExpr ByteArray where
  toExpr x   := mkApp (mkConst ``ByteArray.mk) (toExpr x.data)
  toTypeExpr := mkConst ``ByteArray

instance : ToExpr Address where
  toExpr x   := mkApp (mkConst ``Address.mk) (toExpr x.hash)
  toTypeExpr := mkConst ``Address

/-- Convert a byte (UInt8) to a two‐digit hex string. -/
def byteToHex (b : UInt8) : String :=
  let hexDigits := 
    #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']
  let hi := hexDigits.get! (UInt8.toNat (b >>> 4))
  let lo := hexDigits.get! (UInt8.toNat (b &&& 0xF))
  String.mk [hi, lo]

/-- Convert a ByteArray to a hexadecimal string. -/
def byteArrayToHex (ba : ByteArray) : String :=
  (ba.toList.map byteToHex).foldl (· ++ ·) ""

instance : Repr Address where
  reprPrec a _ := "#" ++ String.toFormat (byteArrayToHex a.hash)

-- TODO: move to a utils namespace
def compareList [Ord α] : List α -> List α -> Ordering
| a::as, b::bs => match compare a b with
  | .eq => compareList as bs
  | x => x
| _::_, [] => .gt
| [], _::_ => .lt
| [], [] => .eq

instance [Ord α] : Ord (List α) where 
  compare := compareList

instance : Ord Address where
  compare a b := compare a.hash.data.toList b.hash.data.toList

