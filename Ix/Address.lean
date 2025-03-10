import Lean
import Ix.ByteArray
import Ix.Common
import Blake3

deriving instance Lean.ToExpr for ByteArray

structure Address where
  hash : ByteArray
  deriving Inhabited, Lean.ToExpr, BEq, Hashable

def Address.ofChars (_adrChars : List Char) : Option Address :=
  some default -- TODO

def Address.ofString (adrStr: String) : Option Address :=
  Address.ofChars adrStr.data

def Address.blake3 (x: ByteArray) : Address := ⟨(Blake3.hash x).val⟩

open Lean

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

instance : ToString Address where
  toString adr := byteArrayToHex adr.hash

instance : Repr Address where
  reprPrec a _ := "#" ++ (toString a).toFormat

instance : Ord Address where
  compare a b := compare a.hash.data.toList b.hash.data.toList

