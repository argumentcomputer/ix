import Lean
import Ix.ByteArray

structure Address where
  adr : ByteArray
  deriving Inhabited, BEq

open Lean

instance : ToExpr ByteArray where
  toExpr x   := mkApp (mkConst ``ByteArray.mk) (toExpr x.data)
  toTypeExpr := mkConst ``ByteArray

instance : ToExpr Address where
  toExpr x   := mkApp (mkConst ``Address.mk) (toExpr x.adr)
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
  reprPrec a _ := "#" ++ String.toFormat (byteArrayToHex a.adr)

