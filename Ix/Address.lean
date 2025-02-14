import Lean

structure Address where
  hash : ByteArray
  deriving Inhabited

instance : ToString Address where
  toString adr := toString adr.hash -- TODO

def Address.ofChars (_adrChars : List Char) : Option Address :=
  some default -- TODO

def Address.ofString (adrStr: String) : Option Address :=
  Address.ofChars adrStr.data

open Lean

instance : ToExpr ByteArray where
  toExpr x   := mkApp (mkConst ``ByteArray.mk) (toExpr x.data)
  toTypeExpr := mkConst ``ByteArray

instance : ToExpr Address where
  toExpr x   := mkApp (mkConst ``Address.mk) (toExpr x.hash)
  toTypeExpr := mkConst ``Address
