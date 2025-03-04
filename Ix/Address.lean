import Lean

deriving instance Lean.ToExpr for ByteArray

structure Address where
  hash : ByteArray
  deriving Inhabited, Lean.ToExpr

instance : ToString Address where
  toString adr := toString adr.hash -- TODO

def Address.ofChars (_adrChars : List Char) : Option Address :=
  some default -- TODO

def Address.ofString (adrStr: String) : Option Address :=
  Address.ofChars adrStr.data
