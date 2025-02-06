import Lean

structure Address where
  adr : ByteArray
  deriving Inhabited

open Lean

instance : ToExpr ByteArray where
  toExpr x   := mkApp (mkConst ``ByteArray.mk) (toExpr x.data)
  toTypeExpr := mkConst ``ByteArray

instance : ToExpr Address where
  toExpr x   := mkApp (mkConst ``Address.mk) (toExpr x.adr)
  toTypeExpr := mkConst ``Address
