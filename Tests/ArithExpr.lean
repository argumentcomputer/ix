import LSpec
import Tests.Common
import Ix.Unsigned
import Ix.Binius.ArithExpr

open LSpec SlimCheck Gen

open Binius

def genOracleId : Gen OracleId :=
  OracleId.mk <$> genUSize

def genArithExpr : Gen ArithExpr := getSize >>= go
  where
    go : Nat → Gen ArithExpr
    | 0 => return .const 0
    | Nat.succ n =>
      frequency [
        (40, .const <$> genUInt128),
        (40, .var <$> genOracleId),
        (25, .add <$> go n <*> go n),
        (25, .mul <$> go n <*> go n),
        (50, .pow <$> go n <*> genUInt64)
      ]

instance : Shrinkable ArithExpr where
  shrink _ := []

instance : Repr ArithExpr where
  reprPrec expr _ := expr.toString

instance : SampleableExt ArithExpr := SampleableExt.mkSelfContained genArithExpr

def Tests.ArithExpr.suite := [
    check "ArithExpr Lean->Rust mapping matches the deserialized bytes"
      (∀ expr : ArithExpr, expr.isEquivalentToBytes expr.toBytes),
  ]
