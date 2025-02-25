import LSpec
import Ix.Ixon
import Ix.Ixon.Univ
import LSpec.SlimCheck.Gen
import LSpec

import Tests.Ixon.Gen.Common
import Tests.Ixon.Gen.Univ

open LSpec
open SlimCheck
open SlimCheck.Gen
open Ixon

def genExpr : SlimCheck.Gen Ixon.Expr := getSize >>= go
  where
    go : Nat -> SlimCheck.Gen Ixon.Expr
    | 0 => return .vari 0
    | Nat.succ f =>
      frequency [
        (100, .vari <$> genUInt64),
        (100, .sort <$> genUniv),
        (100, .cnst <$> genAddress <*> resizeListOf genUniv),
        (100, .rec_ <$> genUInt64 <*> resizeListOf genUniv),
        (30, .apps <$> go f <*> go f <*> resizeListOf (go f)),
        (30, .lams <$> resizeListOf (go f) <*> go f),
        (30, .alls <$> resizeListOf (go f) <*> go f),
        (30, .let_ <$> go f <*> go f <*> go f),
        (50, .proj <$> genUInt64 <*> go f),
        (100, .strl <$> genString),
        (100, .natl <$> chooseAny Nat)
      ]

-- TODO: useful shrinking
instance : Shrinkable Expr where
  shrink _ := []

instance : SampleableExt Expr := SampleableExt.mkSelfContained genExpr
