import Ix.IR

import LSpec.SlimCheck.Gen
import LSpec

import Tests.Common
import Tests.Ix.Common

open LSpec
open SlimCheck
open SlimCheck.Gen

namespace Ix

def genUniv : Gen Ix.Univ := getSize >>= go
  where
    go : Nat -> Gen Ix.Univ
    | 0 => return .zero
    | Nat.succ f =>
      frequency [
        (100, return .zero),
        (100, .var <$> genName <*> genNatUSize),
        (50, .succ <$> go f),
        (25, .max <$> go f <*> go f),
        (25, .imax <$> go f <*> go f)
      ]

instance : Shrinkable Ix.Univ where
  shrink _ := []

instance : SampleableExt Ix.Univ := SampleableExt.mkSelfContained genUniv

def genExpr : Gen Ix.Expr := getSize >>= go
  where
    go : Nat -> Gen Ix.Expr
    | 0 => return .lit (.natVal 0)
    | Nat.succ f =>
      frequency [
        (100, .var <$> genNatUSize),
        (100, .sort <$> genUniv),
        (50, .const <$> genName <*> genAddress <*> genAddress <*> resizeListOf genUniv),
        (50, .rec_ <$> genNat' <*> resizeListOf genUniv),
        (50, .app <$> go f <*> go f),
        (50, .lam <$> genName <*> genBinderInfo <*> go f <*> go f),
        (50, .pi <$> genName <*> genBinderInfo <*> go f <*> go f),
        (25, .letE <$> genName <*> go f <*> go f <*> go f <*> pure .true),
        (25, .letE <$> genName <*> go f <*> go f <*> go f <*> pure .false),
        (25, .lit <$> .strVal <$> genString),
        (25, .lit <$> .natVal <$> chooseAny Nat),
        (25, .proj <$> genName <*> genAddress <*> genNat' <*> go f),
      ]

instance : Shrinkable Ix.Expr where
  shrink _ := []

instance : SampleableExt Ix.Expr := SampleableExt.mkSelfContained genExpr

end Ix
