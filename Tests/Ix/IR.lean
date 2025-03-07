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
        (100, .lit <$> .strVal <$> genString),
        (100, .lit <$> .natVal <$> chooseAny Nat),
        (25, .proj <$> genName <*> genAddress <*> genNat' <*> go f),
      ]

instance : Shrinkable Ix.Expr where
  shrink _ := []

instance : SampleableExt Ix.Expr := SampleableExt.mkSelfContained genExpr

def genConst : Gen Ix.Const := getSize >>= go
  where
    genDef : Gen Ix.Definition := .mk <$> genNat' <*> genExpr <*> genExpr <*> genBool
    genCtor : Gen Ix.Constructor := 
      .mk <$> genNat' <*> genExpr <*> genNat' <*> genNat' <*> genNat'
    genRecr : Gen Ix.Recursor := 
      .mk <$> genNat' <*> genExpr <*> genNat' <*> genNat' <*> genNat' <*> genNat'
        <*> resizeListOf (.mk <$> genNat' <*> genExpr)
        <*> genBool <*> genBool
    genInd : Gen Ix.Inductive := 
      .mk <$> genNat' <*> genExpr <*> genNat' <*> genNat'
        <*> resizeListOf genCtor <*> resizeListOf genRecr
        <*> genBool <*> genBool <*> genBool <*> genBool
    go : Nat -> Gen Ix.Const
    | 0 => return .«axiom» (.mk 0 (Ix.Expr.sort (Ix.Univ.zero)))
    | Nat.succ f =>
      frequency [
        (100, .«axiom» <$> (.mk <$> genNat' <*> genExpr)),
        (100, .«theorem» <$> (.mk <$> genNat' <*> genExpr <*> genExpr)),
        (100, .«opaque» <$> (.mk <$> genNat' <*> genExpr <*> genExpr)),
        (100, .«definition» <$> genDef),
        (100, .quotient <$> (.mk <$> genNat' <*> genExpr <*> genQuotKind)),
        (100, .inductiveProj <$> (.mk <$> genAddress <*> genNat')),
        (100, .constructorProj <$> (.mk <$> genAddress <*> genNat' <*> genNat')),
        (100, .recursorProj <$> (.mk <$> genAddress <*> genNat' <*> genNat')),
        (100, .definitionProj <$> (.mk <$> genAddress <*> genNat')),
        (100, .mutDefBlock <$> resizeListOf genDef),
        (100, .mutIndBlock <$> resizeListOf genInd),
      ]

instance : Shrinkable Ix.Const where
  shrink _ := []

instance : SampleableExt Ix.Const := SampleableExt.mkSelfContained genConst

end Ix
