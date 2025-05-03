import Ix.Common
import Ix.IR

import LSpec.SlimCheck.Gen
import LSpec

import Tests.Common
import Tests.Ix.Common

open LSpec
open SlimCheck
open SlimCheck.Gen

namespace Ix

def genLevel : Gen Ix.Level := getSize >>= go
  where
    go : Nat -> Gen Ix.Level
    | 0 => return .zero
    | Nat.succ f =>
      frequency [
        (100, return .zero),
        (100, .param <$> genName <*> genNatUSize),
        (50, .succ <$> go f),
        (25, .max <$> go f <*> go f),
        (25, .imax <$> go f <*> go f)
      ]

instance : Shrinkable Ix.Level where
  shrink _ := []

instance : SampleableExt Ix.Level := SampleableExt.mkSelfContained genLevel

def genExpr : Gen Ix.Expr := getSize >>= go
  where
    go : Nat -> Gen Ix.Expr
    | 0 => return .lit (.natVal 0)
    | Nat.succ f =>
      frequency [
        (100, .var <$> genNatUSize),
        (100, .sort <$> genLevel),
        (50, .const <$> genName <*> genAddress <*> genAddress <*> resizeListOf genLevel),
        (50, .rec_ <$> genName <*> genNat' <*> resizeListOf genLevel),
        (50, .app <$> go f <*> go f),
        (50, .lam <$> genName <*> genBinderInfo <*> go f <*> go f),
        (50, .pi <$> genName <*> genBinderInfo <*> go f <*> go f),
        (25, .letE <$> genName <*> go f <*> go f <*> go f <*> pure .true),
        (25, .letE <$> genName <*> go f <*> go f <*> go f <*> pure .false),
        (100, .lit <$> .strVal <$> genString),
        (100, .lit <$> .natVal <$> chooseAny Nat),
        (25, .proj <$> genName <*> genAddress <*> genAddress <*> genNat' <*> go f),
      ]

instance : Shrinkable Ix.Expr where
  shrink _ := []

instance : SampleableExt Ix.Expr := SampleableExt.mkSelfContained genExpr

def genConst : Gen Ix.Const := getSize >>= go
  where
    genNames : Gen (List Lean.Name) := resizeListOf genName
    genDef : Gen Ix.Definition := do
      let lvls <- genNames
      let type <- genExpr
      let mode <- genDefMode
      let value <- genExpr
      let hints <- genReducibilityHints
      let isPartial <- genBool
      let all <- genNames
      return ⟨lvls, type, mode, value, hints, isPartial, all⟩
    genCtor : Gen Ix.Constructor := 
      .mk <$> genName <*> genNames <*> genExpr <*> genNat' <*> genNat' <*> genNat'
    genRecr : Gen Ix.Recursor := 
      .mk <$> genName <*> genNames <*> genExpr <*> genNat' <*> genNat' <*> genNat' <*> genNat'
        <*> resizeListOf (.mk <$> genName <*> genNat' <*> genExpr)
        <*> genBool
    genInd : Gen Ix.Inductive := do
      let lvls <- genNames
      let type <- genExpr
      let params <- genNat'
      let indices <- genNat'
      let all <- genNames
      let ctors <- resizeListOf genCtor
      let recrs <- resizeListOf genRecr
      let nested <- genNat'
      let (isRec, isRefl) <- Prod.mk <$> genBool <*> genBool
      return ⟨lvls, type, params, indices, all, ctors, recrs, nested, isRec, isRefl⟩
    genMutDef : Gen Ix.MutualDefinitionBlock := do
      let nns <- resizeListOf (genListSize genName 1 5)
      let ds <- nns.mapM fun ns => do
        let x <- genDef
        ns.mapM (fun _ => pure x)
      return .mk ds nns
    go : Nat -> Gen Ix.Const
    | 0 => return .«axiom» (.mk [] (Ix.Expr.sort (Ix.Level.zero)))
    | Nat.succ _ =>
      frequency [
        (100, .«axiom» <$> (.mk <$> genNames <*> genExpr)),
        (100, .«definition» <$> genDef),
        (100, .quotient <$> (.mk <$> genNames <*> genExpr <*> genQuotKind)),
        (100, .inductiveProj <$> (.mk <$> genAddress <*> genAddress <*> genNat')),
        (100, .constructorProj <$> (.mk <$> genAddress <*> genAddress <*> genNat' <*> genNat')),
        (100, .recursorProj <$> (.mk <$> genAddress <*> genAddress <*> genNat' <*> genNat')),
        (100, .definitionProj <$> (.mk <$> genAddress <*> genAddress <*> genNat')),
        (100, .mutDefBlock <$> genMutDef),
        (100, .mutIndBlock <$> resizeListOf genInd),
      ]

instance : Shrinkable Ix.Const where
  shrink _ := []

instance : SampleableExt Ix.Const := SampleableExt.mkSelfContained genConst

end Ix
