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

--def genLevel : Gen Ix.Level := getSize >>= go
--  where
--    go : Nat -> Gen Ix.Level
--    | 0 => return .zero
--    | Nat.succ f =>
--      frequency [
--        (100, return .zero),
--        (100, .param <$> genName <*> genNat),
--        (50, .succ <$> go f),
--        (25, .max <$> go f <*> go f),
--        (25, .imax <$> go f <*> go f)
--      ]
--
--instance : Shrinkable Ix.Level where
--  shrink _ := []
--
--instance : SampleableExt Ix.Level := SampleableExt.mkSelfContained genLevel
--
--def genExpr : Gen Ix.Expr := getSize >>= go
--  where
--    go : Nat -> Gen Ix.Expr
--    | 0 => return .lit (.natVal 0)
--    | Nat.succ f =>
--      frequency [
--        (100, .var <$> genNat),
--        (100, .sort <$> genLevel),
--        (50, .const <$> genName <*> genAddress <*> genAddress <*> genList genLevel),
--        (50, .rec_ <$> genName <*> genNat <*> genList genLevel),
--        (50, .app <$> go f <*> go f),
--        (50, .lam <$> genName <*> genBinderInfo <*> go f <*> go f),
--        (50, .pi <$> genName <*> genBinderInfo <*> go f <*> go f),
--        (25, .letE <$> genName <*> go f <*> go f <*> go f <*> pure .true),
--        (25, .letE <$> genName <*> go f <*> go f <*> go f <*> pure .false),
--        (100, .lit <$> .strVal <$> genString),
--        (100, .lit <$> .natVal <$> chooseAny Nat),
--        (25, .proj <$> genName <*> genAddress <*> genAddress <*> genNat <*> go f),
--      ]
--
--instance : Shrinkable Ix.Expr where
--  shrink _ := []
--
--instance : SampleableExt Ix.Expr := SampleableExt.mkSelfContained genExpr
--
--def genConst : Gen Ix.Const := getSize >>= go
--  where
--    genNames : Gen (List Lean.Name) := genList genName
--    genDef : Gen Ix.Definition := do
--      let n <- genName
--      let lvls <- genNames
--      let type <- genExpr
--      let mode <- genDefKind
--      let value <- genExpr
--      let hints <- genReducibilityHints
--      let safety <- oneOf #[pure .safe, pure .partial, pure .unsafe]
--      let all <- genNames
--      return ⟨n, lvls, type, mode, value, hints, safety, all⟩
--    genCtor : Gen Ix.Constructor := 
--      .mk <$> genName <*> genNames <*> genExpr <*> genNat <*> genNat <*> genNat <*> genBool
--    genRecr : Gen Ix.Recursor := 
--      .mk <$> genName <*> genNames <*> genExpr <*> genNat <*> genNat <*> genNat <*> genNat
--        <*> genList (.mk <$> genName <*> genNat <*> genExpr)
--        <*> genBool <*> genBool
--    genInd : Gen Ix.Inductive := do
--      let n <- genName
--      let lvls <- genNames
--      let type <- genExpr
--      let params <- genNat
--      let indices <- genNat
--      let all <- genNames
--      let ctors <- genList genCtor
--      let recrs <- genList genRecr
--      let nested <- genNat
--      let (isRec, isRefl, isUnsafe) <- (·,·,·) <$> genBool <*> genBool <*> genBool
--      return ⟨n, lvls, type, params, indices, all, ctors, recrs, nested, isRec, isRefl, isUnsafe⟩
--    genMutDef : Gen Ix.MutualBlock := do
--      let nns <- genList (genListSize genName 1 5)
--      let ds <- nns.mapM fun ns => do
--        let x <- genDef
--        ns.mapM (fun _ => pure x)
--      return .mk ds
--    genMutInd : Gen Ix.InductiveBlock := do
--      let nns <- genList (genListSize genName 1 5)
--      let ds <- nns.mapM fun ns => do
--        let x <- genInd
--        ns.mapM (fun _ => pure x)
--      return .mk ds
--    go : Nat -> Gen Ix.Const
--    | 0 => return .«axiom» (.mk .anonymous [] (Ix.Expr.sort (Ix.Level.zero)) false)
--    | Nat.succ _ =>
--      frequency [
--        (100, .«axiom» <$> (.mk <$> genName <*> genNames <*> genExpr <*> genBool)),
--        (100, .«definition» <$> genDef),
--        (100, .quotient <$> (.mk <$> genName <*> genNames <*> genExpr <*> genQuotKind)),
--        (100, .inductiveProj <$> (.mk <$> genName <*> genAddress <*> genAddress <*> genNat)),
--        (100, .constructorProj <$> (.mk <$> genName <*> genAddress <*> genAddress <*> genNat <*> genName <*> genNat)),
--        (100, .recursorProj <$> (.mk <$> genName <*> genAddress <*> genAddress <*> genNat <*> genName <*> genNat)),
--        (100, .definitionProj <$> (.mk <$> genName <*> genAddress <*> genAddress <*> genNat)),
--        (100, .mutual <$> genMutDef),
--        (100, .inductive <$> genMutInd),
--      ]
--
--instance : Shrinkable Ix.Const where
--  shrink _ := []
--
--instance : SampleableExt Ix.Const := SampleableExt.mkSelfContained genConst
--
--end Ix
