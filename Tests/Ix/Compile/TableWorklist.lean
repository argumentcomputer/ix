import LSpec
import Ix.CompileM

namespace Tests.Ix.Compile.TableWorklist

open LSpec
open _root_.Ix (Name Expr Level)
open _root_.Ix.CompileM

private def context : CompileEnv × BlockEnv :=
  ({ (default : CompileEnv) with pass3 := true },
    { all := {}, current := Name.fromLeanName `Tables, mutCtx := {}, univCtx := [] })

private def retained : Array (Name × Name) :=
  #[(Name.fromLeanName `Retained.below, Name.fromLeanName `Retained)]

private def initial : BlockState := { p3Heads := retained }

private def raw (action : CompileM α) (state : BlockState := initial) :
    Except CompileError α × BlockState := (action context).run state

private def resourceFailure (result : Except CompileError α) : Bool :=
  match result with
  | .error (.resourceLimit _) => true
  | _ => false

private def expressionCollision (collide : Bool) : Bool := Id.run do
  let u := Name.fromLeanName `u
  let v := Name.fromLeanName `v
  let first := Expr.mkSort (Level.mkParam u)
  let second := if collide then Expr.sort (Level.mkParam v) first.getHash else Expr.mkSort (Level.mkParam v)
  let env := (context.1, { context.2 with univCtx := [u, v] })
  let (seeded, state) := (preseedExprTables #[(first, [u, v]), (second, [u, v])] env).run initial
  let (compiled, after) := (compileExpr second env).run state
  return seeded.isOk && state.univs == #[.var 0, .var 1] &&
    compiled.toOption.map (·.1) == some (.sort 1) && after.univs == state.univs && after.univsFinal

private def contextCollision (collide : Bool) : Bool := Id.run do
  let u := Name.fromLeanName `u
  let v := if collide then Name.str Name.mkAnon "v" u.getHash else Name.fromLeanName `v
  let expression := Expr.mkSort (Level.mkParam u)
  let env := (context.1, { context.2 with univCtx := [v, u] })
  let (seeded, state) := (preseedExprTables #[(expression, [u, v]), (expression, [v, u])] env).run initial
  let (compiled, after) := (compileExpr expression env).run state
  return seeded.isOk && state.univs == #[.var 0, .var 1] &&
    compiled.toOption.map (·.1) == some (.sort 1) && after.univs == state.univs && after.univsFinal

private def collisionRejectsUnsupported : Bool := Id.run do
  let valid := Expr.mkSort Level.mkZero
  let invalid := Expr.mvar (Name.fromLeanName `bad) valid.getHash
  let (result, state) := raw (preseedExprTables #[(valid, []), (invalid, [])])
  return (match result with | .error (.unsupportedExpr "metavariable") => true | _ => false) &&
    state.univs.isEmpty && !state.univsFinal && state.p3Heads == retained

def controls : List (String × Bool) := Id.run do
  let key := univParamsKey []
  let mut shared := Expr.mkBVar 0
  for _ in [:64] do
    shared := Expr.mkLam Name.mkAnon shared shared .default
  let (sharedResult, sharedState) := raw (collectExprTables shared key (#[], #[], {}))
  let (sharedSeed, sharedSeedState) := raw (preseedExprTables #[(shared, [])])
  -- Left-associated applications force pending siblings. A recursive
  -- structural collector would consume native stack proportional to depth.
  let mut deep := Expr.mkBVar 0
  let argument := Expr.mkBVar 1
  for _ in [:65536] do deep := Expr.mkApp deep argument
  let (deepResult, deepState) := raw (collectExprTables deep key (#[], #[], {}))
  let roots := Array.replicate 65536 (Expr.mkSort Level.mkZero, [])
  let (wideResult, wideState) := raw (preseedExprTables roots)
  let u := Name.fromLeanName `u
  let v := Name.fromLeanName `v
  let level := Level.mkParam u
  let sort := Expr.mkSort level
  let (positions, positionalState) := raw (preseedExprTables #[(sort, [u, v]), (sort, [v, u])])
  let literal := Expr.mkLit (.natVal 37)
  let literalBytes := ByteArray.mk (Nat.toBytesLE 37)
  let literalAddress := Address.blake3 literalBytes
  let textBytes := "kept".toUTF8
  let textAddress := Address.blake3 textBytes
  let skippedAddress := Address.blake3 "after".toUTF8
  let invalid := Expr.mkMVar (Name.fromLeanName `bad)
  let broken := Expr.mkLetE Name.mkAnon literal
    (Expr.mkApp (Expr.mkLit (.strVal "kept")) invalid)
    (Expr.mkLit (.strVal "after")) false
  let (failure, failed) := raw (preseedExprTables #[(broken, [])])
  let seen : Std.HashMap _root_.Ix.Compile.ExactKey.PreseedKey Unit :=
    ({} : Std.HashMap _root_.Ix.Compile.ExactKey.PreseedKey Unit).insert ⟨invalid, [], key⟩ ()
  let (warm, warmState) := raw (collectExprTables invalid key (#[literalAddress], #[], seen))
  let badLevels := Expr.mkConst (Name.fromLeanName `Missing)
    #[Level.mkZero, Level.mkMvar (Name.fromLeanName `badLevel)]
  let (levelFailure, levelState) := raw (preseedExprTables #[(badLevels, [])])
  let primary := Address.blake3 "primary".toUTF8
  let metadataState : BlockState := { initial with
    refs := #[primary], refsIndex := ({} : Std.HashMap Address UInt64).insert primary 0,
    p3MetaMode := true }
  let (metadata, metadataAfter) := raw (preseedExprTables #[(literal, [])]) metadataState
  let largest := UInt64.size - 1
  let (zeroIndex, _) := raw (checkedTableIndex "control" 0)
  let (lastIndex, _) := raw (checkedTableIndex "control" largest)
  let (tooLarge, tooLargeState) := raw (checkedTableIndex "control" UInt64.size)
  let (largerStill, _) := raw (checkedTableIndex "control" (UInt64.size + 1))
  let (emptyCount, _) := raw (checkedTableCount "control" 0)
  let (largestCount, _) := raw (checkedTableCount "control" largest)
  let (overflowCount, overflowCountState) := raw (checkedTableCount "control" UInt64.size)
  let (beyondCount, _) := raw (checkedTableCount "control" (UInt64.size + 1))
  let goodMeta : BlockState := { metadataState with
    p3MetaRefs := #[literalAddress],
    p3MetaRefsIndex := ({} : Std.HashMap Address UInt64).insert literalAddress 0,
    univs := #[.zero], metaUnivs := #[.succ .zero],
    metaUnivsIndex := ({} : Std.HashMap Ixon.Univ UInt64).insert (.succ .zero) 0 }
  let badMeta := { goodMeta with
    p3MetaRefsIndex := goodMeta.p3MetaRefsIndex.insert literalAddress largest.toUInt64,
    metaUnivsIndex := goodMeta.metaUnivsIndex.insert (.succ .zero) largest.toUInt64 }
  let (goodRef, goodRefAfter) := raw (internRef literalAddress) goodMeta
  let (badRef, badRefAfter) := raw (internRef literalAddress) badMeta
  let (goodUniv, goodUnivAfter) := raw (internMetaUniv (.succ .zero)) goodMeta
  let (badUniv, badUnivAfter) := raw (internMetaUniv (.succ .zero)) badMeta
  return [
    ("shared DAG collector has no tree-size prepass", match sharedResult with
      | .ok (refs, univs, seen) => refs.isEmpty && univs.isEmpty && seen.size == 65
      | .error _ => false),
    ("shared DAG survives the public preseed entry", sharedSeed.isOk && sharedSeedState.univsFinal),
    ("deep pending siblings use the native worklist", match deepResult with
      | .ok (refs, univs, seen) => refs.isEmpty && univs.isEmpty && seen.size == 65538
      | .error _ => false),
    ("wide root arrays use the compiled folds", wideResult.isOk && wideState.univs == #[.zero] && wideState.univsFinal),
    ("seen keys retain universe parameter positions", positions.isOk && positionalState.univs == #[.var 0, .var 1] &&
      positionalState.univCache.get? ⟨level, [v, u]⟩ == some (.var 1)),
    ("preorder error preserves completed blob writes", (match failure with
      | .error (.unsupportedExpr "metavariable") => true | _ => false) &&
      failed.blockBlobs.get? literalAddress == some literalBytes && failed.blockBlobs.get? textAddress == some textBytes),
    ("preorder error leaves later syntax and tables untouched", !failed.blockBlobs.contains skippedAddress &&
      failed.refs.isEmpty && failed.univs.isEmpty && !failed.univsFinal),
    ("an exact warm seen-cache hit retains existing behavior", match warm with
      | .ok (refs, univs, afterSeen) => refs == #[literalAddress] && univs.isEmpty && afterSeen.size == 1
      | .error _ => false),
    ("ordinary distinct expressions preseed both universes", expressionCollision false),
    ("equal expression digests retain both universe dependencies", expressionCollision true),
    ("ordinary reordered contexts preseed both positions", contextCollision false),
    ("equal context digests retain both universe positions", contextCollision true),
    ("a digest collision cannot suppress an unsupported expression", collisionRejectsUnsupported),
    ("universe failure precedes missing reference lookup", (match levelFailure with
      | .error (.unsupportedExpr "level metavariable") => true | _ => false) &&
      levelState.univCache.get? ⟨Level.mkZero, []⟩ == some .zero),
    ("metadata-mode intern tables stay separate", metadata.isOk && metadataAfter.refs == #[primary] &&
      metadataAfter.p3MetaRefs == #[literalAddress] && metadataAfter.univsFinal),
    ("checked indices accept zero and the last wire slot",
      zeroIndex.toOption == some 0 && lastIndex.toOption == some largest.toUInt64),
    ("checked indices reject overflow without changing claims",
      resourceFailure tooLarge && resourceFailure largerStill && tooLargeState.p3Heads == retained),
    ("wire table counts accept empty and largest representable tables",
      emptyCount.toOption == some 0 && largestCount.toOption == some largest.toUInt64),
    ("a representable last slot cannot justify an overflowing table count",
      lastIndex.isOk && resourceFailure overflowCount && resourceFailure beyondCount &&
        overflowCountState.p3Heads == retained),
    ("virtual reference hit retains its intended slot",
      goodRef.toOption == some 1 && goodRefAfter.refs == #[primary] &&
        goodRefAfter.p3MetaRefs == #[literalAddress]),
    ("overflowing virtual reference cannot wrap to the primary slot",
      resourceFailure badRef && badRefAfter.refs == badMeta.refs &&
        badRefAfter.p3MetaRefs == badMeta.p3MetaRefs &&
        badRefAfter.p3MetaRefsIndex.get? literalAddress == some largest.toUInt64),
    ("virtual universe hit retains its intended slot",
      goodUniv.toOption == some 1 && goodUnivAfter.univs == #[.zero] &&
        goodUnivAfter.metaUnivs == #[.succ .zero]),
    ("overflowing virtual universe cannot wrap to the primary slot",
      resourceFailure badUniv && badUnivAfter.univs == badMeta.univs &&
        badUnivAfter.metaUnivs == badMeta.metaUnivs &&
        badUnivAfter.metaUnivsIndex.get? (.succ .zero) == some largest.toUInt64),
    ("all table paths preserve prior head claims",
      [sharedState, sharedSeedState, deepState, wideState, positionalState, failed, warmState, levelState, metadataAfter].all
        (·.p3Heads == retained))
  ]

def suite : List TestSeq := controls.map fun (label, ok) => test s!"table worklist: {label}" ok

end Tests.Ix.Compile.TableWorklist
