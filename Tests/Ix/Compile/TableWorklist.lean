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
  let seen : Std.HashMap (Address × Address) Unit :=
    ({} : Std.HashMap (Address × Address) Unit).insert (invalid.getHash, key) ()
  let (warm, warmState) := raw (collectExprTables invalid key (#[literalAddress], #[], seen))
  let badLevels := Expr.mkConst (Name.fromLeanName `Missing)
    #[Level.mkZero, Level.mkMvar (Name.fromLeanName `badLevel)]
  let (levelFailure, levelState) := raw (preseedExprTables #[(badLevels, [])])
  let primary := Address.blake3 "primary".toUTF8
  let metadataState : BlockState := { initial with
    refs := #[primary], refsIndex := ({} : Std.HashMap Address UInt64).insert primary 0,
    p3MetaMode := true }
  let (metadata, metadataAfter) := raw (preseedExprTables #[(literal, [])]) metadataState
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
      positionalState.univCache.get? level == some (.var 1)),
    ("preorder error preserves completed blob writes", (match failure with
      | .error (.unsupportedExpr "metavariable") => true | _ => false) &&
      failed.blockBlobs.get? literalAddress == some literalBytes && failed.blockBlobs.get? textAddress == some textBytes),
    ("preorder error leaves later syntax and tables untouched", !failed.blockBlobs.contains skippedAddress &&
      failed.refs.isEmpty && failed.univs.isEmpty && !failed.univsFinal),
    ("an arbitrary seen-cache hit retains existing behavior", match warm with
      | .ok (refs, univs, afterSeen) => refs == #[literalAddress] && univs.isEmpty && afterSeen.size == 1
      | .error _ => false),
    ("universe failure precedes missing reference lookup", (match levelFailure with
      | .error (.unsupportedExpr "level metavariable") => true | _ => false) &&
      levelState.univCache.get? Level.mkZero == some .zero),
    ("metadata-mode intern tables stay separate", metadata.isOk && metadataAfter.refs == #[primary] &&
      metadataAfter.p3MetaRefs == #[literalAddress] && metadataAfter.univsFinal),
    ("all table paths preserve prior head claims",
      [sharedState, sharedSeedState, deepState, wideState, positionalState, failed, warmState, levelState, metadataAfter].all
        (·.p3Heads == retained))
  ]

def suite : List TestSeq := controls.map fun (label, ok) => test s!"table worklist: {label}" ok

end Tests.Ix.Compile.TableWorklist
