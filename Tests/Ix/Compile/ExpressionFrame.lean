import LSpec
import Ix.CompileM

namespace Tests.Ix.Compile.ExpressionFrame

open LSpec
open _root_.Ix (Name Expr)
open _root_.Ix.CompileM

private def context : CompileEnv × BlockEnv :=
  ({ (default : CompileEnv) with pass3 := true },
    { all := {}, current := Name.mkAnon, mutCtx := default, univCtx := [] })

private def retained : Array (Name × Name) :=
  #[(Name.fromLeanName `Retained.below, Name.fromLeanName `Retained)]

private def initial : BlockState := { p3Heads := retained }

private def raw (action : CompileM α) (state : BlockState := initial) :
    Except CompileError α × BlockState := (action context).run state

def controls : List (String × Bool) := Id.run do
  let f := Expr.mkBVar 0
  let a := Expr.mkBVar 1
  let b := Expr.mkBVar 2
  let inner := Expr.mkApp f a
  let outer := Expr.mkApp inner b
  let (compiled, after) := raw (compileExpr outer)
  let (innerResult, afterInner) := raw (compileExpr inner) after
  let (cached, afterCached) := raw (compileExpr outer) afterInner
  let seeded : BlockState := { initial with
    exprCache := ({} : Std.HashMap Expr (Ixon.Expr × UInt64)).insert inner (.var 99, 99) }
  let (seedResult, seedAfter) := raw (compileExpr outer) seeded
  let broken := Expr.mkApp inner (Expr.mkMVar (Name.fromLeanName `missing))
  let (failure, failed) := raw (compileExpr broken)
  -- A 64-level shared DAG has exponentially many tree occurrences. A
  -- runtime sizeOf walk would make this small regression infeasible.
  let mut shared := f
  for _ in [:64] do
    shared := Expr.mkLam Name.mkAnon shared shared .default
  let (sharedResult, sharedAfter) := raw (compileExpr shared)
  return [
    ("flattened application result and root", compiled.toOption == some (.app (.app (.var 0) (.var 1)) (.var 2), 4)),
    ("head argument application allocation order",
      after.arena.nodes == #[.leaf, .leaf, .app 0 1, .leaf, .app 2 3]),
    ("inner spine is not cached", !after.exprCache.contains inner),
    ("maximal inner occurrence allocates its own application", innerResult.toOption == some (.app (.var 0) (.var 1), 5)),
    ("maximal outer occurrence reuses its root", cached.isOk && cached.toOption == compiled.toOption && afterCached.arena.nodes.size == 6),
    ("an inner cache entry cannot substitute into the spine", seedResult.isOk && seedResult.toOption == compiled.toOption),
    ("the untouched inner entry remains available", seedAfter.exprCache.get? inner == some (.var 99, 99)),
    ("error retains completed child effects", (match failure with
        | .error (.unsupportedExpr "metavariable") => true | _ => false) &&
      failed.arena.nodes == #[.leaf, .leaf, .app 0 1] && failed.exprCache.contains f && failed.exprCache.contains a),
    ("failed whole expression is not cached", !failed.exprCache.contains broken),
    ("shared DAG has no runtime tree-size prepass", sharedResult.isOk && sharedAfter.arena.nodes.size == 65),
    ("successful compilation retains prior head claims", after.p3Heads == retained && seedAfter.p3Heads == retained),
    ("error compilation retains prior head claims", failed.p3Heads == retained)
  ]

def suite : List TestSeq := controls.map fun (label, ok) => test s!"expression frame: {label}" ok

end Tests.Ix.Compile.ExpressionFrame
