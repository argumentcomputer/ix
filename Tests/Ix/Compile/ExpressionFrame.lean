import LSpec
import Ix.CompileM

/-! Controls for the expression compiler's frame (`Ix.CompileM.compileExpr`):
App spines are flattened, partial
spines are allocated but never cached, cache hits reuse roots, failures keep
their completed children's effects, and a DAG-shared term compiles without a
walk of its exponentially larger tree. -/

namespace Tests.Ix.Compile.ExpressionFrame

open LSpec
open _root_.Ix (Name Expr)
open _root_.Ix.CompileM

private def context : CompileEnv × BlockEnv :=
  ((default : CompileEnv),
    { all := {}, current := Name.mkAnon, mutCtx := default, univCtx := [] })

private def raw (action : CompileM α) (state : BlockState := {}) :
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
  let seeded : BlockState := {
    exprCache := ({} : Std.HashMap _root_.Ix.Compile.ExactKey.ExprKey (Ixon.Expr × UInt64)).insert inner (.var 99, 99) }
  let (seedResult, seedAfter) := raw (compileExpr outer) seeded
  let broken := Expr.mkApp inner (Expr.mkMVar (Name.fromLeanName `missing))
  let (failure, failed) := raw (compileExpr broken)
  -- A 64-level shared DAG has exponentially many tree occurrences. A
  -- runtime walk of the tree would make this small regression infeasible.
  let mut shared := f
  for _ in [:64] do
    shared := Expr.mkLam Name.mkAnon shared shared .default
  let (sharedResult, sharedAfter) := raw (compileExpr shared)
  -- Semantic-contract wrappers are cached under their exact source key.
  let contract : _root_.Ix.SemanticContract.Contract := {
    kind := .lam, binder := ⟨.linear, .shared⟩ }
  let contractData := #[
    (Name.fromLeanName `ix.contract, _root_.Ix.DataValue.ofNat 3),
    (Name.fromLeanName `ix.contract.kind, _root_.Ix.DataValue.ofNat contract.kindCode),
    (Name.fromLeanName `ix.contract.code, _root_.Ix.DataValue.ofNat contract.code)]
  let binder := Expr.mkLam Name.mkAnon (Expr.mkSort _root_.Ix.Level.mkZero) f .default
  let annotated := Expr.mkMData contractData binder
  let (annotation, annotationAfter) := raw (compileExpr annotated)
  let (annotationAgain, annotationAgainAfter) := raw (compileExpr annotated) annotationAfter
  -- Supplied raw keys deliberately share a digest. They exercise the
  -- lookup boundary without claiming a cryptographic collision.
  let colliding : Expr := .bvar 1 f.getHash
  let collidingBad : Expr := .mvar (Name.fromLeanName `missing) f.getHash
  let (_, firstAfter) := raw (compileExpr f)
  let (collision, collisionAfter) := raw (compileExpr colliding) firstAfter
  let (originalAgain, originalAfter) := raw (compileExpr f) collisionAfter
  let (collisionError, collisionErrorAfter) := raw (compileExpr collidingBad) firstAfter
  return [
    ("flattened application result and root",
      compiled.toOption == some (.app (.app (.var 0) (.var 1)) (.var 2), 4)),
    ("head argument application allocation order",
      after.arena.nodes == #[.leaf, .leaf, .app 0 1, .leaf, .app 2 3]),
    ("inner spine is not cached", !after.exprCache.contains inner),
    ("maximal inner occurrence allocates its own application",
      innerResult.toOption == some (.app (.var 0) (.var 1), 5)),
    ("maximal outer occurrence reuses its root",
      cached.isOk && cached.toOption == compiled.toOption && afterCached.arena.nodes.size == 6),
    ("an inner cache entry cannot substitute into the spine",
      seedResult.isOk && seedResult.toOption == compiled.toOption),
    ("the untouched inner entry remains available",
      seedAfter.exprCache.get? inner == some (.var 99, 99)),
    ("error retains completed child effects", (match failure with
        | .error (.unsupportedExpr "metavariable") => true | _ => false) &&
      failed.arena.nodes == #[.leaf, .leaf, .app 0 1] && failed.exprCache.contains f &&
      failed.exprCache.contains a),
    ("failed whole expression is not cached", !failed.exprCache.contains broken),
    ("shared DAG has no runtime tree-size prepass",
      sharedResult.isOk && sharedAfter.arena.nodes.size == 65),
    ("semantic contract lowers the anonymous binder", match annotation with
      | .ok (.lam actual (.sort 0) (.var 0), _) => actual == contract.binder
      | _ => false),
    ("semantic contract wrapper is cached after success",
      annotation.isOk && annotationAfter.exprCache.get? annotated == annotation.toOption),
    ("repeated semantic contract reuses its result and arena",
      annotationAgain.toOption == annotation.toOption &&
        annotationAgainAfter.arena.nodes == annotationAfter.arena.nodes),
    ("different indices sharing a stored hash compile independently",
      collision.toOption == some (.var 1, 1)),
    ("colliding keys retain both cache entries",
      collisionAfter.exprCache.get? f == some (.var 0, 0) &&
      collisionAfter.exprCache.get? colliding == some (.var 1, 1) &&
      collisionAfter.exprCache.size == 2),
    ("colliding insertion preserves the original cached root",
      originalAgain.toOption == some (.var 0, 0) && originalAfter.arena.nodes.size == 2),
    ("a colliding unsupported expression still fails", (match collisionError with
      | .error (.unsupportedExpr "metavariable") => true | _ => false) &&
      collisionErrorAfter.arena.nodes == firstAfter.arena.nodes)
  ]

def suite : List TestSeq := controls.map fun (label, ok) =>
  test s!"expression frame: {label}" ok

end Tests.Ix.Compile.ExpressionFrame
