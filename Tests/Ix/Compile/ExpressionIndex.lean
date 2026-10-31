import LSpec
import Ix.CompileM

/-! Finite controls for expression wire indices (`Ix.CompileM.checkedTableIndex`).
Oversized source indices and mutual contexts are supplied directly; no huge
term or table is allocated. The expression compiler (`compileExpr`) and the
constant-head entry (`compileConstExprRaw`) are checked, including retries
after refusals and a cache hit at the representable bound. -/

namespace Tests.Ix.Compile.ExpressionIndex

open LSpec
open _root_.Ix (Name Expr)
open _root_.Ix.CompileM

private def structName := Name.fromLeanName `IndexBoundary.Structure
private def recursiveName := Name.fromLeanName `IndexBoundary.recursive
private def env : CompileEnv := { (default : CompileEnv) with
  nameToAddr := ({} : Std.HashMap _root_.Ix.Compile.ExactKey.ExactName Address).insert structName default }
private def block (index : Nat := 0) : BlockEnv := {
  all := {}, current := Name.mkAnon,
  mutCtx := (default : _root_.Ix.MutCtx).insert recursiveName index, univCtx := [] }

private def raw (action : CompileM α) (index : Nat := 0) (state : BlockState := {}) :
    Except CompileError α × BlockState := (action (env, block index)).run state

private def overflow (result : Except CompileError α) : Bool := match result with
  | .error (.resourceLimit _) => true
  | _ => false

def controls : List (String × Bool) := Id.run do
  let last := UInt64.size - 1
  let big := Expr.mkBVar UInt64.size
  let bigger := Expr.mkBVar (UInt64.size + 7)
  let edge := Expr.mkBVar last
  let (bad, badAfter) := raw (compileExpr big)
  let (badRetry, retryAfter) := raw (compileExpr big) 0 badAfter
  let (biggerResult, _) := raw (compileExpr bigger)
  let (edgeResult, edgeAfter) := raw (compileExpr edge)
  let (edgeCached, _) := raw (compileExpr edge) 0 edgeAfter
  let (zeroResult, _) := raw (compileExpr (Expr.mkBVar 0))
  let projection := Expr.mkProj structName UInt64.size (Expr.mkBVar 0)
  let (projResult, projAfter) := raw (compileExpr projection)
  let (projRetry, projRetryAfter) := raw (compileExpr projection) 0 projAfter
  let edgeProjection := Expr.mkProj structName last (Expr.mkBVar 0)
  let (edgeProj, _) := raw (compileExpr edgeProjection)
  let recursive := Expr.mkConst recursiveName #[]
  let (recResult, recAfter) := raw (compileExpr recursive) UInt64.size
  let (recRetry, recRetryAfter) := raw (compileExpr recursive) UInt64.size recAfter
  let (rawRec, rawRecAfter) := raw (compileConstExprRaw recursiveName #[]) UInt64.size
  let (edgeRec, _) := raw (compileExpr recursive) last
  let first := Expr.mkBVar 0
  let application := Expr.mkApp first big
  let (appResult, appAfter) := raw (compileExpr application)
  return [
    ("first oversized bound variable is refused", overflow bad),
    ("larger bound variable does not alias its residue", overflow biggerResult),
    ("retry refuses the same bound variable", overflow badRetry),
    ("bound-variable refusal precedes allocation", badAfter.arena.nodes.isEmpty &&
      retryAfter.arena.nodes.isEmpty),
    ("refused bound variable is not cached", badAfter.exprCache.isEmpty &&
      retryAfter.exprCache.isEmpty),
    ("last representable bound variable is exact",
      edgeResult.toOption == some (.var last.toUInt64, 0) &&
        edgeCached.toOption == some (.var last.toUInt64, 0)),
    ("bound variable zero is unchanged", zeroResult.toOption == some (.var 0, 0)),
    ("oversized projection field is refused on both attempts",
      overflow projResult && overflow projRetry),
    ("projection refusal precedes name reference and child writes",
      projAfter.blockNames.isEmpty && projAfter.refs.isEmpty &&
        projAfter.arena.nodes.isEmpty && projAfter.exprCache.isEmpty &&
        projRetryAfter.blockNames.isEmpty && projRetryAfter.arena.nodes.isEmpty),
    ("last representable projection field is exact",
      edgeProj.toOption == some (.prj 0 last.toUInt64 (.var 0), 1)),
    ("oversized mutual reference is refused on both attempts",
      overflow recResult && overflow recRetry),
    ("raw constant entry also refuses mutual overflow", overflow rawRec),
    ("mutual refusal allocates no expression arena node", recAfter.arena.nodes.isEmpty &&
      recRetryAfter.arena.nodes.isEmpty && rawRecAfter.arena.nodes.isEmpty),
    ("mutual refusal does not cache the source expression",
      recAfter.exprCache.isEmpty && recRetryAfter.exprCache.isEmpty),
    ("last representable mutual slot is exact",
      edgeRec.toOption == some (.recur last.toUInt64 #[], 0)),
    ("parent propagates overflow while retaining completed children", overflow appResult &&
      appAfter.arena.nodes == #[.leaf] && appAfter.exprCache.contains first &&
      !appAfter.exprCache.contains big && !appAfter.exprCache.contains application)]

def suite : List TestSeq := controls.map fun (label, ok) => test s!"expression index: {label}" ok

end Tests.Ix.Compile.ExpressionIndex
