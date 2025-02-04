import Lean
import Ix.Basic

def hashLeanExpr (_expr : Lean.Expr) (_constMap: Lean.ConstMap) : Digest :=
  default -- TODO

open Lean Elab Term Command Meta
elab "#ix" "hash" "⟦" stx:term "⟧" "as" name:ident : command => do
  let constMap := (← getEnv).constants
  let expr ← liftTermElabM $ elabTerm stx none >>= instantiateExprMVars
  let digest := hashLeanExpr expr constMap
  let decl := Declaration.defnDecl {
    name        := name.getId
    levelParams := []
    type        := mkConst ``ByteArray
    value       := mkApp (mkConst ``ByteArray.mk) (toExpr digest.data)
    hints       := ReducibilityHints.opaque
    safety      := DefinitionSafety.safe
  }
  liftCoreM $ addAndCompile decl
