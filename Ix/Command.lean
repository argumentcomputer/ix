import Lean
import Ix.Address

def computeIxAddress (_expr : Lean.Expr) (_constMap: Lean.ConstMap) : Address :=
  default -- TODO

open Lean Elab Term Command Meta

/-- Compute the Ix `Address` of an expression and bind it to a name -/
elab "#ix" "hash" stx:term "as" name:ident : command => do
  let constMap := (← getEnv).constants
  let expr ← liftTermElabM $ elabTerm stx none >>= instantiateExprMVars
  let adr := computeIxAddress expr constMap
  let decl := Declaration.defnDecl {
    name        := name.getId
    levelParams := []
    type        := mkConst ``Address
    value       := toExpr adr
    hints       := ReducibilityHints.opaque
    safety      := DefinitionSafety.safe
  }
  liftCoreM $ addAndCompile decl
