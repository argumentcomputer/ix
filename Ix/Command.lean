import Lean
import Ix.Address

open Lean Elab Command

def computeIxAddress (_constName : Name) (_constMap: ConstMap) : Address :=
  default

/-- Compute the Ix `Address` of a Lean constant and bind it to a name -/
elab "#ix" "hash" constName:ident "as" adrName:ident : command => do
  let adr := computeIxAddress constName.getId (← getEnv).constants
  let decl := Declaration.defnDecl {
    name        := adrName.getId
    levelParams := []
    type        := mkConst ``Address
    value       := toExpr adr
    hints       := ReducibilityHints.opaque
    safety      := DefinitionSafety.safe
  }
  liftCoreM $ addAndCompile decl
