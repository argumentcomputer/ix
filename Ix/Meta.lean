import Lean
import Ix.Address

open Lean

def computeIxAddress (_const : ConstantInfo) (_constMap: ConstMap) : Address :=
  default -- TODO

/-- Computes the Ix address of an anonymous definition whose value is provided as input -/
elab "ix_adr" stx:term : term => do
  let value ← Elab.Term.elabTerm stx none >>= instantiateExprMVars
  Meta.check value
  let type ← Meta.inferType value
  let const := .defnInfo {
    name        := .anonymous
    levelParams := []
    type        := type
    value       := value
    hints       := .opaque
    safety      := .safe
  }
  return toExpr $ computeIxAddress const (← getEnv).constants
