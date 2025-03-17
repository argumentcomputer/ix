import Lean
import Ix.Address
import Ix.CanonM

open Lean

def computeIxAddress (const : ConstantInfo) (constMap: ConstMap) : IO Address := do
  IO.ofExcept (<- Ix.CanonM.canonicalize constMap const)

/-- Computes the Ix address of an anonymous definition whose value is provided as input -/
elab "ix_adr" stx:term : term => do
  let value ← Elab.Term.elabTerm stx none >>= instantiateExprMVars
  Meta.check value
--  let type ← Meta.inferType value >>= instantiateExprMVars
  let type ← Meta.inferType value
  let const := .defnInfo {
    name        := .anonymous
    levelParams := []
    type        := type
    value       := value
    hints       := .opaque
    safety      := .safe
  }
  IO.println s!"{type}"
  let adr <- computeIxAddress const (← getEnv).constants
  return toExpr $ adr

def id' (A: Type) (x: A) := x

--#eval (ix_adr id')
