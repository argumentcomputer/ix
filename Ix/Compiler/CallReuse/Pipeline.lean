import Ix.Compiler.IxIR2.Pipeline
import Ix.Compiler.IxIR2.CallReuse

/-! Ordinary validated Ixon compilation with the versioned direct-call pass.
The selection retains either the checked rewrite or the checked baseline and
its rejection reason. No fixture-specific IR is supplied to this boundary. -/

namespace Ix.Compiler.CallReuse

open Ix.Compiler.Ixon (Address Constant)

structure Compilation (constants : List (Address × Constant)) (root : Address)
    (config : Pipeline.Config) (eraseFuel lowerFuel : Nat) where
  attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel
  selection : IxIR2.CallReuse.Selection IxIR2.Validate.defaultLimits
    attached.target.artifact.validationContext attached.target.artifact.program

def compileValidated (constants : List (Address × Constant)) (root : Address)
    (config : Pipeline.Config := {})
    (checkFuel : Nat := Ixon.UsageCheck.defaultFuel)
    (eraseFuel : Nat := Erase.defaultFuel) (validateFuel : Nat := Erase.defaultFuel)
    (lowerFuel : Nat := 10000) (maxDepth : Nat := 100000) :
    Except IxIR2.Pipeline.Error (Compilation constants root config eraseFuel lowerFuel) := do
  let attached ← IxIR2.Pipeline.compileValidated constants root config .shared
    checkFuel eraseFuel validateFuel lowerFuel maxDepth
  return {
    attached
    selection := IxIR2.CallReuse.selectChecked IxIR2.Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program
      ⟨attached.target.stats, attached.target.accepted⟩ }

end Ix.Compiler.CallReuse
