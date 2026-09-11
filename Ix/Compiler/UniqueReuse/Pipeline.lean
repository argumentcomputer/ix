import Ix.Compiler.IxIR2.UniqueLower

/-! Opt-in source compilation for the checked unique reversal fragment.
Optional target failure retains the consuming IxIR₁ artifact; static reuse
failure retains its validated IxIR₂ baseline. -/

namespace Ix.Compiler.UniqueReuse

open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.IxIR0.UniqueReverse (Plan)

structure CompiledTarget (plan : Plan) (limits : IxIR2.Validate.Limits) where
  translation : IxIR2.UniqueLower.Translation (IxIR2.UniqueLower.input plan) plan limits
  selection : IxIR2.UniqueLower.Selection plan limits

inductive Backend (plan : Plan) (limits : IxIR2.Validate.Limits) where
  | ownedOnly (reason : String)
  | translated (target : CompiledTarget plan limits)

def buildTarget (plan : Plan) (limits : IxIR2.Validate.Limits)
    (policy : IxIR2.UniqueLower.ReusePolicy) : Backend plan limits :=
  match IxIR2.UniqueLower.translate plan limits with
  | .error message => .ownedOnly message
  | .ok translation => .translated
      { translation, selection := IxIR2.UniqueLower.select plan limits translation.checked policy }

structure Compilation (constants : List (Address × Constant)) (entry : Pipeline.ClosedEntry)
    (config : Pipeline.Config) (checkFuel eraseFuel : Nat) (limits : IxIR2.Validate.Limits) where
  source : Pipeline.CertifiedErasure constants entry config .saturatedRecursorV1 .unique checkFuel eraseFuel
  lowered : Lowered source
  backend : Backend lowered.plan limits

def Compilation.plan {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}
    (compilation : Compilation constants entry config checkFuel eraseFuel limits) : Plan := compilation.lowered.plan

inductive Error where
  | source (error : Pipeline.Error)
  | ownership (detail : String)
  deriving Repr

def compile (constants : List (Address × Constant)) (entry : Pipeline.ClosedEntry)
    (config : Pipeline.Config := {}) (checkFuel : Nat := 1000) (eraseFuel : Nat := 1000)
    (validateFuel : Nat := 1000) (limits : IxIR2.Validate.Limits := IxIR2.Validate.defaultLimits)
    (policy : IxIR2.UniqueLower.ReusePolicy := {}) :
    Except Error (Compilation constants entry config checkFuel eraseFuel limits) := do
  let source ← (Pipeline.certifyErasure constants entry config .saturatedRecursorV1 .unique
    checkFuel eraseFuel validateFuel).mapError .source
  let lowered ← (lower source).mapError .ownership
  return { source, lowered, backend := buildTarget lowered.plan limits policy }

end Ix.Compiler.UniqueReuse
