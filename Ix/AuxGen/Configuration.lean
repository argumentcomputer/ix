module
public import Ix.AuxGen.Oracle
public import Ix.CompileM

/-! Shared validation for checked generation and measurement. Configuration
failures are ordinary compiler errors, not IxC query refusals. Callers
validate before callbacks, measurement or query-refusal handling. -/

public section
namespace Ix.AuxGen.Configuration

/-- Valid execution intent, selected only after all option checks pass. -/
inductive Intent where
  | compile
  | measure
  deriving BEq, Repr

/-- Execution flags only; asks, trace, support and other options are unchanged
by validation. No default silently converts a historical request. -/
structure Request where
  mode : IxcMode
  recursors : Bool
  measureOnly : Bool
  deriving Repr

/-- Keep invalid historical enum inputs expressible for explicit rejection.
These errors carry no scope/question/reason packet and no retry authority. -/
inductive Error where
  | unsupportedMode (mode : IxcMode)
  | recursorsDisabled
  | nestedRetry
  deriving BEq, Repr

def Error.render : Error → String
  | .unsupportedMode mode => s!"AuxGen (configuration): retired mode '{mode}' is unsupported"
  | .recursorsDisabled => "AuxGen (configuration): recursors must be enabled (rec=off is retired)"
  | .nestedRetry => "AuxGen (configuration): nested retry is unsupported"

instance : ToString Error := ⟨Error.render⟩

/-- A pure ordinary-error conversion. In particular, this does not call
refuseIxc, modify BlockReport.refusal or classify a query failure. -/
def Error.toCompileError (e : Error) : CompileM.CompileError :=
  .unsupportedExpr e.render

private def settings (mode : IxcMode) (recursors : Bool) : Except Error Unit := do
  unless mode == .failClosed do throw (.unsupportedMode mode)
  unless recursors do throw .recursorsDisabled

/-- Error precedence is mode, then recursors. measureOnly never bypasses
either check; a valid measurement remains distinct from compilation. -/
def validateRequest (request : Request) : Except Error Intent := do
  settings request.mode request.recursors
  return if request.measureOnly then .measure else .compile

/-- Inspect only capability flags, without asking status or invoking an
operation. Nested retry is checked after mode and recursors. Existing driver
retry-candidate guards retain their own established messages when wired. -/
def validateCapability (oracle : AuxOracle) : Except Error Unit := do
  settings oracle.mode oracle.recursors
  if oracle.retry.isSome then throw .nestedRetry

end Ix.AuxGen.Configuration
