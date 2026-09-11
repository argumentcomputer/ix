import Ix.Compiler.UniqueReuse.RuntimeSource
import Ix.Compiler.UniqueReuse.Provenance

/-! Compilation and checked selection of the parameterized reversal entry.
IxIR₂ keeps its nullary module main; clients enter the independently checked
exported declaration with an owned runtime argument. -/

namespace Ix.Compiler.UniqueReuse.Runtime

open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.IxIR0.UniqueReverse (Schema)

def entryCode (schema : Schema) : IxIR1.Code :=
  .letOp (.alloc .unique (nilId schema) #[])
    (.letOp (.call (functionAddress schema) #[.var 0, .var 1]) (.ret (.var 0)))

def entryFunction (schema : Schema) : IxIR1.FnDef :=
  { arity := 1, result := .unique, papSafe := false, body := entryCode schema }

def entryAddress (schema : Schema) : Address := (IxIR1.Decl.fn (entryFunction schema)).address

def artifacts (schema : Schema) : List IxIR1.ReaddressAll.Artifact :=
  .ordinary (entryAddress schema) (.fn (entryFunction schema)) :: UniqueReuse.artifacts schema

def targetEntry (schema : Schema) : IxIR2.Function :=
  { signature := { params := #[{ world := .unique, passing := .owned }], result := .unique, papSafe := false }
    blocks := #[
      { valueParams := #[.owned .unique], creditParams := #[]
        instructions := #[.alloc .unique (nilId schema) #[]]
        terminator := .tailCall (functionAddress schema) #[.reg 1, .reg 0] }] }

def program (schema : Schema) (reuse : Bool) : IxIR2.Program :=
  { declarations := [(entryAddress schema, .fn (targetEntry schema)),
      (functionAddress schema, .fn (IxIR2.UniqueLower.function schema reuse))]
    main := IxIR2.UniqueLower.mainFunction { schema, values := [] } }

structure Selection (schema : Schema) (limits : IxIR2.Validate.Limits) where
  reuse : Bool
  reason : Option String
  distinct : entryAddress schema ≠ functionAddress schema
  checked : IxIR2.Validate.Checked limits (IxIR2.UniqueLower.context schema) (program schema reuse)
  placement : reuse = true → ∃ placement : IxIR2.Reuse.Placement (IxIR2.UniqueLower.consBlock schema false),
    placement.value = 1 ∧ placement.position = 0

def select (schema : Schema) (limits : IxIR2.Validate.Limits) (policy : IxIR2.UniqueLower.ReusePolicy) :
    Except String (Selection schema limits) := do
  let distinct : PLift (entryAddress schema ≠ functionAddress schema) ←
    if hd : entryAddress schema ≠ functionAddress schema then pure ⟨hd⟩
    else throw "runtime export collides with the worker identity"
  let baseline ← match hc : IxIR2.Validate.validateWith limits (IxIR2.UniqueLower.context schema) (program schema false) with
    | .error error => throw s!"runtime consuming target rejected: {repr error}"
    | .ok stats => pure (⟨stats, hc⟩ : IxIR2.Validate.Checked limits (IxIR2.UniqueLower.context schema) (program schema false))
  let fallback := fun reason =>
    ({ reuse := false, reason := some reason, distinct := distinct.down, checked := baseline, placement := by simp } : Selection schema limits)
  if !policy.enabled then return fallback "disabled"
  if policy.maxRewrites == 0 then return fallback "rewrite budget"
  match hp : IxIR2.Reuse.inferPlacementWith limits (IxIR2.UniqueLower.consBlock schema false) 1 0 with
  | .error error => return fallback s!"liveness: {repr error}"
  | .ok none => return fallback "unique input has a later use"
  | .ok (some placement) =>
    let bounds := IxIR2.Reuse.inferPlacementWith_sound hp
    match hc : IxIR2.Validate.validateWith limits (IxIR2.UniqueLower.context schema) (program schema true) with
    | .error error => return fallback s!"reuse validation: {repr error}"
    | .ok stats =>
      return {
        reuse := true, reason := none, distinct := distinct.down
        checked := ⟨stats, hc⟩, placement := fun _ => ⟨placement, bounds⟩ }

structure Compilation (constants : List (Address × Constant)) (entry : Pipeline.ClosedEntry)
    (config : Pipeline.Config) (checkFuel eraseFuel : Nat) (limits : IxIR2.Validate.Limits) where
  erased : Pipeline.CertifiedErasure constants entry config .saturatedRecursorV1 .shared checkFuel eraseFuel
  source : CheckedSource erased
  selection : Selection source.shape.schema limits

def Compilation.schema {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}
    (compilation : Compilation constants entry config checkFuel eraseFuel limits) : Schema :=
  compilation.source.shape.schema

def compile (constants : List (Address × Constant)) (entry : Pipeline.ClosedEntry)
    (config : Pipeline.Config := {}) (checkFuel eraseFuel validateFuel : Nat := 1000)
    (limits : IxIR2.Validate.Limits := IxIR2.Validate.defaultLimits)
    (policy : IxIR2.UniqueLower.ReusePolicy := {}) :
    Except String (Compilation constants entry config checkFuel eraseFuel limits) := do
  let erased ← (Pipeline.certifyErasure constants entry config .saturatedRecursorV1 .shared
    checkFuel eraseFuel validateFuel).mapError reprStr
  let source ← checkSource erased
  let selection ← select source.shape.schema limits policy
  return { erased, source, selection }

end Ix.Compiler.UniqueReuse.Runtime
