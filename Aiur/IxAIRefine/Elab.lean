import Aiur.Modules.Emit
import IxAIRefine.Tables

/-! The `Fixed` program elaborator. The program `IxAIAiur.source` (the `UInt8` library and
the `Fixed` module) is resolved for the entries `Fixed::step` and `Fixed::train` as
`Modules.prepare` resolves them, then emitted once as public definitions in the namespace `IxAIStep.Fixed`: one constant per
function, and `functions`, `enums`, `structs`, `maps`, `aliases`, `consts`, `program`. -/

namespace IxAIStep.Fixed.Elab
open Lean Elab Command
open Aiur

abbrev F := IxAIAiur.F

/-- The program's entries. -/
def entries : List String := ["Fixed::step", "Fixed::train"]

/-- The compiler input, as `IxAIAiur.run` prepares it. -/
def moduleProgram : Except String (Modules.Program F) := do
  Modules.checkTemplates IxAIAiur.source
  return IxAIAiur.source.toField F

/-- A function's Lean name: its qualified Aiur name under `IxAIStep.Fixed`
(`Fixed::shr8` is `IxAIStep.Fixed.Fixed.shr8`, `UInt8::to_field` is
`IxAIStep.Fixed.UInt8.to_field`). -/
def functionName (symbol : String) : Name :=
  (symbol.splitOn "::").foldl Name.str `IxAIStep.Fixed

elab "#ixai_fixed_program" : command => Modules.Frontend.uncounted do
  let input ← ofExcept moduleProgram
  let (world, _) ← ofExcept (Modules.collect input entries)
  let assembly ← ofExcept (Modules.assemble input world)
  -- Functions are resolved against the tables' types only; `Static.lean` proves the
  -- real rows valid from their generator.
  let headers := { assembly.program with
    tables := assembly.program.tables.map fun t => { t with rows := [] } }
  let source ← ofExcept (Generic.prepare headers)
  ofExcept (entries.forM source.checkEntry)
  let quoteField ← liftTermElabM (Modules.numeralQuoter (mkConst ``IxAIAiur.F) (fun x : F => x.val))
  letI := quoteField
  Modules.emitProgram (mkConst ``IxAIAiur.F) `IxAIStep.Fixed functionName source.program
    (mkConst `IxAIStep.Fixed.genericTables)

end IxAIStep.Fixed.Elab
