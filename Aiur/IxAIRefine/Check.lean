import IxAIRefine.Source
import IxAIRefine.Elab

/-! Parity of `IxAIStep.Fixed.source` with full module preparation: `Modules.prepare` of
`IxAIAiur.source` for the entries `Fixed::step` and `Fixed::train` yields exactly the emitted program and the
static tables `coreTables`, so `source.world` is the prepared program's world. Checked when
this module is elaborated. -/

namespace IxAIStep.Fixed.Check

/-- Whether the native preparation's source is `IxAIStep.Fixed.source`, part by part. -/
def parity : Except String (Bool × Bool × Bool) := do
  let input ← Elab.moduleProgram
  let prepared ← Aiur.Modules.prepare input entries
  let src := prepared.environment.source
  return (src.program == program, src.tables == coreTables, prepared.entries == entries)

#eval show IO Unit from do
  let (prog, tables, entries) ← IO.ofExcept parity
  unless prog && tables && entries do
    throw (IO.userError s!"Fixed source parity: program {prog}, tables {tables}, entries {entries}")
  IO.println "Fixed source parity: program, static tables and entries match Modules.prepare"

end IxAIStep.Fixed.Check
