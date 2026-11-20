import IxAIRefine.Static

namespace IxAIStep.Fixed

/-- The program's entries. -/
def entries : List String := ["Fixed::step", "Fixed::train"]

/-- The checked source of `Fixed::step` and `Fixed::train`, assembled from the emitted named
functions and the static byte tables. `IxAIRefine.Check` checks that it is the source
`Modules.prepare` makes of `IxAIAiur.source` for those entries. -/
def source : Aiur.Generic.Source F := ⟨program, coreTables, tablesChecked⟩

end IxAIStep.Fixed
