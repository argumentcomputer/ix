import IxVM.Checked.Static

/-! # The checked IxVM source

`IxVM.Checked.source` is the object the refinement statements are about: the
program the backend headline's source semantics runs for the entry
`IxVM::verify_claim`, pinned as a Lean literal. It is what
`Aiur.Modules.prepare IxVM.program ["IxVM::verify_claim"]` computes (the
modules linked, renamed and elaborated), written out by
`lake exe ixvm/ixvm-checked` (`IxVM/IxVM/Checked/`): one definition per
function, the declarations, and the table generator's tables.

Nothing here runs the module frontend or the elaborator. The link to
`IxVM.program` is checked natively: the test suite `ixvm-checked-source`
prepares `IxVM.program` and checks that its source is this one, and
`lake exe ixvm/ixvm-checked --check` that the files are the rendering. -/

namespace IxVM.Checked

/-- The entry the checked source is prepared for. -/
def entry : String := "IxVM::verify_claim"

/-- **The checked IxVM source.** -/
def source : Aiur.Generic.Source F := ⟨program, coreTables, tablesChecked⟩

end IxVM.Checked
