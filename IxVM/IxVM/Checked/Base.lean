import Aiur.Generic.AST
import Aiur.Library.U32.Goldilocks

/-! The field of the checked IxVM source (`IxVM.Checked`): Goldilocks, as
`IxVM.F`. The checked source's files import only this, the Formal Aiur AST and
the table generator, not the module frontend. -/

namespace IxVM.Checked

abbrev F := Aiur.Library.U32.Goldilocks.F

end IxVM.Checked
