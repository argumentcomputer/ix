module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes

public section

namespace IxVM

/-! ## Kernel2: stub Levels

Trivial no-op version of `level_equal` used by
`Kernel2.Check.check_const` (Thm arm). -/

def levels := ⟦
  fn level_equal(a: KLevel, b: KLevel) -> G {
    1
  }
⟧

end IxVM

end
