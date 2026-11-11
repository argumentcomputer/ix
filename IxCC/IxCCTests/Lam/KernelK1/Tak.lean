import IxCCTests.Src.Artifacts.Tak
import IxCCTests.Lam.KernelK1.Front

/-! The `tak` bench-k1 artifact through the front end in the kernel. -/

namespace IxCCTests.Lam.KernelK1.Tak

open IxCCTests.Src.Artifacts.Tak

set_option maxRecDepth 1000000

/-- `tak`'s entry (`Ids.entry`) erases to `Ids.globals` globals rooted at `const Ids.entry`. -/
example : facts program ann Ids.globals Ids.entry = true := by decide +kernel

end IxCCTests.Lam.KernelK1.Tak
